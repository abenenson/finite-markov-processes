#!/usr/bin/env python3
"""Rebuild authored modules, re-elaborate full lint, and audit named transitive axioms."""
import argparse
import hashlib
import json
import re
import subprocess
import sys
import os
from datetime import datetime, timezone
from pathlib import Path

if not __debug__:
    raise SystemExit('Verification requires enabled Python assertions; omit -O/PYTHONOPTIMIZE.')


def uncomment(source):
    """Erase nested Lean comments and strings while preserving command line positions."""
    result, index, depth, quoted = [], 0, 0, False
    while index < len(source):
        pair = source[index:index + 2]
        char = source[index]
        if depth:
            if pair == '/-':
                depth += 1
                result.extend('  ')
                index += 2
            elif pair == '-/':
                depth -= 1
                result.extend('  ')
                index += 2
            else:
                result.append('\n' if char == '\n' else ' ')
                index += 1
        elif quoted:
            if char == '\\':
                result.extend('  ')
                index += 2
            else:
                quoted = char != '"'
                result.append('\n' if char == '\n' else ' ')
                index += 1
        elif pair == '/-':
            depth = 1
            result.extend('  ')
            index += 2
        elif pair == '--':
            end = source.find('\n', index)
            end = len(source) if end < 0 else end
            result.extend(' ' * (end - index))
            index = end
        elif char == '"':
            quoted = True
            result.append(' ')
            index += 1
        else:
            result.append(char)
            index += 1
    assert not depth and not quoted, 'Unterminated comment or string'
    return ''.join(result)


def declarations(source):
    """Enumerate explicit public names; anonymous and generated declarations are separate."""
    stack, names = [], []
    for line in uncomment(source).splitlines():
        if line != line.lstrip():
            continue
        line = re.sub(r'^@\[[^\]]*\]\s*', '', line)
        match = re.match(r"namespace\s+([\w.']+)", line)
        if match:
            stack.append(('namespace', match[1]))
            continue
        if re.match(r'(?:noncomputable\s+)?section\b', line):
            stack.append(('section', ''))
            continue
        if re.match(r'end(?:\s|$)', line):
            assert stack, line
            stack.pop()
            continue
        match = re.match(
            r'((?:(?:private|protected|noncomputable|unsafe)\s+)*)'
            r"(?:theorem|lemma|def|abbrev|structure|class|instance)\s+([\w.']+)", line)
        if match and 'private' not in match[1].split():
            prefix = [name for kind, name in stack if kind == 'namespace']
            names.append('.'.join(prefix + [match[2]]))
    assert not stack, stack
    return names



def check_diagnostics(output, *, json_mode=False):
    """Fail closed on native/JSON diagnostics, including erroneous zero-exit output."""
    def check_text(text):
        assert 'PANIC' not in text and not re.search(r'(?im)\bpanic:', text), 'Native panic'
        assert not re.search(r'(^|: )(?:warning|error):', text, re.M), text

    check_text(output)
    for raw in output.splitlines():
        line = re.sub(r'\x1b\[[0-?]*[ -/]*[@-~]', '', raw).strip()
        if not line:
            continue
        check_text(line)
        if not json_mode and not line.startswith('{'):
            continue
        try:
            message = json.loads(line)
        except json.JSONDecodeError as error:
            raise AssertionError('Malformed diagnostic JSON: ' + line) from error
        assert isinstance(message, dict), 'Unknown diagnostic JSON'
        assert message.get('severity') in {'information', 'warning', 'error'}, message
        assert isinstance(message.get('data'), str), message
        assert message['severity'] == 'information', message
        check_text(message['data'])


def imported_modules(source):
    """Read every ordinary import; unsupported header syntax fails closed."""
    tokens = re.findall(r"[A-Za-z_][\w.']*|[^\s]", uncomment(source))
    boundary = {'import', 'prelude', 'module', 'public', 'private', 'meta', 'open',
                'namespace', 'section', 'noncomputable', 'universe', 'universes',
                'variable', 'variables', 'export', 'attribute', 'set_option',
                'theorem', 'lemma', 'def', 'abbrev', 'instance', 'structure', 'class',
                'end', 'example', 'axiom', 'constant', 'opaque', 'inductive',
                'syntax', 'macro', 'elab', 'initialize', '#', '@'}
    modules = []
    for index, token in enumerate(tokens):
        if token != 'import':
            continue
        index += 1
        if index < len(tokens) and tokens[index] == 'all':
            index += 1
        start = len(modules)
        while index < len(tokens) and tokens[index] not in boundary:
            name = tokens[index]
            assert re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*",
                                name), 'Unsupported import header: ' + name
            modules.append(name)
            index += 1
        assert len(modules) > start, 'Empty or unsupported import header'
    return modules



def lint_source(source):
    """Keep optional module/prelude commands before imports, preserving comments and strings."""
    linter = 'import Mathlib.Tactic.Linter.Lint\n'
    code, end = uncomment(source), 0
    for command in ['module', 'prelude']:
        header = re.match(r'\s*' + command + r'\b', code[end:])
        if not header:
            continue
        end += header.end()
        line_end = code.find('\n', end)
        line_end = len(code) if line_end < 0 else line_end
        assert not code[end:line_end].strip(), 'Unsupported ' + command + ' header'
    if end:
        # Insert at the token boundary rather than a comment's internal newline.
        return source[:end] + '\n' + linter + source[end:]
    return linter + source


def clear_authored_artifacts(root, source_files):
    """Force authored recompilation without deleting or traversing dependency caches."""
    library = root / '.lake' / 'build' / 'lib' / 'lean'
    suffixes = ('.olean', '.ilean', '.ir', '.trace')
    removed = []
    for relative in source_files:
        source = Path(relative)
        assert not source.is_absolute() and '..' not in source.parts
        assert source.suffix == '.lean', relative
        module = library / source.with_suffix('')
        current = root
        for part in module.parent.relative_to(root).parts:
            current = current / part
            assert not current.is_symlink(), 'Linked authored artifact directory: ' + str(current)
            assert not current.exists() or current.is_dir(), str(current)
        if not module.parent.is_dir():
            continue
        for artifact in sorted(module.parent.iterdir()):
            if not any(artifact.name == module.name + suffix or
                       artifact.name.startswith(module.name + suffix + '.')
                       for suffix in suffixes):
                continue
            assert artifact.is_file() or artifact.is_symlink(), str(artifact)
            artifact.unlink()
            removed.append(str(artifact.relative_to(root)))
    return removed


def manifest_dependencies(packages):
    """Read supported single-component Lake names without changing package paths or pins."""
    dependencies = {}
    for entry in packages:
        serialized = entry['name']
        assert isinstance(serialized, str), 'Non-string manifest package name'
        name = (serialized[1:-1] if serialized.startswith('«') and serialized.endswith('»')
                else serialized)
        assert re.fullmatch(r'[A-Za-z_][A-Za-z0-9_-]*', name), \
            'Unsupported manifest package name: ' + serialized
        assert name not in dependencies, 'Duplicate manifest package name: ' + name
        dependencies[name] = entry
    return dependencies


def import_roots(config):
    """Allow extra library roots only for explicitly pinned public dependencies."""
    roots = [config['root_module'], config['examples_module']]
    modules = config.get('dependency_modules', {})
    assert isinstance(modules, dict), 'dependency_modules must map dependency names to roots'
    for name, additions in modules.items():
        assert name in config['public_dependencies'], 'Unpinned dependency module: ' + name
        pin = config['public_dependencies'][name]
        assert re.fullmatch(r'[0-9a-f]{40}', pin.get('rev', '')), name
        assert re.fullmatch(r'https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+',
                            pin.get('url', '')), name
        assert isinstance(additions, list) and additions, name
        roots.extend(additions)
    for name in roots:
        assert isinstance(name, str) and re.fullmatch(
            r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", name), name
        assert name != 'Mathlib', 'Use focused Mathlib imports'
    return roots


def allowed_import(module, roots):
    """Recognize focused Mathlib imports and the declared library module roots."""
    return module.startswith('Mathlib.') or any(
        module == root or module.startswith(root + '.') for root in roots)


IDENTIFIER = r"[\w][\w.']*"
LINE_EXCEPTION_REASONS = {
    'Unchanged source identifier with its required local indentation and delimiters; '
    'splitting its name changes the public API.',
    'Unchanged source declaration identifier cannot be split without changing the public API.',
    'Long Lean identifier cannot be split without changing the public API or Lean layout.',
}


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def check_line_lengths(source, relative, exceptions):
    """Accept only exactly pinned long-identifier lines, never ordinary prose or expressions."""
    assert isinstance(exceptions, list), relative
    pins = {}
    for entry in exceptions:
        assert isinstance(entry, dict) and set(entry) == {'line', 'sha256', 'reason'}, entry
        number = entry['line']
        assert type(number) is int and number > 0 and number not in pins, entry
        assert re.fullmatch(r'[0-9a-f]{64}', entry['sha256']), entry
        assert entry['reason'] in LINE_EXCEPTION_REASONS, 'Unjustified line exception: ' + relative
        pins[number] = entry
    code_lines = uncomment(source).splitlines()
    used = set()
    for number, line in enumerate(source.splitlines(), 1):
        if len(line) <= 100:
            continue
        assert number in pins, f'{relative}:{number}: line exceeds 100 columns'
        entry = pins[number]
        assert sha256(line.encode()) == entry['sha256'], 'Stale line exception: ' + relative
        code = code_lines[number - 1]
        quoted_name = re.fullmatch(r'\s*`(' + IDENTIFIER + r')`[.,]?\s*', line)
        if not code.strip() and quoted_name:
            assert len(quoted_name[1]) >= 80, 'Short documented identifier exception: ' + relative
            used.add(number)
            continue
        tokens = re.findall(IDENTIFIER, code)
        # An exception may retain Lean's required layout around one long indivisible name.
        # A line with multiple names, ordinary text, comments, or an operator is wrappable.
        assert len(tokens) == 1 and len(tokens[0]) >= 80, \
            'Exception does not identify a long Lean identifier: ' + relative
        residue = re.sub(IDENTIFIER, '', code)
        assert re.fullmatch(r'[\s()\[\]{},:;|⟨⟩]*', residue), \
            'Ordinary expression cannot receive a line exception: ' + relative
        assert line.strip() == code.strip(), 'Comment/string line exception: ' + relative
        used.add(number)
    assert used == set(pins), 'Stale or extra line exceptions: ' + relative


def axiom_reports(output, names):
    """Preserve prime suffixes in both requested names and Lean's quoted audit output."""
    pattern = r"'([\w.']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    reports = re.findall(pattern, output)
    assert len(reports) == len(names) and {name for name, _ in reports} == set(names), \
        'Axiom report coverage differs from declaration manifest'
    result = {}
    for name, raw in reports:
        axioms = {item.strip() for item in raw.split(',') if item.strip()}
        assert axioms <= {'Classical.choice', 'Quot.sound', 'propext'}, (name, axioms)
        result[name] = sorted(axioms)
    return result


def messages(output):
    check_diagnostics(output, json_mode=True)
    return '\n'.join(json.loads(line)['data'] for line in output.splitlines() if line.strip())


class EvidenceRunner:
    """Persist passed stages only after all diagnostics and stage-specific checks succeed."""

    def __init__(self, root, evidence, record, previous=None):
        self.root, self.evidence, self.record = root, evidence, record
        self.previous = {}
        for stage in (previous or {}).get('stages', []):
            assert stage['name'] not in self.previous, 'Duplicate evidence stage'
            self.previous[stage['name']] = stage

    def save(self):
        temporary = self.evidence / 'qualification.json.tmp'
        temporary.write_text(json.dumps(self.record, indent=2) + '\n')
        temporary.replace(self.evidence / 'qualification.json')

    def cached(self, name, command, stdin=None):
        stage = self.previous.get(name, {})
        log = self.evidence / (name + '.log')
        return (stage.get('status') == 'passed' and stage.get('exit_code') == 0 and
                stage.get('command') == command and
                stage.get('stdin_sha256') == sha256((stdin or '').encode()) and
                log.is_file() and not log.is_symlink() and
                stage.get('log_sha256') == sha256(log.read_bytes()))

    def run(self, name, command, stdin=None, validate=None, *, cache=True):
        assert re.fullmatch(r'[A-Za-z0-9_.-]+', name), name
        assert not any(stage['name'] == name for stage in self.record['stages']), name
        stage = {'name': name, 'command': command, 'status': 'running',
                 'stdin_sha256': sha256((stdin or '').encode())}
        reused = cache and self.cached(name, command, stdin)
        self.record['stages'].append(stage)
        self.save()
        try:
            if reused:
                output = (self.evidence / (name + '.log')).read_text()
                exit_code = 0
            else:
                result = subprocess.run(command, cwd=self.root, input=stdin, text=True,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                output, exit_code = result.stdout, result.returncode
                (self.evidence / (name + '.log')).write_text(output)
            stage.update(exit_code=exit_code, log_sha256=sha256(output.encode()), reused=reused)
            assert exit_code == 0, name
            check_diagnostics(output)
            if validate:
                validate(output)
            stage['status'] = 'passed'
            self.save()
            print(name, 'reused' if reused else exit_code, flush=True)
            return output
        except BaseException:
            stage['status'] = 'failed'
            self.save()
            raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--evidence-dir', type=Path)
    parser.add_argument('--resume', action='store_true',
                        help='Reuse fully passed stages in the same matching evidence directory')
    args = parser.parse_args()
    assert not args.resume or args.evidence_dir, '--resume requires --evidence-dir'
    root = Path(__file__).resolve().parent.parent
    config_path = root / 'verification.json'
    config = json.loads(config_path.read_text())
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    evidence = (args.evidence_dir or root / 'verification-artifacts' / stamp).resolve()
    previous = None
    if args.resume:
        assert evidence.is_dir(), 'Resume evidence directory does not exist'
        previous = json.loads((evidence / 'qualification.json').read_text())
    else:
        evidence.mkdir(parents=True, exist_ok=False)
    record = {'status': 'running', 'stages': [], 'source_sha256': {}, 'axioms': {},
              'scope': 'Authored sources and explicit named transitive dependencies'}
    runner = EvidenceRunner(root, evidence, record)
    # Do not overwrite existing evidence before deciding whether its identity matches.
    try:
        assert previous is None or previous.get('identity'), \
            'Prior evidence has no qualified input identity'
        actual_sources = {str(path.relative_to(root)) for path in root.rglob('*.lean')
                          if not {'.lake', '.git', 'verification-artifacts'} &
                          set(path.relative_to(root).parts) and not path.is_relative_to(evidence)}
        assert actual_sources == set(config['source_files']) | {'lakefile.lean'}, \
            'Authored Lean file coverage differs from manifest'
        source_files = config['source_files']
        assert len(source_files) == len(set(source_files)), 'Duplicate source path'
        exceptions = config.get('long_identifier_line_exceptions', {})
        assert isinstance(exceptions, dict) and set(exceptions) <= set(source_files), \
            'Extra or invalid line-exception paths'
        assert all(isinstance(entries, list) and entries for entries in exceptions.values()), \
            'Empty or invalid line-exception entries'
        roots = import_roots(config)
        names = []
        for relative in source_files:
            path = Path(relative)
            assert not path.is_absolute() and '..' not in path.parts and path.suffix == '.lean'
            path = root / path
            assert not path.is_symlink(), 'Linked authored source: ' + relative
            source = path.read_text()
            code = uncomment(source)
            record['source_sha256'][relative] = sha256(path.read_bytes())
            assert not re.search(r'\b(?:sorry|admit|sorryAx)\b', code), relative
            assert not re.search(
                r'^\s*(?:@\[[^\]]*\]\s*)*'
                r'(?:(?:private|protected|unsafe|noncomputable)\s+)*(?:axiom|constant)\b',
                code, re.M), relative
            check_line_lengths(source, relative, exceptions.get(relative, []))
            assert source.count('Copyright (c)') == 1 and '/-!' in source, relative
            for module in imported_modules(source):
                assert allowed_import(module, roots), (relative, module)
            names.extend(declarations(source))
        assert names and len(names) == len(set(names)), 'Duplicate or empty declaration list'
        assert names == config['declarations'], 'Declaration manifest differs from actual sources'
        toolchain = (root / 'lean-toolchain').read_text().strip()
        # Version checks are fresh, never replayed from previous evidence.
        version_result = subprocess.run(['lake', 'env', 'lean', '--version'], cwd=root,
                                        text=True, stdout=subprocess.PIPE,
                                        stderr=subprocess.STDOUT)
        version = version_result.stdout.strip()
        assert version_result.returncode == 0, 'Compiler version command failed'
        check_diagnostics(version)
        assert toolchain == 'leanprover/lean4:v4.34.1' and 'version 4.34.1,' in version
        record['compiler_version'] = version
        manifest = json.loads((root / 'lake-manifest.json').read_text())
        dependencies = manifest_dependencies(manifest['packages'])
        assert set(dependencies) == set(config['public_dependencies'])
        record['dependency_revisions'] = {}
        for name, expected in config['public_dependencies'].items():
            actual = dependencies[name]
            assert actual['type'] == 'git' and actual['rev'] == expected['rev']
            assert actual['url'] == expected['url']
            git = ['git', '--no-optional-locks', '--no-replace-objects', '-C',
                   str(root / '.lake/packages' / name)]
            head = subprocess.check_output(git + ['rev-parse', 'HEAD'], text=True).strip()
            assert head == expected['rev'], name
            assert not subprocess.check_output(
                git + ['status', '--porcelain', '--untracked-files=no'], text=True).strip(), \
                'Modified dependency checkout: ' + name
            record['dependency_revisions'][name] = head
        identity = {
            'source_sha256': record['source_sha256'], 'compiler_version': version,
            'dependency_revisions': record['dependency_revisions'],
            'input_sha256': {name: sha256((root / name).read_bytes()) for name in
                             ['verification.json', 'lakefile.lean', 'lake-manifest.json',
                              'lean-toolchain', 'scripts/verify.py']},
        }
        assert previous is None or previous['identity'] == identity, \
            'Resume identity differs: sources, compiler, dependencies, verifier, or config changed'
        record['identity'] = identity
        runner.previous = EvidenceRunner(root, evidence, record, previous).previous
        runner.save()
        (evidence / 'compiler-version.log').write_text(version_result.stdout)
        record['compiler_version_exit_code'] = version_result.returncode
        targets = ['+' + str(Path(path).with_suffix('')).replace('/', '.') + ':olean'
                   for path in source_files]
        build_command = ['lake', '--rehash', '--wfail', 'build', *targets]
        if not runner.cached('exact-build', build_command):
            record['removed_authored_artifacts'] = clear_authored_artifacts(root, source_files)
        else:
            record['removed_authored_artifacts'] = previous.get('removed_authored_artifacts', [])
        runner.save()
        runner.run('exact-build', build_command)

        def lint_passed(output):
            clean = messages(output)
            assert '-- All linting checks passed!' in clean
            assert 'with 16 linters' in clean

        for relative in source_files:
            path = evidence / 'lint-sources' / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(lint_source((root / relative).read_text()) +
                            '\n#lint docBlame docBlameThm\n')
            runner.run('lint-' + relative.replace('/', '-'),
                       ['lake', 'env', 'lean', '-j2', '--json',
                        '--root=' + str(evidence / 'lint-sources'), str(path)],
                       validate=lint_passed)
        probe = '\n'.join('import ' + name for name in config['audit_imports']) + '\n'
        probe += '\n'.join('#print axioms ' + name for name in names) + '\n'
        (evidence / 'axioms.lean').write_text(probe)

        def audit_passed(output):
            record['axioms'] = axiom_reports(messages(output), names)

        runner.run('axioms', ['lake', 'env', 'lean', '-j2', '--json',
                             str(evidence / 'axioms.lean')], validate=audit_passed)
        assert identity['source_sha256'] == {
            relative: sha256((root / relative).read_bytes()) for relative in source_files
        }, 'Authored sources changed during verification'
        assert identity['input_sha256'] == {
            name: sha256((root / name).read_bytes()) for name in identity['input_sha256']
        }, 'Verification inputs changed during verification'
        record.update(status='passed', full_linter_count=16, named_declaration_count=len(names))
        runner.save()
        print('PASS:', len(source_files), 'files;', len(names), 'named declarations')
    except BaseException as error:
        # Rejected input identities must never leave a stale top-level passed flag.
        if previous is not None and 'identity' not in record:
            (evidence / 'qualification.previous.json').write_text(
                json.dumps(previous, indent=2) + '\n')
            record.update(status='rejected', failure=str(error))
            runner.save()
            raise
        record.update(status='interrupted' if isinstance(error, KeyboardInterrupt) else 'failed',
                      failure=str(error))
        runner.save()
        raise


if __name__ == '__main__':
    main()
