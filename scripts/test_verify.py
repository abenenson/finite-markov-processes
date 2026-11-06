"""Regression controls for acceptance failures; no Lean installation is needed."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).with_name('verify.py')
spec = importlib.util.spec_from_file_location('standalone_verify', SCRIPT)
verify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)


def fixture_repository(root):
    """Create a minimal, isolated repository for mocked end-to-end verifier controls."""
    (root / 'scripts').mkdir(parents=True)
    (root / 'scripts/verify.py').write_bytes(SCRIPT.read_bytes())
    (root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
    (root / 'lakefile.lean').write_text('import Lake\n')
    (root / 'lake-manifest.json').write_text(json.dumps({'packages': []}))
    config = {'root_module': 'Fixture', 'examples_module': 'FixtureExamples',
              'source_files': ['Fixture.lean'], 'audit_imports': ['Fixture'],
              'declarations': ['Fixture.identity'], 'public_dependencies': {}}
    (root / 'verification.json').write_text(json.dumps(config))
    (root / 'Fixture.lean').write_text(
        '/- Copyright (c) 2026 Adam Benenson. -/\n/-! Fixture -/\n'
        'namespace Fixture\ntheorem identity : True := by trivial\nend Fixture\n')


class VerificationControls(unittest.TestCase):
    def test_clean_plain_and_json_information(self):
        verify.check_diagnostics('Build completed successfully.\n')
        verify.check_diagnostics(json.dumps({'severity': 'information', 'data': 'checked'}),
                                 json_mode=True)

    def test_native_and_plain_diagnostic_rejection(self):
        for text in ['PANIC at kernel', 'panic: kernel', 'error: fixture',
                     'file.lean:3:2: warning: fixture']:
            with self.subTest(text=text), self.assertRaises(AssertionError):
                verify.check_diagnostics(text)

    def test_json_failures_rejected(self):
        for obj in [{'severity': 'error', 'data': 'fixture'},
                    {'severity': 'warning', 'data': 'fixture'},
                    {'severity': 'information', 'data': 'PANIC at kernel'},
                    {'severity': 'information', 'data': 'error: fixture'},
                    {'error': 'unrecognized diagnostic'},
                    {'severity': 'fatal', 'data': 'fixture'},
                    {'severity': 'information'}, []]:
            with self.subTest(obj=obj), self.assertRaises(AssertionError):
                verify.check_diagnostics(json.dumps(obj), json_mode=True)
        with self.assertRaises(AssertionError):
            verify.check_diagnostics('{"severity":"error"')
        with self.assertRaises(AssertionError):
            verify.check_diagnostics('unstructured output', json_mode=True)

    def test_every_import_is_returned(self):
        text = ('/- import Ignored.Comment -/\n'
                '  public import Mathlib.Data.Bool.Basic Private.Hidden\n'
                'import\n  Mathlib.Data.Nat.Basic\n  Private.Multiline\n'
                'namespace X\ndef s := "import Ignored.String"\nend X\n')
        self.assertEqual(verify.imported_modules(text),
                         ['Mathlib.Data.Bool.Basic', 'Private.Hidden',
                          'Mathlib.Data.Nat.Basic', 'Private.Multiline'])

    def test_unsupported_import_fails_closed(self):
        for text in ['import «Unsupported»', 'import\nnamespace X\nend X']:
            with self.subTest(text=text), self.assertRaises(AssertionError):
                verify.imported_modules(text)

    def test_optimized_python_refused(self):
        result = subprocess.run([sys.executable, '-O', str(SCRIPT), '--help'],
                                text=True, capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('requires enabled Python assertions', result.stderr)

    def test_manifest_quoted_package_names_use_plain_keys(self):
        mathlib = {'name': 'mathlib', 'rev': 'a' * 40}
        markov = {'name': '«finite-markov-kernels»', 'rev': 'b' * 40}
        dependencies = verify.manifest_dependencies([mathlib, markov])
        self.assertEqual(set(dependencies), {'mathlib', 'finite-markov-kernels'})
        self.assertIs(dependencies['mathlib'], mathlib)
        self.assertIs(dependencies['finite-markov-kernels'], markov)

    def test_manifest_invalid_and_colliding_package_names_refused(self):
        for name in ['', '../outside', 'a/b', 'a.b', '«a.b»', '«a b»', '«a»»',
                     '«nested«name»»', '«unclosed', 'unopened»', None, 42]:
            with self.subTest(name=name), self.assertRaises(AssertionError):
                verify.manifest_dependencies([{'name': name}])
        for names in [('mathlib', 'mathlib'),
                      ('finite-markov-kernels', '«finite-markov-kernels»')]:
            with self.subTest(names=names), self.assertRaisesRegex(
                    AssertionError, 'Duplicate manifest package name'):
                verify.manifest_dependencies([{'name': name} for name in names])

    def test_only_declared_dependency_module_roots_are_allowed(self):
        config = {'root_module': 'Fixture', 'examples_module': 'FixtureExamples',
                  'public_dependencies': {'entropy': {'rev': 'a' * 40,
                      'url': 'https://github.com/example/entropy'}},
                  'dependency_modules': {'entropy': ['FiniteRelativeEntropy']}}
        roots = verify.import_roots(config)
        for module in ['Fixture', 'Fixture.Basic', 'FixtureExamples.Basic',
                       'FiniteRelativeEntropy', 'FiniteRelativeEntropy.GibbsVariational',
                       'Mathlib.Data.Real.Basic']:
            self.assertTrue(verify.allowed_import(module, roots), module)
        for module in ['Private.Hidden', 'FiniteRelativeEntropyOther.Basic', 'Mathlib']:
            self.assertFalse(verify.allowed_import(module, roots), module)

    def test_dependency_module_without_exact_public_pin_is_refused(self):
        config = {'root_module': 'Fixture', 'examples_module': 'FixtureExamples',
                  'public_dependencies': {}, 'dependency_modules': {'entropy': ['Entropy']}}
        with self.assertRaisesRegex(AssertionError, 'Unpinned dependency module'):
            verify.import_roots(config)
        for pin in [{}, {'rev': 'main', 'url': 'https://github.com/example/entropy'},
                    {'rev': 'a' * 40, 'url': '/private/local/entropy'}]:
            config['public_dependencies'] = {'entropy': pin}
            with self.subTest(pin=pin), self.assertRaises(AssertionError):
                verify.import_roots(config)

    def test_authored_artifacts_removed_without_touching_other_outputs(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            library = root / '.lake/build/lib/lean'
            dependency = root / '.lake/packages/mathlib/.lake/build/lib/lean/Fixture.olean'
            dependency.parent.mkdir(parents=True)
            dependency.write_bytes(b'dependency cache')
            library.mkdir(parents=True)
            unrelated = library / 'Unrelated.olean'
            unrelated.write_bytes(b'unrelated output')
            stale = [library / ('Fixture' + suffix) for suffix in
                     ('.olean', '.olean.private', '.olean.server', '.ir', '.ilean.hash', '.trace')]
            for path in stale:
                path.write_bytes(b'stale authored artifact')
            removed = verify.clear_authored_artifacts(root, ['Fixture.lean'])
            self.assertEqual(set(removed), {str(path.relative_to(root)) for path in stale})
            self.assertTrue(all(not path.exists() for path in stale))
            self.assertEqual(dependency.read_bytes(), b'dependency cache')
            self.assertEqual(unrelated.read_bytes(), b'unrelated output')

    def test_linked_artifact_directory_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / 'repo'
            external = Path(temp) / 'external'
            external.mkdir()
            artifact = external / 'Fixture.olean'
            artifact.write_bytes(b'preserve external artifact')
            library = root / '.lake/build/lib/lean'
            library.parent.mkdir(parents=True)
            library.symlink_to(external, target_is_directory=True)
            with self.assertRaisesRegex(AssertionError, 'Linked authored artifact directory'):
                verify.clear_authored_artifacts(root, ['Fixture.lean'])
            self.assertEqual(artifact.read_bytes(), b'preserve external artifact')

    def test_cached_authored_artifact_is_removed_before_exact_build(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / 'repo'
            fixture_repository(root)
            stale = root / '.lake/build/lib/lean/Fixture.olean'
            stale.parent.mkdir(parents=True)
            stale.write_bytes(b'invalid cached authored artifact')

            def fake_run(command, **kwargs):
                if command == ['lake', 'env', 'lean', '--version']:
                    output = 'Lean (version 4.34.1, fixture)'
                elif 'build' in command:
                    self.assertFalse(
                        stale.exists(), 'Exact build consumed a cached author artifact')
                    stale.write_bytes(b'fresh authored artifact')
                    output = 'Build completed successfully.'
                elif command[-1].endswith('axioms.lean'):
                    output = json.dumps({'severity': 'information',
                                         'data': "'Fixture.identity' depends on axioms: [propext]"})
                else:
                    output = json.dumps({'severity': 'information',
                                         'data': '-- All linting checks passed! with 16 linters'})
                return SimpleNamespace(returncode=0, stdout=output)

            evidence = Path(temp) / 'evidence'
            with patch.object(verify, '__file__', str(root / 'scripts/verify.py')), \
                 patch.object(sys, 'argv', [str(SCRIPT), '--evidence-dir', str(evidence)]), \
                 patch.object(verify.subprocess, 'run', side_effect=fake_run):
                verify.main()
            record = json.loads((evidence / 'qualification.json').read_text())
            self.assertEqual(record['status'], 'passed')
            self.assertEqual(record['removed_authored_artifacts'],
                             ['.lake/build/lib/lean/Fixture.olean'])
            self.assertEqual(stale.read_bytes(), b'fresh authored artifact')

    def test_zero_exit_exact_build_error_rejected_end_to_end(self):
        def fake_run(command, **kwargs):
            if command == ['lake', 'env', 'lean', '--version']:
                output = 'Lean (version 4.34.1, fixture)'
            else:
                self.assertIn('build', command)
                output = json.dumps({'severity': 'error', 'data': 'synthetic exact-build failure'})
            return SimpleNamespace(returncode=0, stdout=output)

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / 'repo'
            fixture_repository(root)
            evidence = Path(temp) / 'failed-run'
            with patch.object(verify, '__file__', str(root / 'scripts/verify.py')), \
                 patch.object(sys, 'argv', [str(SCRIPT), '--evidence-dir', str(evidence)]), \
                 patch.object(verify.subprocess, 'run', side_effect=fake_run):
                with self.assertRaises(AssertionError):
                    verify.main()
            record = json.loads((evidence / 'qualification.json').read_text())
            self.assertEqual(record['status'], 'failed')
            self.assertEqual(record['stages'][-1]['name'], 'exact-build')
            self.assertEqual(record['stages'][-1]['exit_code'], 0)
            self.assertIn('synthetic exact-build failure', record['failure'])


class LintHeaderControls(unittest.TestCase):
    def test_ordinary_header_prepends_linter_and_keeps_public_import(self):
        source = ('/-! Header mentioning module -/\n'
                  'public import Mathlib.Data.Bool.Basic\nnamespace Example\nend Example\n')
        result = verify.lint_source(source)
        self.assertTrue(result.startswith('import Mathlib.Tactic.Linter.Lint\n'))
        self.assertTrue(result.endswith(source))
        self.assertEqual(verify.imported_modules(result),
                         ['Mathlib.Tactic.Linter.Lint', 'Mathlib.Data.Bool.Basic'])

    def test_module_header_remains_first_and_comments_are_preserved(self):
        source = ('/-! Leading header, module in comments is not a command. -/\n'
                  'module -- trailing module comment\n'
                  'public import Mathlib.Data.Bool.Basic\n')
        result = verify.lint_source(source)
        self.assertEqual(verify.uncomment(result).split(),
                         ['module', 'import', 'Mathlib.Tactic.Linter.Lint',
                          'public', 'import', 'Mathlib.Data.Bool.Basic'])
        self.assertIn('/-! Leading header, module in comments is not a command. -/', result)
        self.assertIn('-- trailing module comment', result)
        self.assertEqual(verify.imported_modules(result),
                         ['Mathlib.Tactic.Linter.Lint', 'Mathlib.Data.Bool.Basic'])

    def test_multiline_comment_after_module_does_not_absorb_linter_import(self):
        source = 'module /- comment with\ninternal newline -/\nimport Mathlib.Data.Nat.Basic\n'
        result = verify.lint_source(source)
        self.assertEqual(verify.imported_modules(result),
                         ['Mathlib.Tactic.Linter.Lint', 'Mathlib.Data.Nat.Basic'])
        self.assertIn('/- comment with\ninternal newline -/', result)

    def test_module_in_string_or_comment_does_not_change_header_placement(self):
        for source in ['/- module -/\npublic import Mathlib.Data.Bool.Basic\n',
                       'def text := "module"\n']:
            result = verify.lint_source(source)
            self.assertEqual(result, 'import Mathlib.Tactic.Linter.Lint\n' + source)

    def test_module_and_prelude_both_precede_all_imports(self):
        source = ('/- Copyright with /- nested module -/ comment -/\nmodule\n'
                  '/- between commands -/\nprelude -- keep this comment\n'
                  'public import Init.Prelude\n')
        result = verify.lint_source(source)
        self.assertEqual(verify.uncomment(result).split(),
                         ['module', 'prelude', 'import', 'Mathlib.Tactic.Linter.Lint',
                          'public', 'import', 'Init.Prelude'])
        self.assertIn('/- between commands -/', result)
        self.assertIn('-- keep this comment', result)

    def test_special_trailing_module_comment_keeps_its_original_attachment(self):
        source = ('module -- deprecated_module: ignore\n'
                  'public import Mathlib.Data.Bool.Basic\n')
        result = verify.lint_source(source)
        self.assertTrue(result.startswith('module -- deprecated_module: ignore\nimport '))
        self.assertEqual(verify.imported_modules(result),
                         ['Mathlib.Tactic.Linter.Lint', 'Mathlib.Data.Bool.Basic'])

    def test_eof_module_header_gets_a_separate_import_line(self):
        source = 'module -- trailing comment without a final newline'
        self.assertEqual(verify.lint_source(source),
                         source + '\nimport Mathlib.Tactic.Linter.Lint\n')

    def test_prelude_alone_remains_before_linter_import(self):
        source = '/- comment -/\nprelude\nimport Init.Prelude\n'
        self.assertEqual(verify.uncomment(verify.lint_source(source)).split(),
                         ['prelude', 'import', 'Mathlib.Tactic.Linter.Lint',
                          'import', 'Init.Prelude'])

    def test_nonstandalone_module_header_fails_closed(self):
        with self.assertRaisesRegex(AssertionError, 'Unsupported module header'):
            verify.lint_source('module unsupported\n')


class PrimeAndLineExceptionControls(unittest.TestCase):
    def test_prime_declarations_remain_distinct(self):
        source = ("namespace Example'\nnoncomputable section\n"
                  "theorem continuousTestIntegral_add : True := by trivial\n"
                  "theorem continuousTestIntegral_add' : True := by trivial\n"
                  "theorem continuousTestIntegral_add'' : True := by trivial\n"
                  "end\nend Example'\n")
        self.assertEqual(verify.declarations(source),
                         ["Example'.continuousTestIntegral_add" + suffix
                          for suffix in ['', "'", "''"]])

    def test_multiline_names_and_prime_suffixes_are_audited(self):
        source = ("namespace Example\nnoncomputable section\n"
                  "@[simp] theorem\n  /- a comment between command and name -/\n"
                  "  longTheorem' : True := by trivial\n"
                  "noncomputable def\n\nlongDefinition : Nat := 1\n"
                  "private theorem\n  hidden : True := by trivial\n"
                  "instance\n  : Inhabited Nat := inferInstance\n"
                  "end\nend Example\n")
        self.assertEqual(verify.declarations(source),
                         ["Example.longTheorem'", 'Example.longDefinition'])

    def test_named_inductive_types_are_audited_without_generated_constructors(self):
        source = ("namespace Example\ninductive Phase where\n"
                  "  | initial\n  | terminal\n"
                  "inductive\n  Direction where\n  | left\n  | right\n"
                  "private inductive Hidden where\n  | secret\n"
                  "opaque opaqueValue' : Nat := 1\nend Example\n")
        self.assertEqual(verify.declarations(source),
                         ['Example.Phase', 'Example.Direction', "Example.opaqueValue'"])

    def test_prime_axiom_reports_have_exact_coverage(self):
        names = ['Example.add', "Example.add'", "Example.add''"]
        output = ("'Example.add' depends on axioms: [propext]\n"
                  "'Example.add'' does not depend on any axioms\n"
                  "'Example.add''' depends on axioms: [Classical.choice, Quot.sound]\n")
        self.assertEqual(verify.axiom_reports(output, names),
                         {'Example.add': ['propext'], "Example.add'": [],
                          "Example.add''": ['Classical.choice', 'Quot.sound']})
        with self.assertRaises(AssertionError):
            verify.axiom_reports(output.replace("'Example.add'' does", "'Example.add' does"),
                                 names)

    def pin(self, source_line, **changes):
        result = {'line': 1, 'sha256': verify.sha256(source_line.encode()),
                  'reason': 'Long Lean identifier cannot be split without changing '
                            'the public API or Lean layout.'}
        result.update(changes)
        return result

    def test_exact_long_identifier_with_lean_layout_is_allowed(self):
        line = ' ' * 16 + '(' + 'declaration_' + 'a' * 85 + ']'
        verify.check_line_lengths(line, 'Fixture.lean', [self.pin(line)])

    def test_stale_extra_duplicate_and_unjustified_pins_rejected(self):
        line = ' ' * 16 + 'declaration_' + 'a' * 85
        cases = [[self.pin(line, sha256='0' * 64)], [self.pin(line, line=2)],
                 [self.pin(line), self.pin(line)], [self.pin(line, reason='convenient')],
                 [dict(self.pin(line), unknown=True)], [self.pin(line, line=True)]]
        for pins in cases:
            with self.subTest(pins=pins), self.assertRaises(AssertionError):
                verify.check_line_lengths(line, 'Fixture.lean', pins)
        with self.assertRaises(AssertionError):
            verify.check_line_lengths('short', 'Fixture.lean', [self.pin('short')])

    def test_ordinary_long_code_comments_and_strings_cannot_be_exempted(self):
        for line in ['long_' + 'a' * 101 + ' another_name',
                     'long_' + 'a' * 101 + ' +', '-- ' + 'a' * 110,
                     '"' + 'a' * 110 + '"', ' ' * 105 + 'short']:
            with self.subTest(line=line), self.assertRaises(AssertionError):
                verify.check_line_lengths(line, 'Fixture.lean', [self.pin(line)])


class ResumeControls(unittest.TestCase):
    def invocation(self, root, evidence, fake_run, *, resume=False):
        arguments = [str(SCRIPT), '--evidence-dir', str(evidence)]
        if resume:
            arguments.append('--resume')
        with patch.object(verify, '__file__', str(root / 'scripts/verify.py')), \
             patch.object(sys, 'argv', arguments), \
             patch.object(verify.subprocess, 'run', side_effect=fake_run):
            verify.main()

    @staticmethod
    def success(command, **kwargs):
        if command == ['lake', 'env', 'lean', '--version']:
            output = 'Lean (version 4.34.1, fixture)'
        elif 'build' in command:
            output = 'Build completed successfully.'
        elif command[-1].endswith('axioms.lean'):
            output = json.dumps({'severity': 'information',
                                 'data': "'Fixture.identity' depends on axioms: [propext]"})
        else:
            output = json.dumps({'severity': 'information',
                                 'data': '-- All linting checks passed! with 16 linters'})
        return SimpleNamespace(returncode=0, stdout=output)

    def test_failed_lint_is_rerun_while_passed_build_is_reused(self):
        with tempfile.TemporaryDirectory() as temp:
            root, evidence = Path(temp) / 'repo', Path(temp) / 'evidence'
            fixture_repository(root)

            def failure(command, **kwargs):
                if command[-1].endswith('Fixture.lean'):
                    return SimpleNamespace(returncode=0, stdout=json.dumps(
                        {'severity': 'error', 'data': 'synthetic lint failure'}))
                return self.success(command, **kwargs)

            with self.assertRaises(AssertionError):
                self.invocation(root, evidence, failure)
            failed = json.loads((evidence / 'qualification.json').read_text())
            self.assertEqual(failed['status'], 'failed')
            self.assertEqual(failed['stages'][-1]['status'], 'failed')
            calls = []

            def resumed(command, **kwargs):
                calls.append(command)
                return self.success(command, **kwargs)

            self.invocation(root, evidence, resumed, resume=True)
            self.assertFalse(any('build' in command for command in calls))
            self.assertTrue(any(command[-1].endswith('Fixture.lean') for command in calls))
            passed = json.loads((evidence / 'qualification.json').read_text())
            self.assertEqual(passed['status'], 'passed')
            self.assertTrue(passed['stages'][0]['reused'])
            self.assertTrue(all(stage['status'] == 'passed' for stage in passed['stages']))

    def test_all_source_lints_run_after_failure_but_audit_and_pass_are_blocked(self):
        with tempfile.TemporaryDirectory() as temp:
            root, evidence = Path(temp) / 'repo', Path(temp) / 'evidence'
            fixture_repository(root)
            second = root / 'FixtureSecond.lean'
            second.write_text(
                '/- Copyright (c) 2026 Adam Benenson. -/\n/-! Second fixture -/\n'
                'namespace FixtureSecond\ntheorem identity : True := by trivial\n'
                'end FixtureSecond\n')
            config_path = root / 'verification.json'
            config = json.loads(config_path.read_text())
            config['source_files'].append('FixtureSecond.lean')
            config['declarations'].append('FixtureSecond.identity')
            config['audit_imports'].append('FixtureSecond')
            config_path.write_text(json.dumps(config))
            calls = []

            def first_lint_fails(command, **kwargs):
                calls.append(command)
                if command[-1].endswith('/Fixture.lean'):
                    return SimpleNamespace(returncode=0, stdout=json.dumps(
                        {'severity': 'error', 'data': 'synthetic first-source lint failure'}))
                return self.success(command, **kwargs)

            with self.assertRaisesRegex(AssertionError, 'Full-source lint failed for: Fixture.lean'):
                self.invocation(root, evidence, first_lint_fails)
            self.assertTrue(any(command[-1].endswith('/FixtureSecond.lean') for command in calls))
            self.assertFalse(any(command[-1].endswith('axioms.lean') for command in calls))
            self.assertFalse((evidence / 'axioms.lean').exists())
            record = json.loads((evidence / 'qualification.json').read_text())
            self.assertEqual(record['status'], 'failed')
            self.assertEqual([(stage['name'], stage['status']) for stage in record['stages']],
                             [('exact-build', 'passed'), ('lint-Fixture.lean', 'failed'),
                              ('lint-FixtureSecond.lean', 'passed')])
            self.assertEqual([failure['source'] for failure in record['lint_failures']],
                             ['Fixture.lean'])
            self.assertIn('synthetic first-source lint failure',
                          record['lint_failures'][0]['failure'])
            self.assertEqual(record['axioms'], {})
            self.assertNotIn('full_linter_count', record)

    def test_zero_exit_semantically_incomplete_lint_never_becomes_passed(self):
        with tempfile.TemporaryDirectory() as temp:
            root, evidence = Path(temp) / 'repo', Path(temp) / 'evidence'
            fixture_repository(root)

            def incomplete(command, **kwargs):
                if command[-1].endswith('Fixture.lean'):
                    return SimpleNamespace(returncode=0, stdout=json.dumps(
                        {'severity': 'information', 'data': 'lint did not complete'}))
                return self.success(command, **kwargs)

            with self.assertRaises(AssertionError):
                self.invocation(root, evidence, incomplete)
            record = json.loads((evidence / 'qualification.json').read_text())
            self.assertEqual(record['status'], 'failed')
            self.assertEqual(record['stages'][-1]['status'], 'failed')

    def test_changed_inputs_refuse_resume_and_invalidate_current_passed_flag(self):
        changes = [('Fixture.lean', '\n-- changed source\n'),
                   ('scripts/verify.py', '\n# changed verifier\n'),
                   ('lakefile.lean', '\n-- changed build config\n'),
                   ('verification.json', ' '), ('lake-manifest.json', ' ')]
        for relative, addition in changes:
            with self.subTest(relative=relative), tempfile.TemporaryDirectory() as temp:
                root, evidence = Path(temp) / 'repo', Path(temp) / 'evidence'
                fixture_repository(root)
                self.invocation(root, evidence, self.success)
                old_record = (evidence / 'qualification.json').read_bytes()
                path = root / relative
                path.write_text(path.read_text() + addition)
                with self.assertRaisesRegex(AssertionError, 'Resume identity differs'):
                    self.invocation(root, evidence, self.success, resume=True)
                rejected = json.loads((evidence / 'qualification.json').read_text())
                self.assertEqual(rejected['status'], 'rejected')
                self.assertNotIn('identity', rejected)
                self.assertEqual(
                    json.loads((evidence / 'qualification.previous.json').read_text()),
                    json.loads(old_record))

    def test_failed_exact_build_is_never_reused(self):
        with tempfile.TemporaryDirectory() as temp:
            root, evidence = Path(temp) / 'repo', Path(temp) / 'evidence'
            fixture_repository(root)

            def failed_build(command, **kwargs):
                if 'build' in command:
                    return SimpleNamespace(returncode=1, stdout='build did not complete')
                return self.success(command, **kwargs)

            with self.assertRaises(AssertionError):
                self.invocation(root, evidence, failed_build)
            record = json.loads((evidence / 'qualification.json').read_text())
            self.assertEqual(record['status'], 'failed')
            self.assertEqual(record['stages'][0]['status'], 'failed')
            calls = []

            def resumed(command, **kwargs):
                calls.append(command)
                return self.success(command, **kwargs)

            self.invocation(root, evidence, resumed, resume=True)
            self.assertTrue(any('build' in command for command in calls))

    def test_dependency_head_and_cleanliness_are_always_rechecked(self):
        for changed in ['head', 'dirty']:
            with self.subTest(changed=changed), tempfile.TemporaryDirectory() as temp:
                root, evidence = Path(temp) / 'repo', Path(temp) / 'evidence'
                fixture_repository(root)
                config_path = root / 'verification.json'
                config = json.loads(config_path.read_text())
                pin = {'url': 'https://github.com/example/fixture', 'rev': 'a' * 40}
                config['public_dependencies'] = {'fixture-dependency': pin}
                config_path.write_text(json.dumps(config))
                (root / 'lake-manifest.json').write_text(json.dumps({'packages': [
                    dict(pin, name='fixture-dependency', type='git')]}))

                def clean_git(command, **kwargs):
                    return 'a' * 40 if 'rev-parse' in command else ''

                with patch.object(verify.subprocess, 'check_output', side_effect=clean_git):
                    self.invocation(root, evidence, self.success)

                def changed_git(command, **kwargs):
                    if 'rev-parse' in command:
                        return ('b' if changed == 'head' else 'a') * 40
                    return ' M Fixture.lean' if changed == 'dirty' else ''

                with patch.object(verify.subprocess, 'check_output', side_effect=changed_git), \
                     self.assertRaises(AssertionError):
                    self.invocation(root, evidence, self.success, resume=True)
                record = json.loads((evidence / 'qualification.json').read_text())
                self.assertEqual(record['status'], 'rejected')

    def test_missing_resume_identity_invalidates_stale_passed_status(self):
        with tempfile.TemporaryDirectory() as temp:
            root, evidence = Path(temp) / 'repo', Path(temp) / 'evidence'
            fixture_repository(root)
            evidence.mkdir()
            (evidence / 'qualification.json').write_text(json.dumps(
                {'status': 'passed', 'stages': []}))
            with self.assertRaisesRegex(AssertionError, 'no qualified input identity'):
                self.invocation(root, evidence, self.success, resume=True)
            record = json.loads((evidence / 'qualification.json').read_text())
            self.assertEqual(record['status'], 'rejected')

    def test_malformed_config_invalidates_prior_top_level_passed_status(self):
        with tempfile.TemporaryDirectory() as temp:
            root, evidence = Path(temp) / 'repo', Path(temp) / 'evidence'
            fixture_repository(root)
            self.invocation(root, evidence, self.success)
            (root / 'verification.json').write_text('{broken')
            with self.assertRaises(json.JSONDecodeError):
                self.invocation(root, evidence, self.success, resume=True)
            record = json.loads((evidence / 'qualification.json').read_text())
            self.assertEqual(record['status'], 'rejected')

    def test_compiler_identity_always_rechecked(self):
        with tempfile.TemporaryDirectory() as temp:
            root, evidence = Path(temp) / 'repo', Path(temp) / 'evidence'
            fixture_repository(root)
            self.invocation(root, evidence, self.success)

            def changed_version(command, **kwargs):
                self.assertEqual(command, ['lake', 'env', 'lean', '--version'])
                return SimpleNamespace(returncode=0, stdout='Lean (version 4.34.1, changed)')

            with self.assertRaisesRegex(AssertionError, 'Resume identity differs'):
                self.invocation(root, evidence, changed_version, resume=True)

    def test_running_stage_and_tampered_log_are_never_reused(self):
        for mode in ['running', 'tampered', 'missing']:
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as temp:
                root, evidence = Path(temp) / 'repo', Path(temp) / 'evidence'
                fixture_repository(root)
                self.invocation(root, evidence, self.success)
                if mode == 'running':
                    path = evidence / 'qualification.json'
                    record = json.loads(path.read_text())
                    record['status'] = 'running'
                    record['stages'][0]['status'] = 'running'
                    path.write_text(json.dumps(record))
                elif mode == 'tampered':
                    (evidence / 'exact-build.log').write_text('tampered output')
                else:
                    (evidence / 'exact-build.log').unlink()
                calls = []

                def resumed(command, **kwargs):
                    calls.append(command)
                    return self.success(command, **kwargs)

                self.invocation(root, evidence, resumed, resume=True)
                self.assertTrue(any('build' in command for command in calls))

    def test_source_changed_during_last_stage_never_reports_passed(self):
        with tempfile.TemporaryDirectory() as temp:
            root, evidence = Path(temp) / 'repo', Path(temp) / 'evidence'
            fixture_repository(root)

            def mutate_source(command, **kwargs):
                result = self.success(command, **kwargs)
                if command[-1].endswith('axioms.lean'):
                    path = root / 'Fixture.lean'
                    path.write_text(path.read_text() + '-- concurrent change\n')
                return result

            with self.assertRaisesRegex(AssertionError, 'sources changed during verification'):
                self.invocation(root, evidence, mutate_source)
            record = json.loads((evidence / 'qualification.json').read_text())
            self.assertEqual(record['status'], 'failed')

    def test_successful_resume_rechecks_semantic_validation(self):
        with tempfile.TemporaryDirectory() as temp:
            root, evidence = Path(temp) / 'repo', Path(temp) / 'evidence'
            fixture_repository(root)
            self.invocation(root, evidence, self.success)
            calls = []

            def resumed(command, **kwargs):
                calls.append(command)
                return self.success(command, **kwargs)

            self.invocation(root, evidence, resumed, resume=True)
            self.assertEqual(calls, [['lake', 'env', 'lean', '--version']])
            record = json.loads((evidence / 'qualification.json').read_text())
            self.assertEqual(record['status'], 'passed')
            self.assertTrue(all(stage['reused'] for stage in record['stages']))


if __name__ == '__main__':
    unittest.main()
