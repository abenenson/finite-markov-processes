"""Offline controls for cache scope and public dependency coverage."""
from pathlib import Path
import tempfile
import unittest

import fetch_mathlib_cache as cache


class CacheScopeControls(unittest.TestCase):
    def fixture(self, root):
        (root / 'Fixture.lean').write_text(
            '/- import Mathlib.Hidden -/\nimport\n Mathlib.Data.Bool.Basic\n'
            'namespace Fixture\ndef text := "import Mathlib.Hidden"\nend Fixture\n')
        return {'root_module': 'Fixture', 'examples_module': 'FixtureExamples',
                'source_files': ['Fixture.lean'], 'public_dependencies': {}}

    def test_focused_multiline_imports_and_linter_are_included(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = self.fixture(root)
            self.assertEqual(cache.mathlib_imports(root, config),
                             ['Mathlib.Data.Bool.Basic', 'Mathlib.Tactic.Linter.Lint'])

    def test_public_dependency_sources_extend_scope(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = self.fixture(root)
            config['public_dependencies']['public-library'] = {
                'url': 'https://github.com/example/public-library', 'rev': 'a' * 40}
            config['dependency_modules'] = {'public-library': ['PublicLibrary']}
            provider = root / '.lake/packages/public-library/PublicLibrary'
            provider.mkdir(parents=True)
            (provider / 'Basic.lean').write_text(
                'module\npublic import Mathlib.Data.Nat.Basic\n')
            self.assertIn('Mathlib.Data.Nat.Basic', cache.mathlib_imports(root, config))

    def test_bare_mathlib_and_private_imports_are_rejected(self):
        for module in ['Mathlib', 'Private.Internal']:
            with self.subTest(module=module), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                config = self.fixture(root)
                (root / 'Fixture.lean').write_text('import ' + module + '\n')
                with self.assertRaises(AssertionError):
                    cache.mathlib_imports(root, config)

    def test_missing_dependency_source_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = self.fixture(root)
            config['public_dependencies']['public-library'] = {
                'url': 'https://github.com/example/public-library', 'rev': 'a' * 40}
            config['dependency_modules'] = {'public-library': ['PublicLibrary']}
            with self.assertRaisesRegex(AssertionError, 'Missing pinned dependency'):
                cache.mathlib_imports(root, config)


if __name__ == '__main__':
    unittest.main()
