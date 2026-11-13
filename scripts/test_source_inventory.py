"""Check release inventories before installing or running Lean."""
import json
from pathlib import Path
import unittest

import verify


class SourceInventoryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(__file__).resolve().parent.parent
        cls.plan = json.loads((cls.root / 'source-plan.json').read_text())
        cls.config = json.loads((cls.root / 'verification.json').read_text())

    def test_planning_and_verification_cover_actual_sources(self):
        planned = self.plan['source_files']
        verified = self.config['source_files']
        self.assertEqual(len(planned), len(set(planned)), 'Duplicate planned source')
        self.assertEqual(len(verified), len(set(verified)), 'Duplicate verified source')
        self.assertEqual(set(planned), set(verified), 'Planning/verification inventory drift')
        excluded = {'.lake', '.git', 'verification-artifacts'}
        actual = {str(path.relative_to(self.root)) for path in self.root.rglob('*.lean')
                  if not excluded.intersection(path.relative_to(self.root).parts)}
        self.assertEqual(actual, set(verified) | {'lakefile.lean'})

    def test_named_audit_covers_current_declarations(self):
        names = [name for source in self.config['source_files']
                 for name in verify.declarations((self.root / source).read_text())]
        self.assertEqual(len(names), len(set(names)), 'Duplicate public declaration')
        self.assertEqual(len(self.config['declarations']), len(set(self.config['declarations'])))
        self.assertEqual(names, self.config['declarations'], 'Named axiom audit order or coverage drift')


if __name__ == '__main__':
    unittest.main()
