"""Tests for the fail-closed audit, independent of the Lean proof run."""
import unittest
from verify import ALLOWED, IMPORTS, audit, guard


class AuditTests(unittest.TestCase):
    def test_standard_axioms(self):
        text = "'a' depends on axioms: [propext,\n Classical.choice, Quot.sound]"
        self.assertEqual(set(audit(text, ('a',))['a']), ALLOWED)

    def test_axiom_free(self):
        self.assertEqual(audit("'a' does not depend on any axioms", ('a',)), {'a': []})

    def test_missing_report(self):
        with self.assertRaises(ValueError):
            audit('', ('a',))

    def test_duplicate_report(self):
        with self.assertRaises(ValueError):
            audit("'a' does not depend on any axioms\n" * 2, ('a',))

    def test_unapproved_axioms(self):
        for name in ('sorryAx', 'forged', 'Lean.ofReduceBool'):
            with self.subTest(name=name), self.assertRaises(ValueError):
                audit("'a' depends on axioms: [propext, %s]" % name, ('a',))

    def test_unexpected_name(self):
        with self.assertRaises(ValueError):
            audit("'not_a' depends on axioms: [propext]", ('a',))

    def test_source_guard(self):
        header = ''.join('import ' + m + '\n' for m in IMPORTS)
        guard(header + 'theorem good : True := by trivial\n')
        for bad in ('sorry', 'admit', 'native_decide', 'unsafe',
                    'axiom fake : False', 'set_option debug.skipKernelTC true'):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                guard(header + bad + '\n')

    def test_unapproved_import(self):
        with self.assertRaises(ValueError):
            guard('import UnknownAssumptions\ntheorem good : True := by trivial\n')


if __name__ == '__main__':
    unittest.main()
