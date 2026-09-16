#!/usr/bin/env python3
"""Check the exact witness, source correspondence and fail-closed audit paths."""
import json
from pathlib import Path
import re
import unittest
from fractions import Fraction
import check_witness
import verify

ROOT = Path(__file__).resolve().parents[1]

class WitnessTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.w = json.loads((ROOT / 'witness.json').read_text())
        cls.a = cls.w['terms']

    def test_exact_witness(self):
        result = check_witness.check(2, self.a)
        self.assertEqual((result['k'], result['last_exponent'], result['upper_bound']),
                         (185, 392, 374))
        self.assertEqual(result['rational_sum'], '1/2')
        self.assertEqual(int(result['scaled_sum']), 2**391)

    def test_bad_arithmetic_rejected(self):
        with self.assertRaises(ValueError):
            check_witness.check(2, self.a[:-1] + [393])

    def test_duplicates_rejected(self):
        with self.assertRaises(ValueError):
            check_witness.check(2, [3, 6, 6] + self.a[3:])

    def test_wrong_n_rejected(self):
        with self.assertRaises(ValueError):
            check_witness.check(3, self.a)

    def test_greedy_identity_not_counterexample(self):
        self.assertEqual(sum(Fraction(a, 2**a) for a in [3,6,8]), Fraction(1,2))
        with self.assertRaisesRegex(ValueError, 'not a counterexample'):
            check_witness.check(2, [3,6,8])

    def test_source_list_matches_json(self):
        source = (ROOT / 'DyadicBound.lean').read_text()
        literal = re.search(r'def exponents : List ℕ := (\[[^\]]+\])', source).group(1)
        self.assertEqual(json.loads(literal), self.a)

class AuditTests(unittest.TestCase):
    def test_inventory(self):
        cfg = json.loads((ROOT / 'verification-config.json').read_text())
        verify.guard((ROOT / 'DyadicBound.lean').read_text(), cfg['imports'], cfg['theorems'])

    def test_standard_axioms(self):
        self.assertEqual(verify.audit("'T' depends on axioms: [propext, Classical.choice, Quot.sound]", ['T'])['T'],
                         ['propext', 'Classical.choice', 'Quot.sound'])

    def test_axiom_free(self):
        self.assertEqual(verify.audit("'T' does not depend on any axioms", ['T']), {'T': []})

    def test_missing_audit(self):
        with self.assertRaises(ValueError):
            verify.audit('', ['T'])

    def test_duplicate_audit(self):
        with self.assertRaises(ValueError):
            verify.audit("'T' does not depend on any axioms\n" * 2, ['T'])

    def test_unapproved_axioms(self):
        for axiom in ['sorryAx', 'forged', 'Lean.ofReduceBool']:
            with self.subTest(axiom=axiom), self.assertRaises(ValueError):
                verify.audit("'T' depends on axioms: [" + axiom + "]", ['T'])

    def test_bad_source(self):
        for src in ['theorem T : False := by sorry', 'axiom forged : False', 'unsafe def x := 1']:
            with self.subTest(src=src), self.assertRaises(ValueError):
                verify.guard(src, [], ['T'])

if __name__ == '__main__':
    unittest.main()
