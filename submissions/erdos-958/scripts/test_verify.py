"""Fail-closed audit tests and bounded cross-checks; these are not the universal proof."""
from collections import Counter
import json
import math
from pathlib import Path
import unittest
import verify

ROOT = Path(__file__).resolve().parents[1]

class AuditTests(unittest.TestCase):
    def test_actual_inventory_and_imports(self):
        cfg = json.loads((ROOT/'verification-config.json').read_text())
        self.assertEqual(len(cfg['theorems']), 41)
        verify.guard((ROOT/'Erdos958.lean').read_text(), cfg['imports'], cfg['theorems'])

    def test_standard_axioms(self):
        report = verify.audit("'T' depends on axioms: [propext,\n Classical.choice, Quot.sound]", ['T'])
        self.assertEqual(set(report['T']), verify.ALLOWED)

    def test_axiom_free(self):
        self.assertEqual(verify.audit("'T' does not depend on any axioms", ['T']), {'T': []})

    def test_missing_or_duplicate(self):
        for report in ['', "'T' does not depend on any axioms\n"*2]:
            with self.subTest(report=report), self.assertRaises(ValueError):
                verify.audit(report, ['T'])

    def test_unapproved_axioms(self):
        for axiom in ['sorryAx', 'forged', 'Lean.ofReduceBool']:
            with self.subTest(axiom=axiom), self.assertRaises(ValueError):
                verify.audit("'T' depends on axioms: ["+axiom+"]", ['T'])

    def test_source_shortcuts_rejected(self):
        for word in ['sorry', 'admit', 'native_decide', 'unsafe', 'skipKernelTC', 'ofReduceBool']:
            with self.subTest(word=word), self.assertRaises(ValueError):
                verify.guard('import Mathlib.Tactic\n'+word, ['Mathlib.Tactic'], [])

    def test_mutations_are_unique_and_current(self):
        source = (ROOT/'Erdos958.lean').read_text()
        cfg = json.loads((ROOT/'verification-config.json').read_text())
        for name, (before, after) in cfg['mutations'].items():
            with self.subTest(name=name):
                self.assertEqual(source.count(before), 1)
                self.assertNotEqual(before, after)

    def test_literal_geometry_and_full_quantifiers(self):
        source = (ROOT/'Erdos958.lean').read_text()
        self.assertIn('EuclideanSpace ℝ (Fin 2)', source)
        self.assertIn('theorem finite_counterexamples (n : ℕ) (hn : 4 ≤ n)', source)
        self.assertIn('theorem original_classification_false', source)
        self.assertIn('¬ Collinear ℝ (A : Set Plane)', source)
        self.assertIn('¬ Cospherical (A : Set Plane)', source)
        self.assertIn('A.offDiag.image', source)
        self.assertIn('(A.offDiag.filter (fun p => dist p.1 p.2 = d)).card / 2', source)
        self.assertNotIn('axiom ', source)

class CombinatorialCrossChecks(unittest.TestCase):
    def test_every_label_and_all_orientations(self):
        for m in range(1, 65):
            pairs = [(i,j) for i in range(m+1) for j in range(i+1,m+1)]
            labels = Counter(0 if i == 0 else j-i for i,j in pairs)
            self.assertEqual(labels, {k: m-k for k in range(m)})
            oriented = {(i,j) for i,j in pairs} | {(j,i) for i,j in pairs}
            self.assertEqual(oriented, {(i,j) for i in range(m+1) for j in range(m+1) if i != j})
            self.assertEqual(len(oriented), 2*len(pairs))
            self.assertEqual(sum(labels.values()), m*(m+1)//2)

    def test_label_inverse_bijection(self):
        for m in range(1,40):
            for k in range(m):
                encoded = [(0,i+1) if k == 0 else (i+1,i+1+k) for i in range(m-k)]
                expected = [(i,j) for i in range(m+1) for j in range(i+1,m+1)
                            if (0 if i == 0 else j-i) == k]
                self.assertEqual(encoded, expected)
                self.assertEqual(len(set(encoded)), m-k)

    def test_duplicate_points_fail_injectivity(self):
        for m in range(3,20):
            wrong = [0] + [1]*m
            self.assertLess(len(set(wrong)), len(wrong))

    def test_numeric_metric_sanity_only(self):
        # Floating-point checks are diagnostics only; all exact statements are proved in Lean.
        for m in range(3,25):
            theta = math.pi/(3*(m+1))
            pts = [(0.0,0.0)] + [(math.cos(j*theta),math.sin(j*theta)) for j in range(m)]
            sq = [1.0] + [2-2*math.cos(k*theta) for k in range(1,m)]
            self.assertTrue(all(0 < value < 1 for value in sq[1:]))
            self.assertTrue(all(a < b for a,b in zip(sq[1:],sq[2:])))
            for i in range(m+1):
                for j in range(i+1,m+1):
                    actual = sum((x-y)**2 for x,y in zip(pts[i],pts[j]))
                    self.assertAlmostEqual(actual,sq[0 if i == 0 else j-i],places=12)

if __name__ == '__main__':
    unittest.main()
