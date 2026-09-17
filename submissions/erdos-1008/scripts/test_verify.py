"""Bounded exact cross-checks; the universal mathematical proof is in Lean."""
from fractions import Fraction
from itertools import combinations
from math import comb
from pathlib import Path
import json
import unittest
from verify import audit, guard

ROOT = Path(__file__).resolve().parents[1]


def has_rectangle(columns: list[int]) -> bool:
    """C4 in a simple bipartite graph: two columns have two common rows."""
    return any((a & b).bit_count() >= 2 for a, b in combinations(columns, 2))


def graph_columns(s: int, t: int, mask: int) -> list[int]:
    return [(mask >> (s*j)) & ((1 << s)-1) for j in range(t)]


def construction(s: int, t: int) -> list[int]:
    if s < 1 or t < comb(s, 2):
        raise ValueError('Outside the stated sharpness range')
    return [(1 << a) | (1 << b) for a, b in combinations(range(s), 2)] + [1]*(t-comb(s, 2))


def exact_small_max(s: int, t: int) -> tuple[int, int]:
    maximum = 0
    checked = 0
    for mask in range(1 << (s*t)):
        columns = graph_columns(s, t, mask)
        if has_rectangle(columns):
            continue
        checked += 1
        e = mask.bit_count()
        if e > t+comb(s, 2):
            raise AssertionError((s, t, mask))
        maximum = max(maximum, e)
    return maximum, checked


class AuditTests(unittest.TestCase):
    def test_actual_inventory_and_imports(self):
        c = json.loads((ROOT/'verification-config.json').read_text())
        s = (ROOT/'Erdos1008.lean').read_text()
        guard(s, c['imports'], c['theorems'])
        self.assertEqual(len(c['theorems']), 26)
        for before, after in c['mutations'].values():
            self.assertEqual(s.count(before), 1)
            self.assertNotEqual(before, after)

    def test_axiom_allowlist(self):
        self.assertEqual(audit("'x' depends on axioms: [propext,\n Classical.choice, Quot.sound]", ['x']),
                         {'x': ['propext', 'Classical.choice', 'Quot.sound']})
        self.assertEqual(audit("'x' does not depend on any axioms", ['x']), {'x': []})

    def test_incomplete_or_unapproved_audits(self):
        for s in ['', "'x' does not depend on any axioms\n"*2,
                  "'x' depends on axioms: [sorryAx]", "'x' depends on axioms: [forged]",
                  "'x' depends on axioms: [Lean.ofReduceBool]"]:
            with self.subTest(s=s), self.assertRaises(ValueError):
                audit(s, ['x'])

    def test_shortcuts_are_rejected(self):
        s = 'import Mathlib.Tactic\ntheorem good : True := by trivial\n#print axioms good\n'
        guard(s, ['Mathlib.Tactic'], ['good'])
        for token in ['sorry', 'admit', 'native_decide', 'unsafe', 'skipKernelTC', 'ofReduceBool',
                      '\naxiom forged : False']:
            with self.subTest(token=token), self.assertRaises(ValueError):
                guard(s+token, ['Mathlib.Tactic'], ['good'])

    def test_literal_graph_and_original_quantifiers(self):
        s = (ROOT/'Erdos1008.lean').read_text()
        self.assertIn('cycleGraph 4 ⊑ incidence F', s)
        self.assertIn('(cycleGraph 4).Free H', s)
        self.assertIn('H.edgeSet.ncard', s)
        self.assertIn('(hs : 0 < s) (ht : s.choose 2 ≤ t)', s)
        tail = s.split('theorem no_uniform_three_quarters', 1)[1].split('#print', 1)[0]
        self.assertIn('¬ ∃ c > (0 : ℝ)', tail)
        self.assertIn('∀ (V : Type) [Fintype V] (G : SimpleGraph V)', tail)
        self.assertIn('(3/4 : ℝ)', tail)
        self.assertNotIn('PairUnique F', tail)


class GraphTests(unittest.TestCase):
    def test_all_small_graphs(self):
        for s, t in [(0,0),(0,4),(1,0),(1,6),(2,0),(2,1),(2,5),(3,2),(3,3),(3,4),(3,6),(4,4)]:
            with self.subTest(s=s,t=t):
                maximum, checked = exact_small_max(s,t)
                self.assertGreater(checked, 0)
                if s >= 1 and t >= comb(s,2):
                    self.assertEqual(maximum,t+comb(s,2))

    def test_rectangle_matches_literal_four_edges(self):
        s,t=3,3
        for mask in range(1 << (s*t)):
            columns=graph_columns(s,t,mask)
            edges={(a,b) for a in range(s) for b in range(t) if mask & (1 << (s*b+a))}
            direct=any(all(x in edges for x in [(a,b),(a,c),(d,b),(d,c)])
                       for a,d in combinations(range(s),2) for b,c in combinations(range(t),2))
            self.assertEqual(direct,has_rectangle(columns))
            self.assertEqual(len(edges),sum(c.bit_count() for c in columns))

    def test_attaining_construction(self):
        for s in range(1,31):
            for extra in [0,1,2,17]:
                t=comb(s,2)+extra
                columns=construction(s,t)
                self.assertEqual(len(columns),t)
                self.assertFalse(has_rectangle(columns))
                self.assertEqual(sum(c.bit_count() for c in columns),t+comb(s,2))
                self.assertTrue(all(0<c<(1 << s) for c in columns))

    def test_numeric_example(self):
        columns=construction(10,100)
        self.assertFalse(has_rectangle(columns))
        self.assertEqual(sum(c.bit_count() for c in columns),145)
        self.assertEqual(10*100,1000)

    def test_folkman_family(self):
        for n in range(1,25):
            columns=construction(n,n*n)
            self.assertFalse(has_rectangle(columns))
            self.assertEqual(sum(c.bit_count() for c in columns),n*n+comb(n,2))
            self.assertEqual(n*(n*n),n**3)

    def test_sharpness_hypotheses_are_needed(self):
        self.assertEqual(exact_small_max(2,0)[0],0)
        self.assertEqual(0+comb(2,2),1)
        self.assertEqual(exact_small_max(0,4)[0],0)
        with self.assertRaises(ValueError):construction(2,0)
        with self.assertRaises(ValueError):construction(0,4)
        self.assertEqual(construction(1,0),[])

    def test_real_mathematical_negative_controls(self):
        self.assertGreater(1,comb(1,2))
        columns=[1]
        self.assertNotEqual(sum(c.bit_count() for c in columns),2)
        self.assertFalse(has_rectangle(construction(2,2)))
        self.assertTrue(has_rectangle([3,3]))
        self.assertNotEqual(2**8,2**9)
        self.assertEqual((2**12)**3,(2**9)**4)

    def test_asymptotic_scaling_with_exact_rationals(self):
        for c in [Fraction(1),Fraction(1,10),Fraction(1,1000),Fraction(3,7)]:
            k=int(2/c)+2
            n=k**4
            host_edges=n**3
            max_free=n*n+comb(n,2)
            self.assertGreater(c*k,2)
            self.assertEqual(host_edges**3,(k**9)**4)
            self.assertLess(Fraction(max_free),c*k**9)


if __name__ == '__main__':
    unittest.main()
