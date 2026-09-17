"""Proof-audit regression tests and independent, bounded integer cross-checks.

The finite computations are diagnostics, not substitutes for the universal Lean proof.
"""
from functools import lru_cache
from math import isqrt
from pathlib import Path
import json
import random
import unittest

from verify import audit, guard

ROOT = Path(__file__).resolve().parents[1]


def triples(n: int) -> list[tuple[int, int, int]]:
    r = isqrt(n)
    return [(2*k, 2*k+1, 2*k*(2*k+1))
            for k in range(isqrt(r)//2+1, (r-1)//2+1)]


def bound(n: int) -> int:
    r = isqrt(n)
    return max(0, max(0, r-1)//2-isqrt(r)//2)


def local_obstructions(n: int) -> list[tuple[int, int, int]]:
    return [(a, a+1, a*(a+1)) for a in range(2, isqrt(n)+1) if a*(a+1) <= n]


def avoids_adjacent_product(b: set[int]) -> bool:
    return all(not (a+1 in b and a*(a+1) in b) for a in b if a >= 2)


def minimum_local_omissions(n: int) -> int:
    """Exact minimum hitting-set size, enumerating only relevant obstruction edges."""
    edges = local_obstructions(n)
    coverage: dict[int, int] = {}
    for i, edge in enumerate(edges):
        for v in edge:
            coverage[v] = coverage.get(v, 0) | (1 << i)

    @lru_cache(None)
    def solve(mask: int) -> int:
        if not mask:
            return 0
        i = (mask & -mask).bit_length()-1
        return min(1 + solve(mask & ~coverage[v]) for v in edges[i])

    return solve((1 << len(edges))-1)


def distinct_blocks(values: list[int]) -> bool:
    seen: set[int] = set()
    for i in range(len(values)):
        p = 1
        for v in values[i:]:
            p *= v
            if p in seen:
                return False
            seen.add(p)
    return True


class AuditTests(unittest.TestCase):
    def test_standard_axioms(self):
        self.assertEqual(audit("'x' depends on axioms: [propext,\n Classical.choice, Quot.sound]", ['x']),
                         {'x': ['propext', 'Classical.choice', 'Quot.sound']})
        self.assertEqual(audit("'x' does not depend on any axioms", ['x']), {'x': []})

    def test_missing_duplicate_and_extra_assumptions(self):
        for text in ['', "'x' does not depend on any axioms\n" * 2,
                     "'x' depends on axioms: [sorryAx]", "'x' depends on axioms: [forged]",
                     "'x' depends on axioms: [Lean.ofReduceBool]"]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                audit(text, ['x'])

    def test_source_shortcuts(self):
        s = 'import Mathlib.Tactic\ntheorem foo : True := by trivial\n#print axioms foo\n'
        guard(s, ['Mathlib.Tactic'], ['foo'])
        for token in ['sorry', 'admit', 'native_decide', 'unsafe', 'skipKernelTC', 'ofReduceBool',
                      '\naxiom forged : False']:
            with self.subTest(token=token), self.assertRaises(ValueError):
                guard(s+token, ['Mathlib.Tactic'], ['foo'])

    def test_actual_inventory_and_mutations(self):
        cfg = json.loads((ROOT/'verification-config.json').read_text())
        source = (ROOT/'JSP346.lean').read_text()
        guard(source, cfg['imports'], cfg['theorems'])
        self.assertEqual(len(cfg['theorems']), 17)
        for before, after in cfg['mutations'].values():
            self.assertEqual(source.count(before), 1)
            self.assertNotEqual(before, after)

    def test_literal_scope(self):
        s = (ROOT/'JSP346.lean').read_text()
        self.assertIn('∏ i ∈ Finset.Icc p.1 p.2, d i', s)
        self.assertIn('(Finset.Icc 1 N).filter (fun n => n ∉ B)', s)
        self.assertNotIn('HasDensity', s)
        final = s.split('theorem product_distinct_half_root', 1)[1].split('#print', 1)[0]
        self.assertIn('∀ᶠ N : ℕ in atTop', final)
        self.assertIn('(hprod : DistinctBlockProducts d)', final)
        self.assertIn('((1 : ℝ)/2 - ε)', final)


class IntegerCrossChecks(unittest.TestCase):
    def test_all_selected_triples_and_small_cutoffs(self):
        for n in list(range(4097)) + [10**6, 10**8]:
            r = isqrt(n)
            ts = triples(n)
            self.assertEqual(len(ts), bound(n))
            used: set[int] = set()
            for a, b, c in ts:
                self.assertEqual(b, a+1)
                self.assertEqual(c, a*b)
                self.assertTrue(1 <= a < b <= r < c <= n)
                self.assertFalse(used.intersection([a,b,c]))
                used.update([a,b,c])

    def test_exact_small_relaxed_minima(self):
        for n in list(range(81)) + [100, 144, 200, 256, 400]:
            e = minimum_local_omissions(n)
            self.assertGreaterEqual(e, bound(n))
            r = isqrt(n)
            self.assertLessEqual(r, 2*e+isqrt(r)+2)
        self.assertEqual(minimum_local_omissions(6), 1)
        self.assertGreater(bound(400), 0)

    def test_actual_hole_choices(self):
        rng = random.Random(346421)
        for n in [36, 100, 400, 4096]:
            for _ in range(8):
                b = set(range(1,n+1))
                for edge in local_obstructions(n):
                    if all(v in b for v in edge):
                        b.remove(rng.choice(edge))
                self.assertTrue(avoids_adjacent_product(b))
                holes = [next(v for v in edge if v not in b) for edge in triples(n)]
                self.assertEqual(len(holes), len(set(holes)))
                self.assertGreaterEqual(n-len(b), len(holes))

    def test_cutoff_is_needed(self):
        # Without the lower cutoff, a large product can equal another pair endpoint.
        self.assertFalse(set((2,3,6)).isdisjoint((6,7,42)))

    def test_coefficient_one_is_not_a_local_consequence(self):
        n = 400
        r = isqrt(n)
        b = {a for a in range(1,r+1) if a % 2 == 1} | set(range(r+2,n+1))
        self.assertTrue(avoids_adjacent_product(b))
        e = n-len(b)
        self.assertGreater(r, e+isqrt(r)+2)
        self.assertLessEqual(r, 2*e+isqrt(r)+2)

    def test_local_condition_is_weaker_than_full_blocks(self):
        b = {2,4,8}
        self.assertTrue(avoids_adjacent_product(b))
        self.assertFalse(distinct_blocks(sorted(b)))
        self.assertTrue(distinct_blocks([2,3,5,7,11,13,17,19,23,29]))
        self.assertTrue(distinct_blocks([2**(2**i) for i in range(8)]))
        self.assertFalse(distinct_blocks(list(range(2,11))))

    def test_exact_displayed_example(self):
        self.assertEqual(bound(10**8), 4949)
        self.assertEqual(bound(10**12), 499499)
        self.assertEqual(bound(0), 0)
        self.assertEqual(bound(1), 0)


if __name__ == '__main__':
    unittest.main()
