#!/usr/bin/env python3
"""Independent exact-arithmetic checks; no floating-point arithmetic or Lean imports."""
from __future__ import annotations
from fractions import Fraction
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def check(n: int, exponents: list[int]) -> dict:
    if type(n) is not int or n <= 0 or len(exponents) < 2:
        raise ValueError('Positive n and at least two summands are required')
    if any(type(a) is not int or a <= 0 for a in exponents):
        raise ValueError('All exponents must be positive integers')
    if any(a >= b for a, b in zip(exponents, exponents[1:])):
        raise ValueError('The exponents must be strictly increasing')
    maximum = exponents[-1]
    if maximum < n:
        raise ValueError('The common denominator must include the left side')
    rational = sum((Fraction(a, 2**a) for a in exponents), Fraction(0))
    scaled = sum(a * 2**(maximum-a) for a in exponents)
    expected = n * 2**(maximum-n)
    if rational != Fraction(n, 2**n) or scaled != expected:
        raise ValueError('The exact identity is false')
    bound = 2 * (n + len(exponents))
    if maximum <= bound:
        raise ValueError('This identity is not a counterexample to the proposed bound')
    return {'n': n, 'k': len(exponents), 'first_exponent': exponents[0],
            'last_exponent': maximum, 'upper_bound': bound, 'excess': maximum-bound,
            'rational_sum': str(rational), 'scaled_sum': str(scaled),
            'scaled_expected': str(expected), 'status': 'EXACT_ARITHMETIC_PASS'}

if __name__ == '__main__':
    witness = json.loads((ROOT / 'witness.json').read_text())
    print(json.dumps(check(witness['n'], witness['terms']), indent=2))
