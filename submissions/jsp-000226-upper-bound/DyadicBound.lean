/-
SPDX-License-Identifier: Apache-2.0
A concrete counterexample to the upper bound in Conjecture 3.7 of
Tengely, Ulas and Zygadlo, On a Diophantine equation of Erdos and Graham (2020).
This addresses its stated universal bound, not a greedy-only variant and not
all open questions in Erdos 261. Discovery priority requires literature review.
-/
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace DyadicBound

def exponents : List ℕ := [3, 6, 9, 10, 12, 14, 18, 19, 21, 22, 24, 26, 29, 30, 33, 34, 35, 36, 39, 42, 43, 45, 47, 48, 49, 50, 52, 53, 58, 59, 61, 65, 66, 68, 69, 71, 75, 80, 81, 82, 83, 84, 85, 87, 92, 93, 95, 96, 97, 100, 101, 107, 108, 109, 112, 116, 120, 121, 124, 126, 127, 128, 129, 132, 135, 138, 140, 141, 142, 147, 148, 150, 151, 152, 154, 155, 157, 158, 160, 163, 164, 167, 172, 173, 175, 177, 179, 181, 182, 183, 184, 185, 187, 189, 194, 197, 200, 201, 203, 204, 206, 207, 209, 211, 213, 217, 221, 222, 224, 226, 229, 234, 235, 243, 248, 249, 251, 253, 254, 259, 260, 261, 262, 263, 264, 269, 272, 274, 275, 276, 277, 278, 279, 281, 283, 288, 289, 290, 291, 295, 298, 302, 303, 306, 308, 309, 314, 315, 316, 317, 319, 320, 321, 324, 326, 332, 333, 334, 335, 337, 338, 343, 344, 345, 347, 348, 349, 352, 356, 360, 363, 364, 365, 366, 368, 369, 370, 371, 373, 377, 379, 381, 387, 390, 392]

def weightedSum (s : List ℕ) : ℚ :=
  (s.map (fun (a : ℕ) => (a : ℚ) / (2 : ℚ) ^ a)).sum

/-- Universal upper bound exactly as stated in TUZ Conjecture 3.7.
For an increasing nonempty list, bounding every entry is equivalent to
bounding its largest entry. -/
def UpperBoundConjecture : Prop :=
  ∀ (n : ℕ) (s : List ℕ), 0 < n → 2 ≤ s.length →
    s.Pairwise (· < ·) → (∀ a ∈ s, 0 < a) →
    weightedSum s = (n : ℚ) / 2 ^ n →
    ∀ a ∈ s, a ≤ 2 * (n + s.length)

theorem length_eq : exponents.length = 185 := by decide +kernel

theorem strictly_increasing : exponents.Pairwise (· < ·) := by decide +kernel

theorem positive : ∀ a ∈ exponents, 0 < a := by decide +kernel

theorem bounded : ∀ a ∈ exponents, a ≤ 392 := by decide +kernel

theorem last_eq : exponents.getLast? = some 392 := by decide +kernel

theorem last_mem : 392 ∈ exponents := by decide +kernel

/-- A second exact certificate obtained by clearing the common denominator. -/
theorem scaled_integer_identity :
    (exponents.map (fun a => a * 2 ^ (392 - a))).sum = 2 ^ 391 := by
  decide +kernel

/-- Direct rational calculation, independently of the scaled certificate. -/
theorem rational_identity : weightedSum exponents = (2 : ℚ) / 2 ^ 2 := by
  decide +kernel

theorem bound_violation : 2 * (2 + exponents.length) < 392 := by
  rw [length_eq]
  norm_num

/-- All hypotheses hold at n=2, k=185, but 392 > 374. -/
theorem certified_counterexample :
    2 ≤ exponents.length ∧ exponents.Pairwise (· < ·) ∧
    (∀ a ∈ exponents, 0 < a) ∧
    weightedSum exponents = (2 : ℚ) / 2 ^ 2 ∧
    exponents.getLast? = some 392 ∧ 2 * (2 + exponents.length) < 392 := by
  exact ⟨by rw [length_eq]; omega, strictly_increasing, positive,
    rational_identity, last_eq, bound_violation⟩

/-- Negation of the complete universally quantified upper-bound claim. -/
theorem conjecture_false : ¬ UpperBoundConjecture := by
  intro h
  have hbound := h 2 exponents (by omega) (by rw [length_eq]; omega)
    strictly_increasing positive rational_identity 392 last_mem
  exact (Nat.not_le_of_lt bound_violation) hbound

#print axioms length_eq
#print axioms strictly_increasing
#print axioms positive
#print axioms bounded
#print axioms last_eq
#print axioms last_mem
#print axioms scaled_integer_identity
#print axioms rational_identity
#print axioms bound_violation
#print axioms certified_counterexample
#print axioms conjecture_false
end DyadicBound
