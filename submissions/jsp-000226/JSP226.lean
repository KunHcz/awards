/- SPDX-License-Identifier: Apache-2.0
JSP-000226 / Erdos 261(i): the Borwein--Loring infinite family.
The identity is classical, not a new mathematical discovery.
This file does not claim all n or continuum-many rational representations.
-/
import Mathlib.Tactic

namespace JustinSunPrize.JSP000226
open scoped BigOperators

/-- Distinct positive denominators, with at least two terms. -/
def Representable (n : ℕ) : Prop :=
  ∃ t : ℕ, 2 ≤ t ∧ ∃ a : Fin t → ℕ, Function.Injective a ∧
    (∀ i, 1 ≤ a i) ∧ (n : ℚ) / 2 ^ n = ∑ i, (a i : ℚ) / 2 ^ a i

/-- Telescoping formula for any finite consecutive block. -/
theorem block_sum (n m : ℕ) :
    (∑ i ∈ Finset.range m, ((n + i + 1 : ℕ) : ℚ) / 2 ^ (n + i + 1)) =
      ((n : ℚ) + 2) / 2 ^ n - ((n : ℚ) + m + 2) / 2 ^ (n + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hpow : (2 : ℚ) ^ (n + (m + 1)) = 2 ^ (n + m) * 2 := by
      rw [show n + (m + 1) = (n + m) + 1 by omega, pow_succ]
    push_cast
    rw [show n + m + 1 = n + (m + 1) by omega, hpow]
    field_simp
    ring

/-- A natural-valued parametrization, including the harmless m=0,1 cases. -/
def family (m : ℕ) : ℕ := 2 ^ (m + 1) - m - 2

theorem family_bound (m : ℕ) : m ≤ family m := by
  have h : m < 2 ^ m := Nat.lt_two_pow_self
  have hp : 2 ^ (m + 1) = 2 ^ m * 2 := by rw [pow_succ]
  unfold family
  omega

theorem family_balance (m : ℕ) : family m + m + 2 = 2 ^ (m + 1) := by
  have h : m < 2 ^ m := Nat.lt_two_pow_self
  have hp : 2 ^ (m + 1) = 2 ^ m * 2 := by rw [pow_succ]
  unfold family
  omega

/-- The exact equality of rational numbers, for arbitrarily large blocks. -/
theorem family_identity (m : ℕ) :
    (family m : ℚ) / 2 ^ family m =
      ∑ i ∈ Finset.range m, ((family m + i + 1 : ℕ) : ℚ) / 2 ^ (family m + i + 1) := by
  rw [block_sum]
  have hb : (family m : ℚ) + m + 2 = (2 : ℚ) ^ (m + 1) := by
    exact_mod_cast family_balance m
  rw [hb, pow_add, pow_succ]
  field_simp
  ring

theorem family_representable (m : ℕ) (hm : 2 ≤ m) : Representable (family m) := by
  refine ⟨m, hm, fun i => family m + i.val + 1, ?_, ?_, ?_⟩
  · intro i j h
    apply Fin.ext
    dsimp at h
    omega
  · intro i
    dsimp
    omega
  · change (family m : ℚ) / 2 ^ family m =
      ∑ i : Fin m, ((family m + i.val + 1 : ℕ) : ℚ) / 2 ^ (family m + i.val + 1)
    exact (family_identity m).trans
      (Fin.sum_univ_eq_sum_range
        (fun i : ℕ => ((family m + i + 1 : ℕ) : ℚ) / 2 ^ (family m + i + 1)) m).symm

/-- Complete affirmative answer to the infinitude question, not the all-n question. -/
theorem infinitely_many_representable :
    {n : ℕ | 0 < n ∧ Representable n}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro b
  refine ⟨family (b + 2), ?_, ?_⟩
  · exact ⟨lt_of_lt_of_le (by omega) (family_bound (b + 2)),
      family_representable (b + 2) (by omega)⟩
  · exact lt_of_lt_of_le (by omega) (family_bound (b + 2))

#print axioms block_sum
#print axioms family_bound
#print axioms family_balance
#print axioms family_identity
#print axioms family_representable
#print axioms infinitely_many_representable
end JustinSunPrize.JSP000226
