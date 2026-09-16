/- SPDX-License-Identifier: Apache-2.0
JSP-000226 / Erdos 261(i): infinitude and the sharp fixed-term extremum.
The upper bound is TUZ (2020), Theorem 2.1(i); its equality case is proved here.
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


def dyadicWeight (n : ℕ) : ℚ := (n : ℚ) / 2 ^ n

def OrderedDecomposition (n k : ℕ) : Prop :=
  ∃ a : Fin k → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧
    dyadicWeight n = ∑ i, dyadicWeight (a i)

theorem dyadicWeight_pos (n : ℕ) (hn : 0 < n) : 0 < dyadicWeight n := by
  unfold dyadicWeight
  positivity

theorem dyadicWeight_succ_le (n : ℕ) (hn : 1 ≤ n) :
    dyadicWeight (n + 1) ≤ dyadicWeight n := by
  unfold dyadicWeight
  rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
  push_cast
  calc
    ((n : ℚ) + 1) * 2 ^ n ≤ (2 * n) * 2 ^ n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show n + 1 ≤ 2 * n by omega))
        (by positivity)
    _ = n * (2 ^ n * 2) := by ring

theorem dyadicWeight_antitone {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    dyadicWeight b ≤ dyadicWeight a := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => exact (dyadicWeight_succ_le b (by omega)).trans ih

theorem dyadicWeight_strict {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) :
    dyadicWeight b < dyadicWeight a := by
  have hstep : dyadicWeight (a + 1) < dyadicWeight a := by
    unfold dyadicWeight
    rw [div_lt_div_iff₀ (by positivity) (by positivity), pow_succ]
    push_cast
    calc
      ((a : ℚ) + 1) * 2 ^ a < (2 * a) * 2 ^ a :=
        mul_lt_mul_of_pos_right (by exact_mod_cast (show a + 1 < 2 * a by omega))
          (by positivity)
      _ = a * (2 ^ a * 2) := by ring
  exact lt_of_le_of_lt (dyadicWeight_antitone (by omega) (by omega)) hstep

/-- No term can be at or before the left-hand exponent. Repetition is not used here. -/
theorem exponent_after_start {n k : ℕ} (hk : 2 ≤ k) (a : Fin k → ℕ)
    (hpos : ∀ i, 0 < a i) (heq : dyadicWeight n = ∑ i, dyadicWeight (a i))
    (i : Fin k) : n < a i := by
  let : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  obtain ⟨j, hji⟩ := exists_ne i
  have hterm : dyadicWeight (a i) < ∑ t, dyadicWeight (a t) :=
    Finset.single_lt_sum hji (Finset.mem_univ i) (Finset.mem_univ j)
      (dyadicWeight_pos _ (hpos j)) (fun t _ _ => (dyadicWeight_pos _ (hpos t)).le)
  by_contra h
  have hle := dyadicWeight_antitone (hpos i) (show a i ≤ n by omega)
  rw [← heq] at hterm
  exact (not_lt_of_ge hle) hterm

/-- Strictly ordered exponents dominate the consecutive comparison block. -/
theorem ordered_exponent_bound {n k : ℕ} (hk : 2 ≤ k) (a : Fin k → ℕ)
    (hmono : StrictMono a) (hpos : ∀ i, 0 < a i)
    (heq : dyadicWeight n = ∑ i, dyadicWeight (a i)) :
    ∀ i : Fin k, n + i.val + 1 ≤ a i := by
  have aux : ∀ j : ℕ, ∀ hj : j < k, n + j + 1 ≤ a ⟨j, hj⟩ := by
    intro j
    induction j with
    | zero =>
      intro hj
      have := exponent_after_start hk a hpos heq ⟨0, hj⟩
      omega
    | succ j ih =>
      intro hj
      have hj' : j < k := by omega
      have hprev := ih hj'
      have hlt := hmono (show (⟨j, hj'⟩ : Fin k) < ⟨j + 1, hj⟩ from Nat.lt_succ_self j)
      omega
  intro i
  exact aux i.val i.isLt

/-- The TUZ sharp upper bound, with all n, k and exponents universally quantified. -/
theorem sharp_start_bound {n k : ℕ} (hk : 2 ≤ k) (h : OrderedDecomposition n k) :
    n ≤ family k := by
  obtain ⟨a, hmono, hpos, heq⟩ := h
  have ha := ordered_exponent_bound hk a hmono hpos heq
  have hsum : dyadicWeight n ≤ ∑ i : Fin k, dyadicWeight (n + i.val + 1) := by
    rw [heq]
    exact Finset.sum_le_sum (fun i _ => dyadicWeight_antitone (by omega) (ha i))
  change (n : ℚ) / 2 ^ n ≤ ∑ i : Fin k, ((n + i.val + 1 : ℕ) : ℚ) / 2 ^ (n + i.val + 1) at hsum
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((n + i + 1 : ℕ) : ℚ) / 2 ^ (n + i + 1)), block_sum] at hsum
  have hscaled := mul_le_mul_of_nonneg_right hsum
    (show (0 : ℚ) ≤ 2 ^ n * 2 ^ k by positivity)
  have hl : ((n : ℚ) / 2 ^ n) * (2 ^ n * 2 ^ k) = n * 2 ^ k := by
    field_simp
  have hr : (((n : ℚ) + 2) / 2 ^ n - ((n : ℚ) + k + 2) / 2 ^ (n + k)) *
      (2 ^ n * 2 ^ k) = (n + 2) * 2 ^ k - (n + k + 2) := by
    rw [pow_add]
    field_simp
  rw [hl, hr] at hscaled
  have hq : (n : ℚ) + k + 2 ≤ (2 : ℚ) ^ (k + 1) := by
    rw [pow_succ]
    nlinarith
  have hn : n + k + 2 ≤ 2 ^ (k + 1) := by exact_mod_cast hq
  have hb := family_balance k
  omega

theorem family_ordered (k : ℕ) : OrderedDecomposition (family k) k := by
  refine ⟨fun i => family k + i.val + 1, ?_, ?_, ?_⟩
  · intro i j hij
    dsimp
    exact Nat.add_lt_add_right (Nat.add_lt_add_left hij _) _
  · intro i
    dsimp
    omega
  · unfold dyadicWeight
    exact (family_identity k).trans
      (Fin.sum_univ_eq_sum_range
        (fun i : ℕ => ((family k + i + 1 : ℕ) : ℚ) / 2 ^ (family k + i + 1)) k).symm

/-- Exact maximum possible starting exponent at each fixed number of summands. -/
theorem maximal_start (k : ℕ) (hk : 2 ≤ k) :
    IsGreatest {n : ℕ | 0 < n ∧ OrderedDecomposition n k} (family k) := by
  refine ⟨⟨by have := family_bound k; omega, family_ordered k⟩, ?_⟩
  intro n hn
  exact sharp_start_bound hk hn.2

/-- Equality at the maximum forces the unique consecutive block of exponents. -/
theorem maximal_representation_unique (k : ℕ) (hk : 2 ≤ k) (a : Fin k → ℕ)
    (hmono : StrictMono a) (hpos : ∀ i, 0 < a i)
    (heq : dyadicWeight (family k) = ∑ i, dyadicWeight (a i)) :
    ∀ i, a i = family k + i.val + 1 := by
  have ha := ordered_exponent_bound hk a hmono hpos heq
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      dyadicWeight (a i) ≤ dyadicWeight (family k + i.val + 1) := by
    intro i _
    exact dyadicWeight_antitone (by omega) (ha i)
  have hsum : (∑ i, dyadicWeight (a i)) =
      ∑ i : Fin k, dyadicWeight (family k + i.val + 1) := by
    rw [← heq]
    unfold dyadicWeight
    exact (family_identity k).trans
      (Fin.sum_univ_eq_sum_range
        (fun i : ℕ => ((family k + i + 1 : ℕ) : ℚ) / 2 ^ (family k + i + 1)) k).symm
  have hterms := (Finset.sum_eq_sum_iff_of_le hle).mp hsum
  intro i
  have hbase := family_bound k
  by_contra hne
  have hlt : family k + i.val + 1 < a i := by have := ha i; omega
  have hstrict := dyadicWeight_strict (by omega : 2 ≤ family k + i.val + 1) hlt
  rw [hterms i (Finset.mem_univ i)] at hstrict
  exact lt_irrefl _ hstrict


#print axioms block_sum
#print axioms family_bound
#print axioms family_balance
#print axioms family_identity
#print axioms family_representable
#print axioms infinitely_many_representable
#print axioms dyadicWeight_pos
#print axioms dyadicWeight_succ_le
#print axioms dyadicWeight_antitone
#print axioms dyadicWeight_strict
#print axioms exponent_after_start
#print axioms ordered_exponent_bound
#print axioms sharp_start_bound
#print axioms family_ordered
#print axioms maximal_start
#print axioms maximal_representation_unique
end JustinSunPrize.JSP000226
