/- SPDX-License-Identifier: Apache-2.0
JSP-000346 / Erdős 421: an unconditional quantitative omission bound.
The adjacent-product obstruction is from Pratt, Proposition 7.1.
The disjoint-triple argument sharpens that proposition's arbitrary-set bound.
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Sqrt

namespace JustinSunPrize.JSP000346
open scoped BigOperators
open Filter
open scoped Topology

/-- Different nonempty consecutive index intervals have different products. -/
def DistinctBlockProducts (d : ℕ → ℕ) : Prop :=
  {p : ℕ × ℕ | p.1 ≤ p.2}.InjOn
    (fun p => ∏ i ∈ Finset.Icc p.1 p.2, d i)

/-- The local obstruction used in the quantitative argument. -/
def AvoidsAdjacentProduct (B : Set ℕ) : Prop :=
  ∀ a : ℕ, 2 ≤ a → a ∈ B → a + 1 ∈ B → a * (a + 1) ∉ B

/-- Consecutive values in a strictly increasing sequence have consecutive indices. -/
theorem consecutive_indices (d : ℕ → ℕ) (hd : StrictMono d)
    (i j : ℕ) (h : d j = d i + 1) : j = i + 1 := by
  have hij : i < j := hd.lt_iff_lt.mp (by omega)
  have hnext : d (i + 1) ≤ d j := hd.monotone (by omega)
  have hi : d i < d (i + 1) := hd (by omega)
  have heq : d (i + 1) = d j := by omega
  exact (hd.injective heq).symm

/-- Pratt's adjacent-product obstruction, derived from the literal interval condition. -/
theorem block_products_avoid_adjacent (d : ℕ → ℕ) (hd : StrictMono d)
    (hprod : DistinctBlockProducts d) : AvoidsAdjacentProduct (Set.range d) := by
  intro a _ha hi hj hk
  obtain ⟨i, rfl⟩ := hi
  obtain ⟨j, hj⟩ := hj
  obtain ⟨k, hk⟩ := hk
  have hji := consecutive_indices d hd i j hj
  subst j
  have heq : (∏ u ∈ Finset.Icc i (i + 1), d u) =
      ∏ u ∈ Finset.Icc k k, d u := by
    rw [Finset.prod_Icc_succ_top (by omega)]
    simpa only [Finset.Icc_self, Finset.prod_singleton, hj] using hk.symm
  have hp := hprod (x₁ := (i, i + 1)) (x₂ := (k, k)) (by simp) (by simp) heq
  have h1 := congrArg Prod.fst hp
  have h2 := congrArg Prod.snd hp
  dsimp at h1 h2
  omega

open scoped Classical in
/-- Omitted positive integers at most N; zero is never counted. -/
noncomputable def missing (B : Set ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => n ∉ B)

noncomputable def omittedCount (B : Set ℕ) (N : ℕ) : ℕ := (missing B N).card

/-- Even-odd pairs above a cutoff whose products lie beyond the whole small interval. -/
def indices (r : ℕ) : Finset ℕ :=
  Finset.Icc (Nat.sqrt r / 2 + 1) ((r - 1) / 2)

def pairProduct (k : ℕ) : ℕ := (2 * k) * (2 * k + 1)

/-- Explicit bounds ensure small endpoints and large products cannot collide. -/
theorem index_bounds (r k : ℕ) (hk : k ∈ indices r) :
    1 ≤ k ∧ 2 * k + 1 ≤ r ∧ r < pairProduct k ∧ pairProduct k ≤ r * r := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hk
  have hkpos : 1 ≤ k := by omega
  have hend : 2 * k + 1 ≤ r := by omega
  have hsquare : r < (2*k) * (2*k) := Nat.sqrt_lt.mp (by omega)
  refine ⟨hkpos, hend, ?_, ?_⟩ <;> unfold pairProduct <;> nlinarith

/-- Products belonging to different pairs are distinct. -/
theorem pairProduct_strictMono : StrictMono pairProduct := by
  intro a b hab
  unfold pairProduct
  nlinarith

open scoped Classical in
/-- Choose an actual omitted element in each obstruction triple. -/
noncomputable def hole (B : Set ℕ) (k : ℕ) : ℕ :=
  if 2 * k ∉ B then 2 * k
  else if 2 * k + 1 ∉ B then 2 * k + 1
  else pairProduct k

/-- The choice is in its three-element obstruction set. -/
theorem hole_cases (B : Set ℕ) (k : ℕ) :
    hole B k = 2*k ∨ hole B k = 2*k+1 ∨ hole B k = pairProduct k := by
  classical
  unfold hole
  split_ifs <;> simp

/-- No triple is accepted in full by a set with the local obstruction. -/
theorem hole_not_mem (B : Set ℕ) (hB : AvoidsAdjacentProduct B) (k : ℕ) (hk : 1 ≤ k) :
    hole B k ∉ B := by
  classical
  by_cases h0 : 2*k ∉ B
  · simp [hole, h0]
  · by_cases h1 : 2*k+1 ∉ B
    · simp [hole, h0, h1]
    · have h := hB (2*k) (by omega) (not_not.mp h0) (not_not.mp h1)
      simpa [hole, h0, h1, pairProduct] using h

/-- Every selected hole lies within the original, not merely a larger, cutoff. -/
theorem hole_mem_missing (B : Set ℕ) (hB : AvoidsAdjacentProduct B)
    (N k : ℕ) (hk : k ∈ indices (Nat.sqrt N)) : hole B k ∈ missing B N := by
  classical
  obtain ⟨hkpos, hsmall, hlarge, hupper⟩ := index_bounds (Nat.sqrt N) k hk
  have hrN := Nat.sqrt_le_self N
  have hr2N := Nat.sqrt_le N
  apply Finset.mem_filter.mpr
  refine ⟨?_, hole_not_mem B hB k hkpos⟩
  apply Finset.mem_Icc.mpr
  rcases hole_cases B k with h | h | h <;> rw [h] <;> omega

/-- Different selected triples have no element in common. -/
theorem holes_injective (B : Set ℕ) (r : ℕ) :
    Set.InjOn (hole B) (indices r : Set ℕ) := by
  intro a ha b hb heq
  obtain ⟨ha0, has, hal, hau⟩ := index_bounds r a ha
  obtain ⟨hb0, hbs, hbl, hbu⟩ := index_bounds r b hb
  rcases hole_cases B a with h1 | h1 | h1 <;>
    rcases hole_cases B b with h2 | h2 | h2
  all_goals rw [h1, h2] at heq
  all_goals first | omega | exact pairProduct_strictMono.injective heq

/-- Exact count of the disjoint obstruction triples, including empty small cases. -/
theorem indices_card (r : ℕ) : (indices r).card = (r-1)/2 - Nat.sqrt r / 2 := by
  rw [indices, Nat.card_Icc]
  omega

/-- An explicit fourth-root-error bound in natural-number arithmetic. -/
theorem omission_bound_nat (B : Set ℕ) (hB : AvoidsAdjacentProduct B) (N : ℕ) :
    (Nat.sqrt N - 1)/2 - Nat.sqrt (Nat.sqrt N)/2 ≤ omittedCount B N := by
  classical
  have hcard := Finset.card_le_card_of_injOn (hole B)
    (fun k hk => hole_mem_missing B hB N k hk) (holes_injective B (Nat.sqrt N))
  simpa only [indices_card, omittedCount] using hcard

/-- A subtraction-free version of the finite bound. -/
theorem omission_bound_integral (B : Set ℕ) (hB : AvoidsAdjacentProduct B) (N : ℕ) :
    Nat.sqrt N ≤ 2 * omittedCount B N + Nat.sqrt (Nat.sqrt N) + 2 := by
  have h := omission_bound_nat B hB N
  omega

/-- The integer square root is bounded by the ordinary real square root. -/
theorem nat_sqrt_le_real (N : ℕ) : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) := by
  have h := Nat.sqrt_le N
  have hr : (Nat.sqrt N : ℝ) * Nat.sqrt N ≤ N := by exact_mod_cast h
  have hs := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hp := Real.sqrt_nonneg (N : ℝ)
  have hn : (0 : ℝ) ≤ Nat.sqrt N := by positivity
  nlinarith

/-- The real square root differs from the integer square root by less than one. -/
theorem real_sqrt_lt_nat_succ (N : ℕ) : Real.sqrt (N : ℝ) < (Nat.sqrt N : ℝ) + 1 := by
  have h := Nat.lt_succ_sqrt N
  have hr : (N : ℝ) < (Nat.sqrt N + 1 : ℝ) * (Nat.sqrt N + 1 : ℝ) := by
    exact_mod_cast h
  have hs := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hp := Real.sqrt_nonneg (N : ℝ)
  have hn : (0 : ℝ) ≤ Nat.sqrt N := by positivity
  nlinarith

/-- Unconditional coefficient one-half, with an explicit fourth-root error. -/
theorem omission_bound_real (B : Set ℕ) (hB : AvoidsAdjacentProduct B) (N : ℕ) :
    Real.sqrt (N : ℝ) / 2 - Real.sqrt (Real.sqrt (N : ℝ))/2 - (3 : ℝ)/2 ≤
      (omittedCount B N : ℝ) := by
  have h := omission_bound_integral B hB N
  have hr : (Nat.sqrt N : ℝ) ≤ 2 * (omittedCount B N : ℝ) +
      (Nat.sqrt (Nat.sqrt N) : ℝ) + 2 := by exact_mod_cast h
  have hfloor := real_sqrt_lt_nat_succ N
  have hfourth : (Nat.sqrt (Nat.sqrt N) : ℝ) ≤ Real.sqrt (Real.sqrt (N : ℝ)) :=
    (nat_sqrt_le_real (Nat.sqrt N)).trans (Real.sqrt_le_sqrt (nat_sqrt_le_real N))
  linarith

/-- The proved coefficient applies eventually at every large cutoff, not just a subsequence. -/
theorem omission_bound_eventually (B : Set ℕ) (hB : AvoidsAdjacentProduct B)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((1 : ℝ)/2 - ε) * Real.sqrt (N : ℝ) ≤ omittedCount B N := by
  obtain ⟨M, hM⟩ := exists_nat_gt (max (2 : ℝ) (4/ε))
  have hM2 : (2 : ℝ) < M := (le_max_left _ _).trans_lt hM
  have hMε : 4 < ε * M := by
    have := (le_max_right (2 : ℝ) (4/ε)).trans_lt hM
    exact (div_lt_iff₀ hε).mp this |>.trans_eq (mul_comm _ _)
  filter_upwards [eventually_ge_atTop (M^4)] with N hN
  let x : ℝ := Real.sqrt (Real.sqrt (N : ℝ))
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x^2 = Real.sqrt (N : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hx4 : x^4 = (N : ℝ) := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    nlinarith [sq_nonneg (x^2 - Real.sqrt (N : ℝ))]
  have hNr : (M : ℝ)^4 ≤ (N : ℝ) := by exact_mod_cast hN
  have hxM : (M : ℝ) ≤ x := by
    by_contra hh
    have hlt : x < (M : ℝ) := by linarith
    have hsq : x^2 < (M : ℝ)^2 := by nlinarith
    have hfour : x^4 < (M : ℝ)^4 := by nlinarith [sq_nonneg (x^2), sq_nonneg ((M : ℝ)^2)]
    linarith
  have hxlarge : 2 < x := hM2.trans_le hxM
  have hex : 4 ≤ ε * x := le_trans hMε.le (mul_le_mul_of_nonneg_left hxM hε.le)
  have herr : x/2 + (3 : ℝ)/2 ≤ ε * Real.sqrt (N : ℝ) := by
    rw [← hx2]
    nlinarith [mul_nonneg (sub_nonneg.mpr hex) hx0]
  have hb := omission_bound_real B hB N
  change Real.sqrt (N : ℝ)/2 - x/2 - (3 : ℝ)/2 ≤ (omittedCount B N : ℝ) at hb
  nlinarith

/-- Final result for the original consecutive-block-product hypothesis. -/
theorem product_distinct_omission_bound (d : ℕ → ℕ) (hd : StrictMono d)
    (hprod : DistinctBlockProducts d) (N : ℕ) :
    Real.sqrt (N : ℝ)/2 - Real.sqrt (Real.sqrt (N : ℝ))/2 - (3 : ℝ)/2 ≤
      (omittedCount (Set.range d) N : ℝ) :=
  omission_bound_real _ (block_products_avoid_adjacent d hd hprod) N

/-- The unconditional half-root asymptotic for every product-distinct increasing sequence. -/
theorem product_distinct_half_root (d : ℕ → ℕ) (hd : StrictMono d)
    (hprod : DistinctBlockProducts d) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((1 : ℝ)/2 - ε) * Real.sqrt (N : ℝ) ≤
      (omittedCount (Set.range d) N : ℝ) :=
  omission_bound_eventually _ (block_products_avoid_adjacent d hd hprod) ε hε

#print axioms consecutive_indices
#print axioms block_products_avoid_adjacent
#print axioms index_bounds
#print axioms pairProduct_strictMono
#print axioms hole_cases
#print axioms hole_not_mem
#print axioms hole_mem_missing
#print axioms holes_injective
#print axioms indices_card
#print axioms omission_bound_nat
#print axioms omission_bound_integral
#print axioms nat_sqrt_le_real
#print axioms real_sqrt_lt_nat_succ
#print axioms omission_bound_real
#print axioms omission_bound_eventually
#print axioms product_distinct_omission_bound
#print axioms product_distinct_half_root

end JustinSunPrize.JSP000346
