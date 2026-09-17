/- SPDX-License-Identifier: Apache-2.0
JSP-000346 / Erdős 421: an unconditional quantitative omission bound.
The adjacent-product obstruction is from Pratt, Proposition 7.1.
The disjoint-triple argument gives coefficient one-half for the weaker local condition.
The retained-successor injection gives coefficient one for the original block condition,
without a density-one assumption.
The minimal block-crossing injection further gives logarithmic and inverse-factorial errors.
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Log

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


/-- A pair of consecutive retained values cannot itself occur as a singleton value. -/
theorem retained_product_not_mem (d : ℕ → ℕ) (hprod : DistinctBlockProducts d) (i : ℕ) :
    d i * d (i+1) ∉ Set.range d := by
  rintro ⟨k,hk⟩
  have heq : (∏ u ∈ Finset.Icc i (i+1), d u) = ∏ u ∈ Finset.Icc k k, d u := by
    rw [Finset.prod_Icc_succ_top (by omega)]
    simpa only [Finset.Icc_self, Finset.prod_singleton] using hk.symm
  have he := hprod (x₁ := (i,i+1)) (x₂ := (k,k)) (by simp) (by simp) heq
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  dsimp at h1 h2
  omega

theorem retained_products_strictMono (d : ℕ → ℕ) (hd : StrictMono d) :
    StrictMono (fun i => d i * d (i+1)) := by
  intro i j hij
  have h1 := hd hij
  have h2 := hd (Nat.add_lt_add_right hij 1)
  have h3 := hd (Nat.lt_succ_self i)
  nlinarith

theorem exists_above (d : ℕ → ℕ) (hd : StrictMono d) (M : ℕ) : ∃ i, M < d i :=
  ⟨M+1, lt_of_lt_of_le (Nat.lt_succ_self M) (hd.id_le (M+1))⟩

noncomputable def cutIndex (d : ℕ → ℕ) (hd : StrictMono d) (M : ℕ) : ℕ :=
  Nat.find (exists_above d hd M)

theorem below_cut_iff (d : ℕ → ℕ) (hd : StrictMono d) (M i : ℕ) :
    d i ≤ M ↔ i < cutIndex d hd M := by
  have ht : M < d (cutIndex d hd M) := Nat.find_spec (exists_above d hd M)
  constructor
  · intro hi
    by_contra h
    have hle : cutIndex d hd M ≤ i := by omega
    have := hd.monotone hle
    omega
  · intro hi
    exact Nat.le_of_not_gt (Nat.find_min (exists_above d hd M) hi)

/-- Only the last retained value below M lacks a successor below M. -/
theorem retained_successor_le (d : ℕ → ℕ) (hd : StrictMono d) (M i : ℕ)
    (hi : d i ≤ M) (hlast : d i ≠ d (cutIndex d hd M - 1)) : d (i+1) ≤ M := by
  have hic := (below_cut_iff d hd M i).mp hi
  have hne : i ≠ cutIndex d hd M - 1 := fun h => hlast (congrArg d h)
  apply (below_cut_iff d hd M (i+1)).mpr
  omega

open scoped Classical in
noncomputable def retainedDomain (d : ℕ → ℕ) (hd : StrictMono d) (M : ℕ) : Finset ℕ :=
  (Finset.Icc (Nat.sqrt M + 1) M).erase (d (cutIndex d hd M - 1))

open scoped Classical in
/-- Charge a missing integer to itself, and a retained integer to its next retained product. -/
noncomputable def retainedHole (d : ℕ → ℕ) (x : ℕ) : ℕ :=
  if x ∈ Set.range d then x * d (Function.invFun d x + 1) else x

theorem retainedHole_at (d : ℕ → ℕ) (hd : StrictMono d) (i : ℕ) :
    retainedHole d (d i) = d i * d (i+1) := by
  have hx : d i ∈ Set.range d := ⟨i,rfl⟩
  simp only [retainedHole, ite_eq_left hx, Function.leftInverse_invFun hd.injective i]

theorem retained_product_large (d : ℕ → ℕ) (hd : StrictMono d) (M i : ℕ)
    (hi : Nat.sqrt M < d i) : M < d i * d (i+1) := by
  have hsq : M < d i * d i := Nat.sqrt_lt.mp hi
  have hn := hd (Nat.lt_succ_self i)
  nlinarith

theorem retainedHole_missing (d : ℕ → ℕ) (hd : StrictMono d)
    (hprod : DistinctBlockProducts d) (x : ℕ) : retainedHole d x ∉ Set.range d := by
  classical
  by_cases hx : x ∈ Set.range d
  · obtain ⟨i,rfl⟩ := hx
    rw [retainedHole_at d hd]
    exact retained_product_not_mem d hprod i
  · simpa only [retainedHole, ite_eq_right hx] using hx

theorem retainedHole_in_range (d : ℕ → ℕ) (hd : StrictMono d) (N M x : ℕ)
    (hMN : M*M ≤ N) (hx : x ∈ retainedDomain d hd M) :
    1 ≤ retainedHole d x ∧ retainedHole d x ≤ N := by
  classical
  obtain ⟨hlast,hx⟩ := Finset.mem_erase.mp hx
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hx
  have hMpos : 1 ≤ M := by omega
  have hle : M ≤ N := by nlinarith
  by_cases hmem : x ∈ Set.range d
  · obtain ⟨i,rfl⟩ := hmem
    have hn := retained_successor_le d hd M i hhi hlast
    have hp := retained_product_large d hd M i (by omega)
    rw [retainedHole_at d hd]
    constructor <;> nlinarith
  · simp only [retainedHole, ite_eq_right hmem]
    omega

/-- Small missing values and large products lie on opposite sides of M. -/
theorem retainedHole_injOn (d : ℕ → ℕ) (hd : StrictMono d) (M : ℕ) :
    Set.InjOn (retainedHole d) (retainedDomain d hd M : Set ℕ) := by
  classical
  intro x hx y hy heq
  have hx' := Finset.mem_Icc.mp (Finset.mem_erase.mp hx).2
  have hy' := Finset.mem_Icc.mp (Finset.mem_erase.mp hy).2
  by_cases hxm : x ∈ Set.range d
  · obtain ⟨i,rfl⟩ := hxm
    rw [retainedHole_at d hd] at heq
    by_cases hym : y ∈ Set.range d
    · obtain ⟨j,rfl⟩ := hym
      rw [retainedHole_at d hd] at heq
      exact congrArg d ((retained_products_strictMono d hd).injective heq)
    · rw [retainedHole, ite_eq_right hym] at heq
      have := retained_product_large d hd M i (by omega)
      omega
  · rw [retainedHole, ite_eq_right hxm] at heq
    by_cases hym : y ∈ Set.range d
    · obtain ⟨j,rfl⟩ := hym
      rw [retainedHole_at d hd] at heq
      have := retained_product_large d hd M j (by omega)
      omega
    · simpa only [retainedHole, ite_eq_right hym] using heq

theorem retainedDomain_card (d : ℕ → ℕ) (hd : StrictMono d) (M : ℕ) :
    M ≤ (retainedDomain d hd M).card + Nat.sqrt M + 1 := by
  classical
  have hs := Nat.sqrt_le_self M
  unfold retainedDomain
  by_cases ht : d (cutIndex d hd M - 1) ∈ Finset.Icc (Nat.sqrt M+1) M
  · have hc := Finset.card_erase_add_one ht
    rw [Nat.card_Icc] at hc
    omega
  · rw [Finset.erase_eq_of_notMem ht, Nat.card_Icc]
    omega

/-- Coefficient one follows from the full block-product hypothesis, without density one. -/
theorem product_distinct_full_root_integral (d : ℕ → ℕ) (hd : StrictMono d)
    (hprod : DistinctBlockProducts d) (N : ℕ) :
    Nat.sqrt N ≤ omittedCount (Set.range d) N + Nat.sqrt (Nat.sqrt N) + 1 := by
  classical
  have hmap : Set.MapsTo (retainedHole d) (retainedDomain d hd (Nat.sqrt N))
      (missing (Set.range d) N) := by
    intro x hx
    refine Finset.mem_filter.mpr ⟨?_, retainedHole_missing d hd hprod x⟩
    exact Finset.mem_Icc.mpr (retainedHole_in_range d hd N (Nat.sqrt N) x (Nat.sqrt_le N) hx)
  have hc := Finset.card_le_card_of_injOn (retainedHole d) hmap (retainedHole_injOn d hd (Nat.sqrt N))
  have hb := retainedDomain_card d hd (Nat.sqrt N)
  unfold omittedCount
  omega

theorem product_distinct_full_root_real (d : ℕ → ℕ) (hd : StrictMono d)
    (hprod : DistinctBlockProducts d) (N : ℕ) :
    Real.sqrt (N : ℝ) - Real.sqrt (Real.sqrt (N : ℝ)) - 2 ≤
      (omittedCount (Set.range d) N : ℝ) := by
  have hr : (Nat.sqrt N : ℝ) ≤ (omittedCount (Set.range d) N : ℝ) +
      (Nat.sqrt (Nat.sqrt N) : ℝ) + 1 := by
    exact_mod_cast product_distinct_full_root_integral d hd hprod N
  have hfloor := real_sqrt_lt_nat_succ N
  have hfourth : (Nat.sqrt (Nat.sqrt N) : ℝ) ≤ Real.sqrt (Real.sqrt (N : ℝ)) :=
    (nat_sqrt_le_real (Nat.sqrt N)).trans (Real.sqrt_le_sqrt (nat_sqrt_le_real N))
  linarith

/-- Every sufficiently large cutoff has omission coefficient at least 1-epsilon. -/
theorem product_distinct_full_root_eventually (d : ℕ → ℕ) (hd : StrictMono d)
    (hprod : DistinctBlockProducts d) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (1-ε) * Real.sqrt (N : ℝ) ≤
      (omittedCount (Set.range d) N : ℝ) := by
  obtain ⟨M,hM⟩ := exists_nat_gt (max (2 : ℝ) (4/ε))
  have hM2 : (2 : ℝ) < M := (le_max_left _ _).trans_lt hM
  have hMε : 4 < ε * M := by
    have h := (le_max_right (2 : ℝ) (4/ε)).trans_lt hM
    exact (div_lt_iff₀ hε).mp h |>.trans_eq (mul_comm _ _)
  filter_upwards [eventually_ge_atTop (M^4)] with N hN
  let x : ℝ := Real.sqrt (Real.sqrt (N : ℝ))
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x^2 = Real.sqrt (N : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hx4 : x^4 = (N : ℝ) := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    nlinarith [sq_nonneg (x^2 - Real.sqrt (N : ℝ))]
  have hNr : (M : ℝ)^4 ≤ N := by exact_mod_cast hN
  have hxM : (M : ℝ) ≤ x := by
    by_contra hh
    have hlt : x < (M : ℝ) := by linarith
    have hs : x^2 < (M : ℝ)^2 := by nlinarith
    have hq : x^4 < (M : ℝ)^4 := by nlinarith [sq_nonneg (x^2), sq_nonneg ((M : ℝ)^2)]
    linarith
  have hxlarge : 2 < x := hM2.trans_le hxM
  have hex : 4 ≤ ε*x := le_trans hMε.le (mul_le_mul_of_nonneg_left hxM hε.le)
  have herr : x+2 ≤ ε * Real.sqrt (N : ℝ) := by
    rw [← hx2]
    nlinarith [mul_nonneg (sub_nonneg.mpr hex) hx0]
  have hb := product_distinct_full_root_real d hd hprod N
  change Real.sqrt (N : ℝ) - x - 2 ≤ (omittedCount (Set.range d) N : ℝ) at hb
  nlinarith


def blockProduct (d : ℕ → ℕ) (i l : ℕ) : ℕ :=
  ∏ k ∈ Finset.range l, d (i+k)

theorem blockProduct_zero (d : ℕ → ℕ) (i : ℕ) : blockProduct d i 0 = 1 := by
  simp [blockProduct]

theorem blockProduct_succ (d : ℕ → ℕ) (i l : ℕ) :
    blockProduct d i (l+1) = blockProduct d i l * d (i+l) := by
  simp only [blockProduct, Finset.prod_range_succ]

theorem blockProduct_interval (d : ℕ → ℕ) (i l : ℕ) :
    blockProduct d i (l+1) = ∏ k ∈ Finset.Icc i (i+l), d k := by
  induction l with
  | zero => simp [blockProduct]
  | succ l ih =>
    rw [blockProduct_succ, ih]
    rw [show i+(l+1) = (i+l)+1 by omega, Finset.prod_Icc_succ_top (by omega)]

theorem retained_term_two_le (d : ℕ → ℕ) (hprod : DistinctBlockProducts d) (i : ℕ) :
    2 ≤ d i := by
  by_contra h
  have hcases : d i = 0 ∨ d i = 1 := by omega
  rcases hcases with hz | ho
  · have heq : (∏ k ∈ Finset.Icc i (i+1), d k) = ∏ k ∈ Finset.Icc i i, d k := by
      rw [Finset.prod_Icc_succ_top (by omega)]
      simp [hz]
    have he := hprod (x₁ := (i,i+1)) (x₂ := (i,i)) (by simp) (by simp) heq
    have := congrArg Prod.snd he
    simp only at this
    omega
  · have heq : (∏ k ∈ Finset.Icc i (i+1), d k) =
        ∏ k ∈ Finset.Icc (i+1) (i+1), d k := by
      rw [Finset.prod_Icc_succ_top (by omega)]
      simp [ho]
    have he := hprod (x₁ := (i,i+1)) (x₂ := (i+1,i+1)) (by simp) (by simp) heq
    have := congrArg Prod.fst he
    simp only at this
    omega

theorem retained_term_index_lower (d : ℕ → ℕ) (hd : StrictMono d)
    (hprod : DistinctBlockProducts d) (i : ℕ) : i+2 ≤ d i := by
  induction i with
  | zero => exact retained_term_two_le d hprod 0
  | succ i ih =>
    have : d i < d (i+1) := hd (by omega)
    omega

theorem blockProduct_factorial_lower (d : ℕ → ℕ) (hd : StrictMono d)
    (hprod : DistinctBlockProducts d) (i l : ℕ) : (l+1).factorial ≤ blockProduct d i l := by
  induction l with
  | zero => simp [blockProduct]
  | succ l ih =>
    rw [blockProduct_succ, Nat.factorial_succ]
    have ht := retained_term_index_lower d hd hprod (i+l)
    nlinarith

theorem blockProduct_power_lower (d : ℕ → ℕ) (hprod : DistinctBlockProducts d)
    (i l : ℕ) : 2^l ≤ blockProduct d i l := by
  induction l with
  | zero => simp [blockProduct]
  | succ l ih =>
    rw [blockProduct_succ, pow_succ]
    have ht := retained_term_two_le d hprod (i+l)
    nlinarith

/-- A crossing exists for all starting indices; no asymptotic estimate is assumed. -/
theorem crossing_exists (d : ℕ → ℕ) (hprod : DistinctBlockProducts d) (i M : ℕ) :
    ∃ l, M < blockProduct d i l := by
  refine ⟨Nat.log 2 M + 1, ?_⟩
  exact (Nat.lt_pow_succ_log_self (by decide : 1 < 2) M).trans_le
    (blockProduct_power_lower d hprod i _)

noncomputable def crossingLength (d : ℕ → ℕ) (hprod : DistinctBlockProducts d)
    (i M : ℕ) : ℕ := Nat.find (crossing_exists d hprod i M)

theorem crossing_spec (d : ℕ → ℕ) (hprod : DistinctBlockProducts d) (i M : ℕ) :
    M < blockProduct d i (crossingLength d hprod i M) :=
  Nat.find_spec (crossing_exists d hprod i M)

theorem crossing_min (d : ℕ → ℕ) (hprod : DistinctBlockProducts d) (i M l : ℕ)
    (hl : l < crossingLength d hprod i M) : blockProduct d i l ≤ M :=
  Nat.le_of_not_gt (Nat.find_min (crossing_exists d hprod i M) hl)

theorem crossing_le (d : ℕ → ℕ) (hprod : DistinctBlockProducts d) (i M L : ℕ)
    (hL : M < blockProduct d i L) : crossingLength d hprod i M ≤ L :=
  Nat.find_min' (crossing_exists d hprod i M) hL

theorem crossing_two_le (d : ℕ → ℕ) (hprod : DistinctBlockProducts d) (i M : ℕ)
    (hM : 1 ≤ M) (hi : d i ≤ M) : 2 ≤ crossingLength d hprod i M := by
  have hc := crossing_spec d hprod i M
  by_contra h
  have hl : crossingLength d hprod i M = 0 ∨ crossingLength d hprod i M = 1 := by omega
  rcases hl with hl | hl <;> rw [hl] at hc <;> simp [blockProduct] at hc <;> omega

open scoped Classical in
noncomputable def crossingDomain (d : ℕ → ℕ) (hd : StrictMono d) (M L : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M) \ ((Finset.range (L-1)).image (fun j => d (cutIndex d hd M - 1 - j)))

theorem crossingDomain_card (d : ℕ → ℕ) (hd : StrictMono d) (M L : ℕ) :
    M ≤ (crossingDomain d hd M L).card + (L-1) := by
  classical
  have hc := Finset.card_le_card_sdiff_add_card
    (s := Finset.Icc 1 M)
    (t := (Finset.range (L-1)).image (fun j => d (cutIndex d hd M - 1 - j)))
  have ht := Finset.card_image_le
    (s := Finset.range (L-1)) (f := fun j => d (cutIndex d hd M - 1 - j))
  simp only [Nat.card_Icc, Finset.card_range] at hc ht
  change M ≤ _ + (L-1)
  unfold crossingDomain
  omega

theorem crossingDomain_room (d : ℕ → ℕ) (hd : StrictMono d) (M L i : ℕ)
    (hi : d i ∈ crossingDomain d hd M L) : i+L ≤ cutIndex d hd M := by
  classical
  obtain ⟨hir,hit⟩ := Finset.mem_sdiff.mp hi
  have him := (Finset.mem_Icc.mp hir).2
  have hic := (below_cut_iff d hd M i).mp him
  by_contra h
  apply hit
  refine Finset.mem_image.mpr ⟨cutIndex d hd M - 1 - i, Finset.mem_range.mpr (by omega), ?_⟩
  congr 1
  omega

open scoped Classical in
noncomputable def crossingHole (d : ℕ → ℕ) (hprod : DistinctBlockProducts d) (M x : ℕ) : ℕ :=
  if x ∈ Set.range d then
    blockProduct d (Function.invFun d x) (crossingLength d hprod (Function.invFun d x) M)
  else x

theorem crossingHole_at (d : ℕ → ℕ) (hd : StrictMono d) (hprod : DistinctBlockProducts d)
    (i M : ℕ) : crossingHole d hprod M (d i) =
      blockProduct d i (crossingLength d hprod i M) := by
  have hi : d i ∈ Set.range d := ⟨i,rfl⟩
  simp only [crossingHole, ite_eq_left hi, Function.leftInverse_invFun hd.injective i]

theorem crossing_product_missing (d : ℕ → ℕ) (hprod : DistinctBlockProducts d)
    (i M : ℕ) (hM : 1 ≤ M) (hi : d i ≤ M) :
    blockProduct d i (crossingLength d hprod i M) ∉ Set.range d := by
  have hl := crossing_two_le d hprod i M hM hi
  obtain ⟨l,he⟩ : ∃ l, crossingLength d hprod i M = l+1 := by
    exact ⟨crossingLength d hprod i M-1, by omega⟩
  rw [he,blockProduct_interval]
  rintro ⟨k,hk⟩
  have heq : (∏ j ∈ Finset.Icc i (i+l), d j) = ∏ j ∈ Finset.Icc k k, d j := by
    simpa only [Finset.Icc_self, Finset.prod_singleton] using hk.symm
  have hp := hprod (x₁ := (i,i+l)) (x₂ := (k,k)) (by simp) (by simp) heq
  have h1 := congrArg Prod.fst hp
  have h2 := congrArg Prod.snd hp
  simp only at h1 h2
  omega

theorem crossing_product_upper (d : ℕ → ℕ) (hd : StrictMono d)
    (hprod : DistinctBlockProducts d) (M L i : ℕ) (hM : 1 ≤ M)
    (hi : d i ∈ crossingDomain d hd M L) (hg : M < blockProduct d i L) :
    blockProduct d i (crossingLength d hprod i M) ≤ M*M := by
  have hiM := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hi).1).2
  have hl2 := crossing_two_le d hprod i M hM hiM
  have hle := crossing_le d hprod i M L hg
  have hroom := crossingDomain_room d hd M L i hi
  obtain ⟨l,he⟩ : ∃ l, crossingLength d hprod i M = l+1 :=
    ⟨crossingLength d hprod i M-1, by omega⟩
  have hp : blockProduct d i l ≤ M := crossing_min d hprod i M l (by omega)
  have ht : d (i+l) ≤ M := (below_cut_iff d hd M (i+l)).mpr (by omega)
  rw [he,blockProduct_succ]
  exact Nat.mul_le_mul hp ht

theorem crossingHole_injective (d : ℕ → ℕ) (hd : StrictMono d)
    (hprod : DistinctBlockProducts d) (M L : ℕ) :
    Set.InjOn (crossingHole d hprod M) (crossingDomain d hd M L : Set ℕ) := by
  classical
  intro x hx y hy heq
  have hxM := Finset.mem_Icc.mp (Finset.mem_sdiff.mp hx).1
  have hyM := Finset.mem_Icc.mp (Finset.mem_sdiff.mp hy).1
  have hM : 1 ≤ M := by omega
  by_cases hxm : x ∈ Set.range d
  · obtain ⟨i,rfl⟩ := hxm
    rw [crossingHole_at d hd] at heq
    by_cases hym : y ∈ Set.range d
    · obtain ⟨j,rfl⟩ := hym
      rw [crossingHole_at d hd] at heq
      have hi := crossing_two_le d hprod i M hM hxM.2
      have hj := crossing_two_le d hprod j M hM hyM.2
      obtain ⟨a,ha⟩ : ∃ a, crossingLength d hprod i M = a+1 :=
        ⟨crossingLength d hprod i M-1, by omega⟩
      obtain ⟨b,hb⟩ : ∃ b, crossingLength d hprod j M = b+1 :=
        ⟨crossingLength d hprod j M-1, by omega⟩
      rw [ha,hb,blockProduct_interval,blockProduct_interval] at heq
      have hp := hprod (x₁ := (i,i+a)) (x₂ := (j,j+b)) (by simp) (by simp) heq
      exact congrArg d (congrArg Prod.fst hp)
    · rw [crossingHole,ite_eq_right hym] at heq
      have := crossing_spec d hprod i M
      omega
  · rw [crossingHole,ite_eq_right hxm] at heq
    by_cases hym : y ∈ Set.range d
    · obtain ⟨j,rfl⟩ := hym
      rw [crossingHole_at d hd] at heq
      have := crossing_spec d hprod j M
      omega
    · simpa only [crossingHole,ite_eq_right hym] using heq

/-- Every common crossing-length bound gives an explicit omission bound. -/
theorem block_crossing_omission (d : ℕ → ℕ) (hd : StrictMono d)
    (hprod : DistinctBlockProducts d) (N M L : ℕ) (hMN : M*M ≤ N)
    (hg : ∀ i, M < blockProduct d i L) :
    M ≤ omittedCount (Set.range d) N + (L-1) := by
  classical
  have hmap : Set.MapsTo (crossingHole d hprod M) (crossingDomain d hd M L)
      (missing (Set.range d) N) := by
    intro x hx
    have hxr := Finset.mem_Icc.mp (Finset.mem_sdiff.mp hx).1
    have hM : 1 ≤ M := by omega
    apply Finset.mem_filter.mpr
    by_cases hmem : x ∈ Set.range d
    · obtain ⟨i,rfl⟩ := hmem
      rw [crossingHole_at d hd]
      have hlo := crossing_spec d hprod i M
      have hhi := (crossing_product_upper d hd hprod M L i hM hx (hg i)).trans hMN
      exact ⟨Finset.mem_Icc.mpr ⟨by omega,hhi⟩,crossing_product_missing d hprod i M hM hxr.2⟩
    · rw [crossingHole,ite_eq_right hmem]
      have hle : M ≤ N := by nlinarith
      exact ⟨Finset.mem_Icc.mpr ⟨hxr.1,hxr.2.trans hle⟩,hmem⟩
  have hc := Finset.card_le_card_of_injOn (crossingHole d hprod M) hmap
    (crossingHole_injective d hd hprod M L)
  have hdcard := crossingDomain_card d hd M L
  unfold omittedCount
  omega

/-- Factorial-scale error; every admissible integer L yields a certified bound. -/
theorem product_distinct_factorial_error (d : ℕ → ℕ) (hd : StrictMono d)
    (hprod : DistinctBlockProducts d) (N L : ℕ) (hL : Nat.sqrt N < (L+1).factorial) :
    Nat.sqrt N ≤ omittedCount (Set.range d) N + (L-1) := by
  apply block_crossing_omission d hd hprod N (Nat.sqrt N) L (Nat.sqrt_le N)
  intro i
  exact hL.trans_le (blockProduct_factorial_lower d hd hprod i L)

/-- In particular the error can be logarithmic instead of fourth-root size. -/
theorem product_distinct_logarithmic_error (d : ℕ → ℕ) (hd : StrictMono d)
    (hprod : DistinctBlockProducts d) (N : ℕ) :
    Nat.sqrt N ≤ omittedCount (Set.range d) N + Nat.log 2 (Nat.sqrt N) := by
  have h := block_crossing_omission d hd hprod N (Nat.sqrt N)
    (Nat.log 2 (Nat.sqrt N)+1) (Nat.sqrt_le N) (fun i =>
      (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (Nat.sqrt N)).trans_le
        (blockProduct_power_lower d hprod i _))
  omega

theorem omission_example_one_hundred_million (d : ℕ → ℕ) (hd : StrictMono d)
    (hprod : DistinctBlockProducts d) :
    9994 ≤ omittedCount (Set.range d) 100000000 := by
  have hs : Nat.sqrt 100000000 = 10000 := by
    have h1 : 10000 ≤ Nat.sqrt 100000000 := Nat.le_sqrt.mpr (by norm_num)
    have h2 : Nat.sqrt 100000000 < 10001 := Nat.sqrt_lt.mpr (by norm_num)
    omega
  have h := product_distinct_factorial_error d hd hprod 100000000 7
    (by rw [hs]; norm_num [Nat.factorial])
  rw [hs] at h
  omega

theorem omission_example_one_trillion (d : ℕ → ℕ) (hd : StrictMono d)
    (hprod : DistinctBlockProducts d) :
    999992 ≤ omittedCount (Set.range d) 1000000000000 := by
  have hs : Nat.sqrt 1000000000000 = 1000000 := by
    have h1 : 1000000 ≤ Nat.sqrt 1000000000000 := Nat.le_sqrt.mpr (by norm_num)
    have h2 : Nat.sqrt 1000000000000 < 1000001 := Nat.sqrt_lt.mpr (by norm_num)
    omega
  have h := product_distinct_factorial_error d hd hprod 1000000000000 9
    (by rw [hs]; norm_num [Nat.factorial])
  rw [hs] at h
  omega

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
#print axioms retained_product_not_mem
#print axioms retained_products_strictMono
#print axioms exists_above
#print axioms below_cut_iff
#print axioms retained_successor_le
#print axioms retainedHole_at
#print axioms retained_product_large
#print axioms retainedHole_missing
#print axioms retainedHole_in_range
#print axioms retainedHole_injOn
#print axioms retainedDomain_card
#print axioms product_distinct_full_root_integral
#print axioms product_distinct_full_root_real
#print axioms product_distinct_full_root_eventually
#print axioms blockProduct_zero
#print axioms blockProduct_succ
#print axioms blockProduct_interval
#print axioms retained_term_two_le
#print axioms retained_term_index_lower
#print axioms blockProduct_factorial_lower
#print axioms blockProduct_power_lower
#print axioms crossing_exists
#print axioms crossing_spec
#print axioms crossing_min
#print axioms crossing_le
#print axioms crossing_two_le
#print axioms crossingDomain_card
#print axioms crossingDomain_room
#print axioms crossingHole_at
#print axioms crossing_product_missing
#print axioms crossing_product_upper
#print axioms crossingHole_injective
#print axioms block_crossing_omission
#print axioms product_distinct_factorial_error
#print axioms product_distinct_logarithmic_error
#print axioms omission_example_one_hundred_million
#print axioms omission_example_one_trillion

end JustinSunPrize.JSP000346
