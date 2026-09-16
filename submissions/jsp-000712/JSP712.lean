/- SPDX-License-Identifier: Apache-2.0
JSP-000712 / Erdos 859: exact rational density for every fixed divisor-sum target.
Known periodicity argument; no asymptotic estimate as the target grows is claimed.
-/
import Mathlib.Data.Nat.Count
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace JustinSunPrize.JSP000712
open Filter
open scoped Topology

/-- The literal distinct-divisor subset-sum property. -/
def DivisorSum (t n : ℕ) : Prop :=
  ∃ s : Finset ℕ, s ⊆ n.divisors ∧ ∑ a ∈ s, a = t

/-- A finite predicate using only possible summands from 1 to t. -/
def Good (t n : ℕ) : Prop :=
  ∃ s ∈ (Finset.Icc 1 t).powerset, (∑ a ∈ s, a) = t ∧ ∀ a ∈ s, a ∣ n

instance (t n : ℕ) : Decidable (Good t n) := by
  unfold Good
  infer_instance

theorem good_iff_divisorSum (t n : ℕ) (hn : 0 < n) : Good t n ↔ DivisorSum t n := by
  constructor
  · rintro ⟨s, hs, hsum, hdiv⟩
    refine ⟨s, ?_, hsum⟩
    intro a ha
    exact Nat.mem_divisors.mpr ⟨hdiv a ha, hn.ne'⟩
  · rintro ⟨s, hs, hsum⟩
    refine ⟨s, Finset.mem_powerset.mpr ?_, hsum, ?_⟩
    · intro a ha
      have hdiv := Nat.mem_divisors.mp (hs ha)
      have hpos : 0 < a := Nat.pos_of_dvd_of_pos hdiv.1 hn
      have hle : a ≤ t := hsum ▸ Finset.single_le_sum (fun i _ => Nat.zero_le i) ha
      exact Finset.mem_Icc.mpr ⟨hpos, hle⟩
    · intro a ha
      exact (Nat.mem_divisors.mp (hs ha)).1

/-- Factorial is a valid period, including the t=0 case. It need not be minimal. -/
theorem good_periodic (t n : ℕ) : Good t (n + t.factorial) ↔ Good t n := by
  have hd : ∀ s ∈ (Finset.Icc 1 t).powerset, ∀ a ∈ s, a ∣ t.factorial := by
    intro s hs a ha
    have h := Finset.mem_Icc.mp ((Finset.mem_powerset.mp hs) ha)
    exact Nat.dvd_factorial h.1 h.2
  constructor
  · rintro ⟨s, hs, hsum, hdiv⟩
    refine ⟨s, hs, hsum, fun a ha => ?_⟩
    exact (Nat.dvd_add_iff_right (hd s hs a ha)).mpr (by simpa [add_comm] using hdiv a ha)
  · rintro ⟨s, hs, hsum, hdiv⟩
    refine ⟨s, hs, hsum, fun a ha => ?_⟩
    exact dvd_add (hdiv a ha) (hd s hs a ha)

theorem periodic_multiple (p : ℕ → Prop) (L : ℕ) (hp : ∀ n, p (n + L) ↔ p n)
    (k n : ℕ) : p (k * L + n) ↔ p n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := hp (k * L + n)
    simpa only [Nat.succ_mul, add_assoc, add_comm, add_left_comm] using h.trans ih

theorem count_shift (p : ℕ → Prop) [DecidablePred p] (L : ℕ)
    (hp : ∀ n, p (n + L) ↔ p n) (k n : ℕ) :
    Nat.count (fun j => p (k * L + j)) n = Nat.count p n := by
  have h : (fun j => p (k * L + j)) = p := by
    funext j
    exact propext (periodic_multiple p L hp k j)
  simp only [h]

theorem count_blocks (p : ℕ → Prop) [DecidablePred p] (L : ℕ)
    (hp : ∀ n, p (n + L) ↔ p n) (k : ℕ) :
    Nat.count p (k * L) = k * Nat.count p L := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Nat.count_add, ih, count_shift p L hp]
    ring

/-- Exact quotient/remainder formula, not an asymptotic approximation. -/
theorem count_decomposition (p : ℕ → Prop) [DecidablePred p] (L : ℕ)
    (hp : ∀ n, p (n + L) ↔ p n) (N : ℕ) :
    Nat.count p N = (N / L) * Nat.count p L + Nat.count p (N % L) := by
  calc
    Nat.count p N = Nat.count p ((N / L) * L + N % L) := by
      rw [Nat.mul_comm (N / L) L, Nat.div_add_mod]
    _ = _ := by rw [Nat.count_add, count_blocks p L hp, count_shift p L hp]

/-- Every periodic predicate has a uniform absolute counting error at most one period. -/
theorem periodic_count_error (p : ℕ → Prop) [DecidablePred p] (L : ℕ) (hL : 0 < L)
    (hp : ∀ n, p (n + L) ↔ p n) (N : ℕ) :
    |(Nat.count p N : ℝ) - (N : ℝ) * ((Nat.count p L : ℝ) / L)| ≤ L := by
  let d : ℝ := (Nat.count p L : ℝ) / L
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hd1 : d ≤ 1 := by
    dsimp [d]
    exact (div_le_one hLr).mpr (by exact_mod_cast Nat.count_le (p := p) (n := L))
  have hd : (L : ℝ) * d = Nat.count p L := by dsimp [d]; field_simp
  have hN : (N : ℝ) = (N / L : ℕ) * (L : ℝ) + (N % L : ℕ) := by
    exact_mod_cast (show N = N / L * L + N % L by
      simpa [Nat.mul_comm] using (Nat.div_add_mod N L).symm)
  have hc : (Nat.count p N : ℝ) = (N / L : ℕ) * (Nat.count p L : ℝ) +
      (Nat.count p (N % L) : ℝ) := by exact_mod_cast count_decomposition p L hp N
  have hr : ((N % L : ℕ) : ℝ) < L := by exact_mod_cast Nat.mod_lt N hL
  have hR0 : (0 : ℝ) ≤ Nat.count p (N % L) := by positivity
  have hR : (Nat.count p (N % L) : ℝ) ≤ (N % L : ℕ) := by
    exact_mod_cast Nat.count_le (p := p) (n := N % L)
  have hrd : (0 : ℝ) ≤ (N % L : ℕ) * d := mul_nonneg (Nat.cast_nonneg _) hd0
  have hrd' : (N % L : ℕ) * d ≤ ((N % L : ℕ) : ℝ) := by nlinarith
  have heq : (Nat.count p N : ℝ) - (N : ℝ) * d =
      (Nat.count p (N % L) : ℝ) - (N % L : ℕ) * d := by
    rw [hc, hN]
    nlinarith [congrArg (fun z : ℝ => (N / L : ℕ) * z) hd]
  change |(Nat.count p N : ℝ) - (N : ℝ) * d| ≤ L
  rw [heq, abs_le]
  constructor <;> linarith

/-- Explicit convergence of the actual counting ratio. -/
theorem periodic_density (p : ℕ → Prop) [DecidablePred p] (L : ℕ) (hL : 0 < L)
    (hp : ∀ n, p (n + L) ↔ p n) :
    Tendsto (fun N : ℕ => (Nat.count p N : ℝ) / N) atTop
      (𝓝 ((Nat.count p L : ℝ) / L)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (g := fun N : ℕ => (L : ℝ) / N)
    (Filter.Eventually.of_forall fun _ => dist_nonneg)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.dist_eq]
    have heq : (Nat.count p N : ℝ) / N - (Nat.count p L : ℝ) / L =
        ((Nat.count p N : ℝ) - N * ((Nat.count p L : ℝ) / L)) / N := by
      rw [sub_div, mul_div_cancel_left₀ _ hNr.ne']
    rw [heq, abs_div, abs_of_pos hNr]
    exact div_le_div_of_nonneg_right (periodic_count_error p L hL hp N) hNr.le
  · exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The period itself always has the property: {t} works for positive t. -/
theorem good_factorial (t : ℕ) : Good t t.factorial := by
  by_cases ht : t = 0
  · subst t
    exact ⟨∅, by simp, by simp, by simp⟩
  · refine ⟨{t}, ?_, by simp, ?_⟩
    · simp only [Finset.mem_powerset, Finset.singleton_subset_iff, Finset.mem_Icc]
      omega
    · intro a ha
      have hat : a = t := Finset.mem_singleton.mp ha
      subst a
      exact Nat.dvd_factorial (Nat.pos_of_ne_zero ht) le_rfl

/-- Numerator in a finite, computable exact rational density. -/
def densityNumerator (t : ℕ) : ℕ := Nat.count (fun j => Good t (j + 1)) t.factorial

theorem densityNumerator_pos (t : ℕ) : 0 < densityNumerator t := by
  apply Nat.pos_of_ne_zero
  apply Nat.count_ne_iff_exists.mpr
  have hL := Nat.factorial_pos t
  refine ⟨t.factorial - 1, by omega, ?_⟩
  simpa only [Nat.sub_add_cancel hL] using good_factorial t

theorem densityNumerator_le (t : ℕ) : densityNumerator t ≤ t.factorial :=
  Nat.count_le (fun j => Good t (j + 1))

/-- Exact positive rational density for every target, with no unproved analytical input. -/
theorem divisor_sum_density (t : ℕ) :
    (0 : ℝ) < (densityNumerator t : ℝ) / t.factorial ∧
    (densityNumerator t : ℝ) / t.factorial ≤ 1 ∧
    Tendsto (fun N : ℕ => (Nat.count (fun j => Good t (j + 1)) N : ℝ) / N)
      atTop (𝓝 ((densityNumerator t : ℝ) / t.factorial)) := by
  refine ⟨by positivity [densityNumerator_pos t], ?_, ?_⟩
  · exact (div_le_one (by positivity : (0 : ℝ) < t.factorial)).mpr
      (by exact_mod_cast densityNumerator_le t)
  · apply periodic_density _ _ (Nat.factorial_pos t)
    intro n
    simpa [add_assoc, add_comm, add_left_comm] using good_periodic t (n + 1)

open scoped Classical in
/-- The limit is for the literal divisor-subset property on [1,N], not a surrogate. -/
theorem literal_divisor_sum_density (t : ℕ) :
    ∃ d : ℚ, 0 < d ∧ d ≤ 1 ∧
      Tendsto (fun N : ℕ => ((Finset.Icc 1 N).filter (DivisorSum t)).card / (N : ℝ))
        atTop (𝓝 (d : ℝ)) := by
  classical
  refine ⟨(densityNumerator t : ℚ) / t.factorial, by positivity [densityNumerator_pos t], ?_, ?_⟩
  · exact (div_le_one (by positivity : (0 : ℚ) < t.factorial)).mpr
      (by exact_mod_cast densityNumerator_le t)
  · have h := (divisor_sum_density t).2.2
    have hcount (N : ℕ) : ((Finset.Icc 1 N).filter (DivisorSum t)).card =
        Nat.count (fun j => Good t (j + 1)) N := by
      induction N with
      | zero => simp
      | succ N ih =>
        have hI : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
          ext n
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [hI, Finset.filter_insert, Nat.count_succ]
        have hnot : N + 1 ∉ (Finset.Icc 1 N).filter (DivisorSum t) := by simp
        by_cases hg : Good t (N + 1)
        · have hd := (good_iff_divisorSum t (N + 1) (by omega)).mp hg
          simp only [ite_eq_left hd, ite_eq_left hg, Finset.card_insert_of_notMem hnot, ih]
        · have hd : ¬ DivisorSum t (N + 1) :=
            fun h => hg ((good_iff_divisorSum t (N + 1) (by omega)).mpr h)
          simp only [ite_eq_right hd, ite_eq_right hg, ih, add_zero]
    simpa only [hcount, Rat.cast_div, Rat.cast_natCast] using h

/-- Small exact densities provide executable checks of both indexing and normalization. -/
theorem small_density_values :
    (densityNumerator 0 : ℚ) / Nat.factorial 0 = 1 ∧
    (densityNumerator 1 : ℚ) / Nat.factorial 1 = 1 ∧
    (densityNumerator 2 : ℚ) / Nat.factorial 2 = 1 / 2 ∧
    (densityNumerator 3 : ℚ) / Nat.factorial 3 = 2 / 3 ∧
    (densityNumerator 4 : ℚ) / Nat.factorial 4 = 1 / 2 := by
  decide +kernel

#print axioms good_iff_divisorSum
#print axioms good_periodic
#print axioms periodic_multiple
#print axioms count_shift
#print axioms count_blocks
#print axioms count_decomposition
#print axioms periodic_count_error
#print axioms periodic_density
#print axioms good_factorial
#print axioms densityNumerator_pos
#print axioms densityNumerator_le
#print axioms divisor_sum_density
#print axioms literal_divisor_sum_density
#print axioms small_density_values
end JustinSunPrize.JSP000712
