/- SPDX-License-Identifier: Apache-2.0
JSP-000388 / Erdos 477: the complete quadratic obstruction.
The difference identities are the known AlphaProof/Adenwalla argument.
This formalization does not claim the higher-degree existence theorem.
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace JustinSunPrize.JSP000388

/-- Uniqueness counts value pairs (a,f(x)), not polynomial inputs x. -/
def ExactComplement (f : ℤ → ℤ) (A : Set ℤ) : Prop :=
  ∀ z : ℤ, ∃! uv : ℤ × ℤ, uv ∈ A ×ˢ Set.range f ∧ z = uv.1 + uv.2

/-- An infinite set contains distinct elements congruent modulo any nonzero integer. -/
theorem congruent_pair (A : Set ℤ) (hA : A.Infinite) (q : ℤ) (hq : q ≠ 0) :
    ∃ u ∈ A, ∃ v ∈ A, u ≠ v ∧ q ∣ u - v := by
  let : NeZero q.natAbs := ⟨Int.natAbs_ne_zero.mpr hq⟩
  obtain ⟨u, hu, v, hv, hne, heq⟩ := hA.exists_ne_map_eq_of_mapsTo
    (f := fun z : ℤ => (z : ZMod q.natAbs)) (t := Set.univ)
    (fun _ _ => Set.mem_univ _) (Set.finite_univ)
  refine ⟨u, hu, v, hv, hne, Int.natAbs_dvd.mp ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  push_cast
  rw [heq, sub_self]

/-- A full arithmetic lattice in the difference set prevents an infinite complement. -/
theorem no_infinite_complement (f : ℤ → ℤ) (q : ℤ) (hq : q ≠ 0)
    (hlattice : ∀ k : ℤ, ∃ x y : ℤ, f x - f y = q * k)
    (A : Set ℤ) (hA : A.Infinite) : ¬ ExactComplement f A := by
  intro h
  obtain ⟨u, hu, v, hv, hne, k, hk⟩ := congruent_pair A hA q hq
  obtain ⟨x, y, hxy⟩ := hlattice k
  have hs : u + f y = v + f x := by omega
  have hpair : (u, f y) = (v, f x) := (h (u + f y)).unique
    ⟨⟨hu, ⟨y, rfl⟩⟩, rfl⟩ ⟨⟨hv, ⟨x, rfl⟩⟩, hs⟩
  exact hne (congrArg Prod.fst hpair)

/-- Every target has at least one value-pair representation under exact complementation. -/
theorem terms_of_exact {f : ℤ → ℤ} {A : Set ℤ} (h : ExactComplement f A) (z : ℤ) :
    ∃ u ∈ A, ∃ x : ℤ, z = u + f x := by
  obtain ⟨uv, huv, _⟩ := h z
  obtain ⟨x, hx⟩ := huv.1.2
  exact ⟨uv.1, huv.1.1, x, by simpa [hx] using huv.2⟩

/-- A bounded-on-one-side range cannot cover all integers with a finite complement. -/
theorem complement_infinite_of_one_sided (f : ℤ → ℤ) (A : Set ℤ)
    (hside : (∃ L : ℤ, ∀ x, L ≤ f x) ∨ (∃ U : ℤ, ∀ x, f x ≤ U))
    (h : ExactComplement f A) : A.Infinite := by
  by_contra hfinite
  have hfin : A.Finite := Set.not_infinite.mp hfinite
  rcases hside with ⟨L, hL⟩ | ⟨U, hU⟩
  · obtain ⟨B, hB⟩ := hfin.bddBelow
    obtain ⟨u, hu, x, hx⟩ := terms_of_exact h (B + L - 1)
    have huB := hB hu
    have hxL := hL x
    omega
  · obtain ⟨B, hB⟩ := hfin.bddAbove
    obtain ⟨u, hu, x, hx⟩ := terms_of_exact h (B + U + 1)
    have huB := hB hu
    have hxU := hU x
    omega

/-- A reusable non-tiling criterion with no polynomial-specific hypotheses. -/
theorem no_complement_of_lattice_and_bound (f : ℤ → ℤ) (q : ℤ) (hq : q ≠ 0)
    (hlattice : ∀ k : ℤ, ∃ x y : ℤ, f x - f y = q * k)
    (hside : (∃ L : ℤ, ∀ x, L ≤ f x) ∨ (∃ U : ℤ, ∀ x, f x ≤ U)) :
    ∀ A : Set ℤ, ¬ ExactComplement f A := by
  intro A h
  exact no_infinite_complement f q hq hlattice A
    (complement_infinite_of_one_sided f A hside h) h

/-- All integer quadratics with nonzero leading coefficient, with no divisibility restriction. -/
def quad (a b c x : ℤ) : ℤ := a * x ^ 2 + b * x + c

theorem quad_lower (a b c x : ℤ) (ha : 0 < a) : c - b ^ 2 ≤ quad a b c x := by
  have hmul : 0 ≤ (a - 1) * x ^ 2 := mul_nonneg (by omega) (sq_nonneg x)
  dsimp [quad]
  nlinarith [sq_nonneg x, sq_nonneg (x + b), sq_nonneg b]

theorem quad_upper (a b c x : ℤ) (ha : a < 0) : quad a b c x ≤ c + b ^ 2 := by
  have h := quad_lower (-a) (-b) (-c) x (by omega)
  dsimp [quad] at h ⊢
  nlinarith

theorem quad_one_sided (a b c : ℤ) (ha : a ≠ 0) :
    (∃ L : ℤ, ∀ x, L ≤ quad a b c x) ∨ (∃ U : ℤ, ∀ x, quad a b c x ≤ U) := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · exact Or.inr ⟨c + b ^ 2, fun x => quad_upper a b c x ha⟩
  · exact Or.inl ⟨c - b ^ 2, fun x => quad_lower a b c x ha⟩

theorem quad_difference_lattice (a b c : ℤ) (ha : a ≠ 0) :
    ∃ q : ℤ, q ≠ 0 ∧ ∀ k : ℤ, ∃ x y : ℤ, quad a b c x - quad a b c y = q * k := by
  by_cases hb : b = 0
  · refine ⟨4 * a, mul_ne_zero (by norm_num) ha, fun k => ⟨k + 1, k - 1, ?_⟩⟩
    simp only [quad, hb]
    ring
  · refine ⟨2 * b, mul_ne_zero (by norm_num) hb, fun k => ⟨k, -k, ?_⟩⟩
    simp only [quad]
    ring

/-- The complete quadratic case of the polynomial-value tiling question. -/
theorem no_quadratic_complement (a b c : ℤ) (ha : a ≠ 0) (A : Set ℤ) :
    ¬ ExactComplement (quad a b c) A := by
  obtain ⟨q, hq, hqspec⟩ := quad_difference_lattice a b c ha
  exact no_complement_of_lattice_and_bound (quad a b c) q hq hqspec
    (quad_one_sided a b c ha) A

/-- Expanded version matching the original quantifiers over target integers and value pairs. -/
theorem answer_quadratic (a b c : ℤ) (ha : a ≠ 0) (A : Set ℤ) :
    ∃ z : ℤ, ¬ ∃! uv : ℤ × ℤ,
      uv ∈ A ×ˢ Set.range (fun x : ℤ => a * x ^ 2 + b * x + c) ∧ z = uv.1 + uv.2 := by
  have h := no_quadratic_complement a b c ha A
  unfold ExactComplement quad at h
  push Not at h
  exact h

/-- Bridge from the coefficient formulation to actual degree-two integer polynomials. -/
theorem no_degree_two_polynomial_complement (p : Polynomial ℤ) (hp : p.natDegree = 2)
    (A : Set ℤ) : ¬ ExactComplement p.eval A := by
  have hp0 : p ≠ 0 := by
    intro h
    simp [h] at hp
  have hc : p.coeff 2 ≠ 0 := by
    rw [← hp, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hf : p.eval = quad (p.coeff 2) (p.coeff 1) (p.coeff 0) := by
    funext x
    rw [Polynomial.eval_eq_sum_range, hp]
    simp [Finset.sum_range_succ, quad]
    ring
  rw [hf]
  exact no_quadratic_complement _ _ _ hc A

/-- Boundary check: the nonzero quadratic coefficient cannot be dropped. -/
theorem linear_has_complement : ExactComplement (fun x : ℤ => x) ({0} : Set ℤ) := by
  intro z
  refine ⟨(0, z), ⟨⟨by simp, ⟨z, rfl⟩⟩, by simp⟩, ?_⟩
  rintro ⟨u, v⟩ ⟨⟨hu, _⟩, hz⟩
  have hu0 : u = 0 := by simpa using hu
  subst u
  simp only [zero_add] at hz
  simp [hz]

#print axioms congruent_pair
#print axioms no_infinite_complement
#print axioms terms_of_exact
#print axioms complement_infinite_of_one_sided
#print axioms no_complement_of_lattice_and_bound
#print axioms quad_lower
#print axioms quad_upper
#print axioms quad_one_sided
#print axioms quad_difference_lattice
#print axioms no_quadratic_complement
#print axioms answer_quadratic
#print axioms no_degree_two_polynomial_complement
#print axioms linear_has_complement
end JustinSunPrize.JSP000388
