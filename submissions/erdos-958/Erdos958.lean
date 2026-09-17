/- SPDX-License-Identifier: Apache-2.0
Erdos 958: complete unbounded counterexamples from the circular-arc-plus-centre
construction of Clemen, Dumitrescu and Liu (2025), Section 5.
The construction is known mathematics; this is its Lean formalization.
The reference classification predicates and off-diagonal counting definitions
are adapted from FormalConjectures/ErdosProblems/958.lean and
FormalConjecturesForMathlib/Geometry/Metric.lean, copyright 2025/2026
The Formal Conjectures Authors, licensed under Apache 2.0.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic

namespace Erdos958
open Finset EuclideanGeometry
abbrev Plane := EuclideanSpace ℝ (Fin 2)

def pt (x y : ℝ) : Plane := !₂[x, y]
noncomputable def arc (t : ℝ) : Plane := pt (Real.cos t) (Real.sin t)
noncomputable def angle (m : ℕ) : ℝ := Real.pi / (3 * (m + 1))
noncomputable def sqLen (m d : ℕ) : ℝ := 2 - 2 * Real.cos (d * angle m)

/-- The actual Euclidean metric, expanded in coordinates. -/
theorem dist_sq_coords (p q : Plane) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem arc_dist_sq (s t : ℝ) :
    dist (arc s) (arc t) ^ 2 = 2 - 2 * Real.cos (t - s) := by
  rw [dist_sq_coords, Real.cos_sub]
  change (Real.cos s-Real.cos t)^2 + (Real.sin s-Real.sin t)^2 =
    2-2*(Real.cos t*Real.cos s+Real.sin t*Real.sin s)
  nlinarith [Real.sin_sq_add_cos_sq s, Real.sin_sq_add_cos_sq t]

theorem arc_origin_sq (t : ℝ) : dist (0 : Plane) (arc t) ^ 2 = 1 := by
  rw [dist_sq_coords]
  change (0 - Real.cos t)^2 + (0 - Real.sin t)^2 = 1
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem angle_pos (m : ℕ) : 0 < angle m := by
  unfold angle
  positivity

theorem angle_bound (m d : ℕ) (hd : d ≤ m) :
    (d : ℝ) * angle m < Real.pi / 3 := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hd' : (d : ℝ) < (m : ℝ) + 1 := by exact_mod_cast (show d < m+1 by omega)
  unfold angle
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 3 * (m + 1))).mpr
  nlinarith [Real.pi_pos]

theorem sqLen_pos (m d : ℕ) (hd0 : 0 < d) (hd : d ≤ m) : 0 < sqLen m d := by
  have hpos : (0 : ℝ) < d * angle m := mul_pos (by exact_mod_cast hd0) (angle_pos m)
  have hbound := angle_bound m d hd
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0)
    (by linarith [Real.pi_pos] : (d : ℝ)*angle m ≤ Real.pi) hpos
  simp only [Real.cos_zero] at hc
  unfold sqLen
  linarith

theorem sqLen_lt_one (m d : ℕ) (hd : d ≤ m) : sqLen m d < 1 := by
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi
    (mul_nonneg (Nat.cast_nonneg d) (angle_pos m).le)
    (by linarith [Real.pi_pos] : Real.pi/3 ≤ Real.pi) (angle_bound m d hd)
  rw [Real.cos_pi_div_three] at hc
  unfold sqLen
  linarith

theorem sqLen_strictMono (m : ℕ) : StrictMono (fun d : Fin (m+1) => sqLen m d) := by
  intro a b hab
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi
    (mul_nonneg (Nat.cast_nonneg a.val) (angle_pos m).le)
    (by have := angle_bound m b.val (by omega); linarith [Real.pi_pos] :
      (b.val : ℝ)*angle m ≤ Real.pi)
    (mul_lt_mul_of_pos_right (by exact_mod_cast hab) (angle_pos m))
  unfold sqLen
  linarith

/-- Index zero is the centre, and indices 1,...,m are the m arc points. -/
noncomputable def points (m : ℕ) (i : Fin (m+1)) : Plane :=
  if i.val = 0 then 0 else arc ((i.val - 1 : ℕ) * angle m)

@[simp]
theorem points_zero (m : ℕ) : points m 0 = 0 := by simp [points]

theorem points_pos (m : ℕ) (i : Fin (m+1)) (hi : 0 < i.val) :
    points m i = arc ((i.val - 1 : ℕ) * angle m) := by
  simp [points, show i.val ≠ 0 by omega]

theorem points_pair_sq (m : ℕ) (i j : Fin (m+1)) (hij : i < j) :
    dist (points m i) (points m j) ^ 2 =
      if i.val = 0 then 1 else sqLen m (j.val-i.val) := by
  by_cases hi : i.val = 0
  · have hi' : i = 0 := Fin.ext hi
    subst i
    rw [points_zero, points_pos m j (by simpa using hij), arc_origin_sq]
    simp
  · rw [points_pos m i (by omega), points_pos m j (by omega), arc_dist_sq,
      ite_eq_right hi]
    unfold sqLen
    have hi' : 1 ≤ i.val := by omega
    have hj' : 1 ≤ j.val := by omega
    have he : ((j.val-1 : ℕ) : ℝ)*angle m - ((i.val-1 : ℕ) : ℝ)*angle m =
        ((j.val-i.val : ℕ) : ℝ)*angle m := by
      rw [Nat.cast_sub hi', Nat.cast_sub hj', Nat.cast_sub (le_of_lt hij)]
      push_cast
      ring
    rw [he]

theorem points_injective (m : ℕ) : Function.Injective (points m) := by
  have hordered : ∀ i j : Fin (m+1), i < j → points m i ≠ points m j := by
    intro i j hij heq
    have hs := points_pair_sq m i j hij
    rw [heq, dist_self] at hs
    by_cases hi : i.val = 0
    · simp [hi] at hs
    · rw [ite_eq_right hi] at hs
      have := sqLen_pos m (j.val-i.val) (by omega) (by omega)
      norm_num at hs
      linarith
  intro i j heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hordered i j h heq
  · exact hordered j i h heq.symm

/-- The centre and two distinct short-arc points are not collinear. -/
theorem points_not_collinear (m : ℕ) (hm : 3 ≤ m) :
    ¬ Collinear ℝ (Set.range (points m)) := by
  intro h
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (Set.mem_range_self (0 : Fin (m+1)))).mp h
  obtain ⟨r, hr⟩ := hv (points m ⟨1, by omega⟩) (Set.mem_range_self _)
  obtain ⟨s, hs⟩ := hv (points m ⟨2, by omega⟩) (Set.mem_range_self _)
  have hr0 := congrArg (fun p : Plane => p 0) hr
  have hr1 := congrArg (fun p : Plane => p 1) hr
  have hs1 := congrArg (fun p : Plane => p 1) hs
  simp [points, arc, pt] at hr0 hr1 hs1
  have hrne : r ≠ 0 := by intro he; simp [he] at hr0
  have hv1 : v 1 = 0 := hr1.resolve_left hrne
  have hsin := Real.sin_pos_of_pos_of_lt_pi (angle_pos m)
    (by have := angle_bound m 1 (by omega); norm_num at this; linarith [Real.pi_pos])
  rw [hv1, mul_zero] at hs1
  linarith

/-- The centre and three consecutive arc points cannot lie on any circle. -/
theorem points_not_cospherical (m : ℕ) (hm : 3 ≤ m) :
    ¬ Cospherical (Set.range (points m)) := by
  rintro ⟨c, r, hr⟩
  have h0 := congrArg (fun z : ℝ => z^2) (hr (points m 0) (Set.mem_range_self _))
  rw [points_zero, dist_sq_coords] at h0
  change (0-c 0)^2+(0-c 1)^2=r^2 at h0
  have hd : ∀ j : ℕ, j < m → c 0 * Real.cos (j * angle m) +
      c 1 * Real.sin (j * angle m) = 1/2 := by
    intro j hj
    have h := congrArg (fun z : ℝ => z^2)
      (hr (points m ⟨j+1, by omega⟩) (Set.mem_range_self _))
    rw [points_pos m _ (by simp), dist_sq_coords] at h
    change (Real.cos ((j+1-1 : ℕ)*angle m)-c 0)^2 +
      (Real.sin ((j+1-1 : ℕ)*angle m)-c 1)^2 = r^2 at h
    simp only [Nat.add_sub_cancel] at h
    nlinarith [Real.sin_sq_add_cos_sq ((j:ℝ)*angle m)]
  have h1 := hd 0 (by omega)
  have h2 := hd 1 (by omega)
  have h3 := hd 2 (by omega)
  norm_num at h1 h2 h3
  rw [Real.cos_two_mul, Real.sin_two_mul] at h3
  have hprod := congrArg (fun z : ℝ => 2*Real.cos (angle m)*z) h2
  have hc : Real.cos (angle m) = 1 := by nlinarith
  have hc' := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ) ≤ 0)
    (by have := angle_bound m 1 (by omega); norm_num at this; linarith [Real.pi_pos])
    (angle_pos m)
  simp [hc] at hc'

/-- Each unordered pair is represented exactly once, by its increasing indices. -/
abbrev Pairs (m : ℕ) := {p : Fin (m+1) × Fin (m+1) // p.1 < p.2}

/-- Label zero for radial pairs; positive labels are the gap between arc indices. -/
def pairLabel {m : ℕ} (p : Pairs m) : Fin m :=
  if hi : p.val.1.val = 0 then ⟨0, by have := p.property; omega⟩
  else ⟨p.val.2.val - p.val.1.val, by have := p.property; have := p.val.2.isLt; omega⟩

/-- All pairs of a prescribed label, enumerated without duplication. -/
def pairFromLabel (m : ℕ) (k : Fin m) (i : Fin (m-k.val)) : Pairs m :=
  if hk : k.val = 0 then
    ⟨(⟨0, by omega⟩, ⟨i.val+1, by omega⟩), by change 0 < i.val+1; omega⟩
  else
    ⟨(⟨i.val+1, by omega⟩, ⟨i.val+1+k.val, by omega⟩), by change i.val+1 < i.val+1+k.val; omega⟩

theorem pairFromLabel_label (m : ℕ) (k : Fin m) (i : Fin (m-k.val)) :
    pairLabel (pairFromLabel m k i) = k := by
  apply Fin.ext
  by_cases hk : k.val = 0 <;> simp [pairFromLabel, pairLabel, hk]

theorem pairFromLabel_injective (m : ℕ) (k : Fin m) :
    Function.Injective (pairFromLabel m k) := by
  intro i j h
  apply Fin.ext
  by_cases hk : k.val = 0
  · have := congrArg (fun p : Pairs m => p.val.2.val) h
    simp [pairFromLabel, hk] at this
    omega
  · have := congrArg (fun p : Pairs m => p.val.1.val) h
    simp [pairFromLabel, hk] at this
    omega

theorem pairFromLabel_surjective (m : ℕ) (k : Fin m) (p : Pairs m)
    (hp : pairLabel p = k) : ∃ i, pairFromLabel m k i = p := by
  have heq := congrArg Fin.val hp
  have hlt := p.property
  by_cases hi : p.val.1.val = 0
  · have hk : k.val = 0 := by simpa [pairLabel, hi] using heq.symm
    refine ⟨⟨p.val.2.val-1, by omega⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> simp [pairFromLabel, hk] <;> omega
  · have hk : k.val = p.val.2.val-p.val.1.val := by
      simpa [pairLabel, hi] using heq.symm
    have hk0 : k.val ≠ 0 := by omega
    refine ⟨⟨p.val.1.val-1, by omega⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> simp [pairFromLabel, hk0] <;> omega

/-- Exact cardinality of every label class; no asymptotic estimate. -/
theorem label_card (m : ℕ) (k : Fin m) :
    Fintype.card {p : Pairs m // pairLabel p = k} = m-k.val := by
  classical
  let f : Fin (m-k.val) → {p : Pairs m // pairLabel p = k} :=
    fun i => ⟨pairFromLabel m k i, pairFromLabel_label m k i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact pairFromLabel_injective m k (congrArg Subtype.val h)
    · intro p
      obtain ⟨i, hi⟩ := pairFromLabel_surjective m k p.val p.property
      exact ⟨i, Subtype.ext hi⟩
  exact (Fintype.card_congr (Equiv.ofBijective f hf)).symm.trans (Fintype.card_fin _)

noncomputable def lengths (m : ℕ) (k : Fin m) : ℝ :=
  if k.val = 0 then 1 else Real.sqrt (sqLen m k.val)

theorem lengths_pos (m : ℕ) (k : Fin m) : 0 < lengths m k := by
  by_cases hk : k.val = 0
  · simp [lengths, hk]
  · simp only [lengths, ite_eq_right hk]
    exact Real.sqrt_pos.mpr (sqLen_pos m k.val (by omega) (by omega))

theorem lengths_sq (m : ℕ) (k : Fin m) :
    lengths m k ^ 2 = if k.val = 0 then 1 else sqLen m k.val := by
  by_cases hk : k.val = 0
  · simp [lengths, hk]
  · simp only [lengths, ite_eq_right hk]
    exact Real.sq_sqrt (sqLen_pos m k.val (by omega) (by omega)).le

theorem lengths_injective (m : ℕ) : Function.Injective (lengths m) := by
  intro a b hab
  have hs := congrArg (fun x : ℝ => x^2) hab
  rw [lengths_sq, lengths_sq] at hs
  by_cases ha : a.val = 0
  · by_cases hb : b.val = 0
    · exact Fin.ext (ha.trans hb.symm)
    · rw [ite_eq_left ha, ite_eq_right hb] at hs
      have := sqLen_lt_one m b.val (by omega)
      linarith
  · by_cases hb : b.val = 0
    · rw [ite_eq_right ha, ite_eq_left hb] at hs
      have := sqLen_lt_one m a.val (by omega)
      linarith
    · rw [ite_eq_right ha, ite_eq_right hb] at hs
      have he := (sqLen_strictMono m).injective (a₁ := a.castSucc) (a₂ := b.castSucc) hs
      exact Fin.ext (congrArg (fun x : Fin (m+1) => x.val) he)

/-- Every real Euclidean distance is exactly the distance assigned to its pair label. -/
theorem distance_of_label (m : ℕ) (p : Pairs m) :
    dist (points m p.val.1) (points m p.val.2) = lengths m (pairLabel p) := by
  have hs : dist (points m p.val.1) (points m p.val.2)^2 = lengths m (pairLabel p)^2 := by
    rw [points_pair_sq m p.val.1 p.val.2 p.property, lengths_sq]
    by_cases hi : p.val.1.val = 0
    · simp [pairLabel, hi]
    · have hgap : p.val.2.val-p.val.1.val ≠ 0 := by have := p.property; omega
      simp [pairLabel, hi, hgap]
  have hp := lengths_pos m (pairLabel p)
  have hd := dist_nonneg (x := points m p.val.1) (y := points m p.val.2)
  nlinarith

open scoped Classical in
noncomputable def multiplicity {m : ℕ} (P : Fin (m+1) → Plane) (d : ℝ) : ℕ :=
  Fintype.card {p : Pairs m // dist (P p.val.1) (P p.val.2) = d}

/-- There are m, m-1, ..., 1 pairs at the m different distances. -/
theorem distance_multiplicity (m : ℕ) (k : Fin m) :
    multiplicity (points m) (lengths m k) = m-k.val := by
  classical
  have heq : ∀ p : Pairs m,
      (dist (points m p.val.1) (points m p.val.2) = lengths m k) ↔ pairLabel p = k := by
    intro p
    rw [distance_of_label]
    exact (lengths_injective m).eq_iff
  unfold multiplicity
  rw [Fintype.card_congr (Equiv.subtypeEquivRight heq)]
  exact label_card m k

open scoped Classical in
/-- The positive distances, counted as a set rather than as point pairs. -/
noncomputable def distanceSet {m : ℕ} (P : Fin (m+1) → Plane) : Finset ℝ :=
  Finset.univ.image (fun p : Pairs m => dist (P p.val.1) (P p.val.2))

theorem distanceSet_eq (m : ℕ) :
    distanceSet (points m) = Finset.univ.image (lengths m) := by
  classical
  ext d
  simp only [distanceSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨pairLabel p, (distance_of_label m p).symm⟩
  · rintro ⟨k, rfl⟩
    let i : Fin (m-k.val) := ⟨0, by omega⟩
    refine ⟨pairFromLabel m k i, ?_⟩
    rw [distance_of_label, pairFromLabel_label]

theorem distanceSet_card (m : ℕ) : (distanceSet (points m)).card = m := by
  classical
  rw [distanceSet_eq, Finset.card_image_of_injective _ (lengths_injective m)]
  simp

/-- The exact multiset-of-multiplicities profile, with no omitted distances. -/
theorem multiplicity_profile (m : ℕ) :
    (distanceSet (points m)).image (multiplicity (points m)) = Finset.Icc 1 m := by
  classical
  rw [distanceSet_eq, Finset.image_image]
  ext r
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply,
    distance_multiplicity, Finset.mem_Icc]
  constructor
  · rintro ⟨k, rfl⟩
    omega
  · rintro ⟨hr1, hrm⟩
    refine ⟨⟨m-r, by omega⟩, ?_⟩
    dsimp
    omega

/-- Each natural m >= 3 gives m+1 points with the full requested profile.
The non-collinearity and non-cosphericity use mathlib's ordinary geometric notions. -/
theorem full_family (m : ℕ) (hm : 3 ≤ m) :
    Function.Injective (points m) ∧
    (distanceSet (points m)).card = m ∧
    (distanceSet (points m)).image (multiplicity (points m)) = Finset.Icc 1 m ∧
    ¬ Collinear ℝ (Set.range (points m)) ∧
    ¬ Cospherical (Set.range (points m)) := by
  exact ⟨points_injective m, distanceSet_card m, multiplicity_profile m,
    points_not_collinear m hm, points_not_cospherical m hm⟩

/-- Counterexamples of arbitrarily large cardinality; not merely one small exception. -/
theorem unbounded_counterexamples (N : ℕ) :
    ∃ m ≥ N, ∃ P : Fin (m+1) → Plane, Function.Injective P ∧
      (distanceSet P).card = m ∧
      (distanceSet P).image (multiplicity P) = Finset.Icc 1 m ∧
      ¬ Collinear ℝ (Set.range P) ∧ ¬ Cospherical (Set.range P) := by
  exact ⟨max N 3, le_max_left _ _, points (max N 3), full_family _ (le_max_right _ _)⟩

/-- Even the weaker eventual classification by arbitrary lines or circles is false.
In particular the proposed classification by equidistant line/circle points is false. -/
theorem no_eventual_line_or_circle_classification :
    ¬ ∃ N : ℕ, ∀ m ≥ N, ∀ P : Fin (m+1) → Plane, Function.Injective P →
      (distanceSet P).card = m →
      (distanceSet P).image (multiplicity P) = Finset.Icc 1 m →
      Collinear ℝ (Set.range P) ∨ Cospherical (Set.range P) := by
  rintro ⟨N, hN⟩
  obtain ⟨m, hm, P, hP, hd, hp, hl, hc⟩ := unbounded_counterexamples N
  exact (hN m hm P hP hd hp).elim hl hc

open scoped Classical in
noncomputable def pointSet {m : ℕ} (P : Fin (m+1) → Plane) : Finset Plane :=
  Finset.univ.image P

theorem pointSet_card {m : ℕ} (P : Fin (m+1) → Plane) (hP : Function.Injective P) :
    (pointSet P).card = m+1 := by
  classical
  simp [pointSet, Finset.card_image_of_injective _ hP]

theorem pointSet_coe {m : ℕ} (P : Fin (m+1) → Plane) :
    (pointSet P : Set Plane) = Set.range P := by
  classical
  ext x
  simp [pointSet]

open scoped Classical in
/-- The literal off-diagonal distance-set definition from the reference statement. -/
noncomputable def finiteDistances (A : Finset Plane) : Finset ℝ :=
  A.offDiag.image (fun p => dist p.1 p.2)

open scoped Classical in
noncomputable def finiteMultiplicity (A : Finset Plane) (d : ℝ) : ℕ :=
  (A.offDiag.filter (fun p => dist p.1 p.2 = d)).card / 2

def orientedPair {m : ℕ} (P : Fin (m+1) → Plane) (b : Bool) (p : Pairs m) : Plane × Plane :=
  if b then (P p.val.2, P p.val.1) else (P p.val.1, P p.val.2)

theorem orientedPair_injective {m : ℕ} (P : Fin (m+1) → Plane) (hP : Function.Injective P) :
    Function.Injective (fun z : Bool × Pairs m => orientedPair P z.1 z.2) := by
  rintro ⟨b, p⟩ ⟨c, q⟩ heq
  have hp := p.property
  have hq := q.property
  cases b <;> cases c
  · have h1 := hP (congrArg Prod.fst heq)
    have h2 := hP (congrArg Prod.snd heq)
    have hpq : p = q := Subtype.ext (Prod.ext h1 h2)
    subst q
    rfl
  · have h1 := hP (congrArg Prod.fst heq)
    have h2 := hP (congrArg Prod.snd heq)
    change p.val.1 = q.val.2 at h1
    change p.val.2 = q.val.1 at h2
    have : False := by rw [h1, h2] at hp; exact (lt_asymm hp hq)
    exact this.elim
  · have h1 := hP (congrArg Prod.fst heq)
    have h2 := hP (congrArg Prod.snd heq)
    change p.val.2 = q.val.1 at h1
    change p.val.1 = q.val.2 at h2
    have : False := by rw [h1, h2] at hp; exact (lt_asymm hp hq)
    exact this.elim
  · have h1 := hP (congrArg Prod.fst heq)
    have h2 := hP (congrArg Prod.snd heq)
    have hpq : p = q := Subtype.ext (Prod.ext h2 h1)
    subst q
    rfl

theorem orientedPair_mem {m : ℕ} (P : Fin (m+1) → Plane) (hP : Function.Injective P)
    (b : Bool) (p : Pairs m) : orientedPair P b p ∈ (pointSet P).offDiag := by
  classical
  have hne : P p.val.1 ≠ P p.val.2 := fun h => (ne_of_lt p.property) (hP h)
  cases b <;> simp [orientedPair, Finset.mem_offDiag, pointSet, hne, hne.symm]

theorem orientedPair_dist {m : ℕ} (P : Fin (m+1) → Plane) (b : Bool) (p : Pairs m) :
    dist (orientedPair P b p).1 (orientedPair P b p).2 = dist (P p.val.1) (P p.val.2) := by
  cases b <;> simp [orientedPair, dist_comm]

theorem orientedPair_surjective {m : ℕ} (P : Fin (m+1) → Plane)
    (u : Plane × Plane) (hu : u ∈ (pointSet P).offDiag) :
    ∃ b p, orientedPair P b p = u := by
  classical
  obtain ⟨hu1, hu2, hne⟩ := Finset.mem_offDiag.mp hu
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hu1
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hu2
  have hij : i ≠ j := by intro h; subst j; exact hne (hi.symm.trans hj)
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨false, ⟨(i,j), h⟩, Prod.ext hi hj⟩
  · exact ⟨true, ⟨(j,i), h⟩, Prod.ext hi hj⟩

theorem finiteDistances_eq {m : ℕ} (P : Fin (m+1) → Plane) (hP : Function.Injective P) :
    finiteDistances (pointSet P) = distanceSet P := by
  classical
  ext d
  simp only [finiteDistances, distanceSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨b,p,rfl⟩ := orientedPair_surjective P u hu
    exact ⟨p, (orientedPair_dist P b p).symm⟩
  · rintro ⟨p,rfl⟩
    exact ⟨orientedPair P false p, orientedPair_mem P hP false p, orientedPair_dist P false p⟩

/-- A verified two-to-one correspondence removes the risk of counting ordered pairs twice. -/
theorem finiteMultiplicity_eq {m : ℕ} (P : Fin (m+1) → Plane)
    (hP : Function.Injective P) (d : ℝ) :
    finiteMultiplicity (pointSet P) d = multiplicity P d := by
  classical
  let S := (pointSet P).offDiag.filter (fun p => dist p.1 p.2 = d)
  let f : (Bool × {p : Pairs m // dist (P p.val.1) (P p.val.2) = d}) → S := fun z =>
    ⟨orientedPair P z.1 z.2.val, Finset.mem_filter.mpr
      ⟨orientedPair_mem P hP z.1 z.2.val, (orientedPair_dist P z.1 z.2.val).trans z.2.property⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨b,p⟩ ⟨c,q⟩ heq
      have he : orientedPair P b p.val = orientedPair P c q.val := congrArg Subtype.val heq
      have h := orientedPair_injective P hP (a₁ := (b,p.val)) (a₂ := (c,q.val)) he
      have hb : b = c := congrArg (fun z : Bool × Pairs m => z.1) h
      have hpq : p.val = q.val := congrArg (fun z : Bool × Pairs m => z.2) h
      exact Prod.ext hb (Subtype.ext hpq)
    · intro u
      obtain ⟨hu, hd⟩ := Finset.mem_filter.mp u.property
      obtain ⟨b,p,hp⟩ := orientedPair_surjective P u.val hu
      have hpd : dist (P p.val.1) (P p.val.2) = d := by
        rw [← orientedPair_dist P b p, hp]
        exact hd
      exact ⟨(b,⟨p,hpd⟩), Subtype.ext hp⟩
  have hc := Fintype.card_congr (Equiv.ofBijective f hf)
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_coe] at hc
  change S.card / 2 = _
  rw [← hc, Nat.mul_div_right _ (by decide)]
  rfl

/-- Literal finite-set version: every cardinality n >= 4, with the original counting convention. -/
theorem finite_counterexamples (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : Finset Plane, A.card = n ∧ (finiteDistances A).card = n-1 ∧
      (finiteDistances A).image (finiteMultiplicity A) = Finset.Icc 1 (n-1) ∧
      ¬ Collinear ℝ (A : Set Plane) ∧ ¬ Cospherical (A : Set Plane) := by
  classical
  have hP := points_injective (n-1)
  refine ⟨pointSet (points (n-1)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [pointSet_card _ hP]
    omega
  · rw [finiteDistances_eq _ hP]
    exact distanceSet_card _
  · rw [finiteDistances_eq _ hP, show finiteMultiplicity (pointSet (points (n-1))) =
        multiplicity (points (n-1)) from funext (finiteMultiplicity_eq _ hP)]
    exact multiplicity_profile _
  · rw [pointSet_coe]
    exact points_not_collinear _ (by omega)
  · rw [pointSet_coe]
    exact points_not_cospherical _ (by omega)

/-- Same equidistant-line predicate as the reference statement, over the usual Euclidean plane. -/
def IsEquidistantOnLine (A : Finset Plane) : Prop :=
  ∃ a v : Plane, v ≠ 0 ∧ (A : Set Plane) =
    {x | ∃ i : ℕ, i < A.card ∧ x = a + (i : ℝ) • v}

/-- Same equidistant-circle predicate as the reference statement. -/
def IsEquidistantOnCircle (A : Finset Plane) : Prop :=
  ∃ (c : Plane) (r t a : ℝ), 0 < r ∧ a ≠ 0 ∧ (A : Set Plane) =
    {x | ∃ i : ℕ, i < A.card ∧ x = c + r • arc (t + (i : ℝ) * a)}

theorem equidistant_line_collinear (A : Finset Plane) (hA : IsEquidistantOnLine A) :
    Collinear ℝ (A : Set Plane) := by
  obtain ⟨a,v,_,hA⟩ := hA
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨a,v,?_⟩
  intro p hp
  rw [hA] at hp
  obtain ⟨i,_,rfl⟩ := hp
  exact ⟨(i : ℝ), by simp [vadd_eq_add, add_comm]⟩

theorem equidistant_circle_cospherical (A : Finset Plane)
    (hA : IsEquidistantOnCircle A) : Cospherical (A : Set Plane) := by
  obtain ⟨c,r,t,a,hr,_,hA⟩ := hA
  refine ⟨c,r,?_⟩
  intro p hp
  rw [hA] at hp
  obtain ⟨i,_,rfl⟩ := hp
  have hdist := dist_sq_coords (c+r • arc (t+(i:ℝ)*a)) c
  have hnorm := Real.sin_sq_add_cos_sq (t+(i:ℝ)*a)
  have hscaled := congrArg (fun z : ℝ => r^2*z) hnorm
  change dist (c+r • arc (t+(i:ℝ)*a)) c ^ 2 =
    (c 0+r*Real.cos (t+(i:ℝ)*a)-c 0)^2 +
    (c 1+r*Real.sin (t+(i:ℝ)*a)-c 1)^2 at hdist
  have hd : dist (c+r • arc (t+(i:ℝ)*a)) c ^ 2 = r^2 := by
    nlinarith
  nlinarith [dist_nonneg (x := c+r • arc (t+(i:ℝ)*a)) (y := c)]

/-- Direct negation of the full eventual classification from Erdős 958. -/
theorem original_classification_false :
    ¬ ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset Plane, A.card = n →
      ((finiteDistances A).card = n-1 ∧
        (finiteDistances A).image (finiteMultiplicity A) = Finset.Icc 1 (n-1)) →
      (IsEquidistantOnLine A ∨ IsEquidistantOnCircle A) := by
  rintro ⟨N,hN⟩
  obtain ⟨A,hcard,hd,hprofile,hline,hcircle⟩ := finite_counterexamples (max N 4) (le_max_right _ _)
  rcases hN (max N 4) (le_max_left _ _) A hcard ⟨hd,hprofile⟩ with h | h
  · exact hline (equidistant_line_collinear A h)
  · exact hcircle (equidistant_circle_cospherical A h)

#print axioms dist_sq_coords
#print axioms arc_dist_sq
#print axioms arc_origin_sq
#print axioms angle_pos
#print axioms angle_bound
#print axioms sqLen_pos
#print axioms sqLen_lt_one
#print axioms sqLen_strictMono
#print axioms points_zero
#print axioms points_pos
#print axioms points_pair_sq
#print axioms points_injective
#print axioms points_not_collinear
#print axioms points_not_cospherical
#print axioms pairFromLabel_label
#print axioms pairFromLabel_injective
#print axioms pairFromLabel_surjective
#print axioms label_card
#print axioms lengths_pos
#print axioms lengths_sq
#print axioms lengths_injective
#print axioms distance_of_label
#print axioms distance_multiplicity
#print axioms distanceSet_eq
#print axioms distanceSet_card
#print axioms multiplicity_profile
#print axioms full_family
#print axioms unbounded_counterexamples
#print axioms no_eventual_line_or_circle_classification
#print axioms pointSet_card
#print axioms pointSet_coe
#print axioms orientedPair_injective
#print axioms orientedPair_mem
#print axioms orientedPair_dist
#print axioms orientedPair_surjective
#print axioms finiteDistances_eq
#print axioms finiteMultiplicity_eq
#print axioms finite_counterexamples
#print axioms equidistant_line_collinear
#print axioms equidistant_circle_cospherical
#print axioms original_classification_false

end Erdos958
