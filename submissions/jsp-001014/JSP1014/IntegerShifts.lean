/- SPDX-License-Identifier: Apache-2.0
A strengthened domain check: all integer shifts, not only natural shifts.
The mathematical method remains the classical diagonal Dirichlet argument.
-/
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

namespace JustinSunPrize.JSP001014.IntegerShifts

theorem obstruction (z : ℤ) (hz : z ≠ 0) (B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ ¬ Squarefree (z + (p : ℤ)) := by
  let m := (z.natAbs + 1) ^ 2
  have hm : m ≠ 0 := by dsimp [m]; positivity
  let : NeZero m := ⟨hm⟩
  have hc : z.natAbs.Coprime m := by
    dsimp [m]
    exact (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right z.natAbs)).pow_right 2
  have habs : IsUnit (z.natAbs : ZMod m) := (ZMod.isUnit_iff_coprime _ _).mpr hc
  have hu : IsUnit (z : ZMod m) := by
    cases z with
    | ofNat n => simpa using habs
    | negSucc n => simpa using habs.neg
  obtain ⟨p, hpB, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu.neg B
  refine ⟨p, hpB, hp, ?_⟩
  have hzero : ((z + (p : ℤ) : ℤ) : ZMod m) = 0 := by
    push_cast
    rw [hmod, add_neg_cancel]
  have hd : (m : ℤ) ∣ z + (p : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  intro hsf
  have hunit : IsUnit ((z.natAbs + 1 : ℕ) : ℤ) :=
    hsf _ (by simpa [m, pow_two] using hd)
  have hval : z.natAbs + 1 = 1 := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_of_isUnit hunit
  have : z.natAbs = 0 := by omega
  exact hz (Int.natAbs_eq_zero.mp this)

/-- An explicit enumeration of all nonzero integer shifts. -/
def shift (k : ℕ) : ℤ :=
  if k % 2 = 0 then ((k / 2 + 1 : ℕ) : ℤ) else -((k / 2 + 1 : ℕ) : ℤ)

theorem shift_ne_zero (k : ℕ) : shift k ≠ 0 := by
  unfold shift
  split_ifs <;> omega

theorem shift_even (n : ℕ) : shift (2 * n) = (n + 1 : ℕ) := by
  unfold shift
  split_ifs <;> omega

theorem shift_odd (n : ℕ) : shift (2 * n + 1) = -((n + 1 : ℕ) : ℤ) := by
  unfold shift
  split_ifs <;> omega

theorem shift_covers (z : ℤ) (hz : z ≠ 0) : ∃ k : ℕ, shift k = z := by
  cases z with
  | ofNat n =>
    have hn : 0 < n := by
      have hne : n ≠ 0 := by intro h; subst n; exact hz rfl
      omega
    refine ⟨2 * (n - 1), ?_⟩
    rw [shift_even]
    rw [Nat.sub_add_cancel hn]
    rfl
  | negSucc n =>
    refine ⟨2 * n + 1, ?_⟩
    rw [shift_odd]
    omega

noncomputable def next (k B : ℕ) : ℕ :=
  Classical.choose (obstruction (shift k) (shift_ne_zero k) B)

theorem next_spec (k B : ℕ) :
    B < next k B ∧ (next k B).Prime ∧ ¬ Squarefree (shift k + (next k B : ℤ)) :=
  Classical.choose_spec (obstruction (shift k) (shift_ne_zero k) B)

noncomputable def sequence (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => next 0 (f 0)
  | k + 1 => next (k + 1) (max (f (k + 1)) (sequence f k))

theorem sequence_spec (f : ℕ → ℕ) (k : ℕ) :
    f k < sequence f k ∧ (sequence f k).Prime ∧
      ¬ Squarefree (shift k + (sequence f k : ℤ)) := by
  cases k with
  | zero => exact next_spec 0 (f 0)
  | succ k =>
    have h := next_spec (k + 1) (max (f (k + 1)) (sequence f k))
    exact ⟨lt_of_le_of_lt (le_max_left _ _) h.1, h.2⟩

theorem sequence_strictMono (f : ℕ → ℕ) : StrictMono (sequence f) := by
  apply strictMono_nat_of_lt_succ
  intro k
  exact lt_of_le_of_lt (le_max_right _ _)
    (next_spec (k + 1) (max (f (k + 1)) (sequence f k))).1

/-- The squarefree translate set over the entire integer domain is the singleton zero. -/
theorem squarefree_shift_iff (f : ℕ → ℕ) (z : ℤ) :
    (∀ k : ℕ, Squarefree (z + (sequence f k : ℤ))) ↔ z = 0 := by
  constructor
  · intro h
    by_contra hz
    obtain ⟨k, hk⟩ := shift_covers z hz
    have hbad := (sequence_spec f k).2.2
    rw [hk] at hbad
    exact hbad (h k)
  · rintro rfl
    intro k
    simpa using (Int.squarefree_natCast.mpr (sequence_spec f k).2.1.squarefree)

/-- The same theorem for integer primality, which also allows negative associates. -/
theorem prime_shift_iff (f : ℕ → ℕ) (z : ℤ) :
    (∀ k : ℕ, Prime (z + (sequence f k : ℤ))) ↔ z = 0 := by
  constructor
  · intro h
    exact (squarefree_shift_iff f z).mp (fun k => (h k).squarefree)
  · rintro rfl
    intro k
    simpa using (Nat.prime_iff_prime_int.mp (sequence_spec f k).2.1)

theorem simultaneous_counterexample (f : ℕ → ℕ) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ k, f k ≤ a k) ∧ (∀ k, (a k).Prime) ∧
      {z : ℤ | ∀ k, Prime (z + (a k : ℤ))} = {0} ∧
      {z : ℤ | ∀ k, Squarefree (z + (a k : ℤ))} = {0} := by
  refine ⟨sequence f, sequence_strictMono f, ?_, ?_, ?_, ?_⟩
  · exact fun k => (sequence_spec f k).1.le
  · exact fun k => (sequence_spec f k).2.1
  · ext z
    exact prime_shift_iff f z
  · ext z
    exact squarefree_shift_iff f z

#print axioms obstruction
#print axioms shift_ne_zero
#print axioms shift_even
#print axioms shift_odd
#print axioms shift_covers
#print axioms next_spec
#print axioms sequence_spec
#print axioms sequence_strictMono
#print axioms squarefree_shift_iff
#print axioms prime_shift_iff
#print axioms simultaneous_counterexample
end JustinSunPrize.JSP001014.IntegerShifts
