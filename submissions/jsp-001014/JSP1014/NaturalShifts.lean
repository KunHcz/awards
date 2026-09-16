/-
SPDX-License-Identifier: Apache-2.0

JSP-001014 / Erdős 1209, first two questions.
Formalization of the classical diagonal Dirichlet construction described at
https://www.erdosproblems.com/1209 . This is NOT a new mathematical discovery.
The separate Fermat-number questions are not claimed here.
-/
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

namespace JustinSunPrize.JSP001014

/-- For any positive shift, an arbitrarily large prime acquires a nonunit
square divisor after that shift. -/
theorem prime_with_square_obstruction (s B : ℕ) (hs : 0 < s) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ ¬ Squarefree (s + p) := by
  let m := (s + 1) ^ 2
  have hm : m ≠ 0 := by dsimp [m]; positivity
  let : NeZero m := ⟨hm⟩
  have hc : s.Coprime m := by
    dsimp [m]
    exact (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right s)).pow_right 2
  have hu : IsUnit (-(s : ZMod m)) :=
    ((ZMod.isUnit_iff_coprime s m).mpr hc).neg
  obtain ⟨p, hpB, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu B
  refine ⟨p, hpB, hp, ?_⟩
  have hz : ((s + p : ℕ) : ZMod m) = 0 := by
    push_cast
    rw [hmod, add_neg_cancel]
  have hd : m ∣ s + p := (ZMod.natCast_eq_zero_iff _ _).mp hz
  intro hsf
  have hunit : IsUnit (s + 1) := hsf (s + 1) (by simpa [m, pow_two] using hd)
  have := Nat.isUnit_iff.mp hunit
  omega

/-- A chosen prime with the proven obstruction; not an assumed oracle. -/
noncomputable def nextPrime (s B : ℕ) : ℕ :=
  Classical.choose (prime_with_square_obstruction (s + 1) B (by omega))

theorem nextPrime_spec (s B : ℕ) :
    B < nextPrime s B ∧ (nextPrime s B).Prime ∧
      ¬ Squarefree ((s + 1) + nextPrime s B) :=
  Classical.choose_spec (prime_with_square_obstruction (s + 1) B (by omega))

/-- A strictly increasing prime sequence above an arbitrary pointwise bound. -/
noncomputable def sequence (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => nextPrime 0 (f 0)
  | k + 1 => nextPrime (k + 1) (max (f (k + 1)) (sequence f k))

theorem sequence_spec (f : ℕ → ℕ) (k : ℕ) :
    f k < sequence f k ∧ (sequence f k).Prime ∧
      ¬ Squarefree ((k + 1) + sequence f k) := by
  cases k with
  | zero => exact nextPrime_spec 0 (f 0)
  | succ k =>
    have h := nextPrime_spec (k + 1) (max (f (k + 1)) (sequence f k))
    exact ⟨lt_of_le_of_lt (le_max_left _ _) h.1, h.2⟩

theorem sequence_strictMono (f : ℕ → ℕ) : StrictMono (sequence f) := by
  apply strictMono_nat_of_lt_succ
  intro k
  exact lt_of_le_of_lt (le_max_right _ _)
    (nextPrime_spec (k + 1) (max (f (k + 1)) (sequence f k))).1

/-- Among all natural shifts, exactly zero preserves squarefreeness of every term. -/
theorem squarefree_shift_iff (f : ℕ → ℕ) (n : ℕ) :
    (∀ k : ℕ, Squarefree (n + sequence f k)) ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact (sequence_spec f k).2.2 (h k)
  · rintro rfl
    intro k
    simpa using (sequence_spec f k).2.1.squarefree

/-- Among all natural shifts, exactly zero preserves primality of every term. -/
theorem prime_shift_iff (f : ℕ → ℕ) (n : ℕ) :
    (∀ k : ℕ, (n + sequence f k).Prime) ↔ n = 0 := by
  constructor
  · intro h
    exact (squarefree_shift_iff f n).mp (fun k => (h k).squarefree)
  · rintro rfl
    intro k
    simpa using (sequence_spec f k).2.1

/-- Both complete counterexamples hold for the same sequence, for every growth bound. -/
theorem simultaneous_counterexample (f : ℕ → ℕ) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ k, f k ≤ a k) ∧
      (∀ k, (a k).Prime) ∧
      {n : ℕ | ∀ k, (n + a k).Prime} = {0} ∧
      {n : ℕ | ∀ k, Squarefree (n + a k)} = {0} := by
  refine ⟨sequence f, sequence_strictMono f, ?_, ?_, ?_, ?_⟩
  · exact fun k => (sequence_spec f k).1.le
  · exact fun k => (sequence_spec f k).2.1
  · ext n
    exact prime_shift_iff f n
  · ext n
    exact squarefree_shift_iff f n

/-- Negation of the entire first question, including the quantifier over growth bounds. -/
theorem answer_prime :
    ¬ (∃ f : ℕ → ℕ, ∀ a : ℕ → ℕ, StrictMono a → (∀ k, f k ≤ a k) →
      (∃ n : ℕ, ∀ k, (n + a k).Prime) →
      {n : ℕ | ∀ k, (n + a k).Prime}.Infinite) := by
  rintro ⟨f, hf⟩
  obtain ⟨a, ha, hbound, hp, hset, _⟩ := simultaneous_counterexample f
  have hInf := hf a ha hbound ⟨0, by simpa using hp⟩
  rw [hset] at hInf
  exact Set.finite_singleton 0 |>.not_infinite hInf

/-- Negation of the entire second question, with the same unbounded quantifiers. -/
theorem answer_squarefree :
    ¬ (∃ f : ℕ → ℕ, ∀ a : ℕ → ℕ, StrictMono a → (∀ k, f k ≤ a k) →
      (∃ n : ℕ, ∀ k, Squarefree (n + a k)) →
      {n : ℕ | ∀ k, Squarefree (n + a k)}.Infinite) := by
  rintro ⟨f, hf⟩
  obtain ⟨a, ha, hbound, hp, _, hset⟩ := simultaneous_counterexample f
  have hInf := hf a ha hbound ⟨0, fun k => by simpa using (hp k).squarefree⟩
  rw [hset] at hInf
  exact Set.finite_singleton 0 |>.not_infinite hInf

#print axioms prime_with_square_obstruction
#print axioms nextPrime_spec
#print axioms sequence_spec
#print axioms sequence_strictMono
#print axioms squarefree_shift_iff
#print axioms prime_shift_iff
#print axioms simultaneous_counterexample
#print axioms answer_prime
#print axioms answer_squarefree

end JustinSunPrize.JSP001014
