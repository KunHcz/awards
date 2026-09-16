/- SPDX-License-Identifier: Apache-2.0
JSP-000489 / Erdos 602: Bernstein's countable-family splitting lemma.
Known mathematics. No claim about arbitrary uncountable families.
-/
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

namespace JustinSunPrize.JSP000489
universe u
variable {α : Type u}

noncomputable def fresh (A : ℕ → Set α) (hA : ∀ i, (A i).Infinite)
    (n : ℕ) (used : Finset α) : α :=
  Classical.choose ((hA n).exists_notMem_finset used)

theorem fresh_spec (A : ℕ → Set α) (hA : ∀ i, (A i).Infinite)
    (n : ℕ) (used : Finset α) :
    fresh A hA n used ∈ A n ∧ fresh A hA n used ∉ used :=
  Classical.choose_spec ((hA n).exists_notMem_finset used)

noncomputable def history (A : ℕ → Set α) (hA : ∀ i, (A i).Infinite) : ℕ → Finset α
  | 0 => ∅
  | n + 1 => by
    classical
    exact insert (fresh A hA n (history A hA n)) (history A hA n)

noncomputable def picked (A : ℕ → Set α) (hA : ∀ i, (A i).Infinite) (n : ℕ) : α :=
  fresh A hA n (history A hA n)

theorem history_mono (A : ℕ → Set α) (hA : ∀ i, (A i).Infinite) :
    Monotone (history A hA) := by
  classical
  apply monotone_nat_of_le_succ
  intro n
  exact Finset.subset_insert _ _

theorem picked_mem (A : ℕ → Set α) (hA : ∀ i, (A i).Infinite) (n : ℕ) :
    picked A hA n ∈ A n := (fresh_spec A hA n _).1

theorem picked_ne_of_lt (A : ℕ → Set α) (hA : ∀ i, (A i).Infinite)
    {i j : ℕ} (hij : i < j) : picked A hA i ≠ picked A hA j := by
  classical
  intro heq
  have hmem : picked A hA i ∈ history A hA (i + 1) := by
    simp [history, picked]
  have hj := history_mono A hA (Nat.succ_le_of_lt hij) hmem
  rw [heq] at hj
  exact (fresh_spec A hA j _).2 hj

theorem picked_injective (A : ℕ → Set α) (hA : ∀ i, (A i).Infinite) :
    Function.Injective (picked A hA) := by
  intro i j h
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim (picked_ne_of_lt A hA hij h)
  · exact hij
  · exact False.elim (picked_ne_of_lt A hA hij h.symm)

/-- One coloring simultaneously gives every member infinitely many points of every
natural-number color. The sets themselves and the ground type need not be countable. -/
theorem infinitely_many_each_color (A : ℕ → Set α) (hA : ∀ i, (A i).Infinite) :
    ∃ f : α → ℕ, ∀ i c : ℕ, {x : α | x ∈ A i ∧ f x = c}.Infinite := by
  classical
  let : Nonempty α := ⟨(hA 0).nonempty.choose⟩
  let B : ℕ → Set α := fun t => A (Nat.unpair t).1
  have hB : ∀ t, (B t).Infinite := fun t => hA _
  let e := picked B hB
  have he : Function.Injective e := picked_injective B hB
  let f : α → ℕ := fun x => (Nat.unpair (Nat.unpair (Function.invFun e x)).2).1
  refine ⟨f, fun i c => ?_⟩
  apply Set.infinite_of_injective_forall_mem
    (f := fun r : ℕ => e (Nat.pair i (Nat.pair c r)))
  · intro r s hrs
    have h := congrArg (fun t => (Nat.unpair (Nat.unpair t).2).2) (he hrs)
    simpa using h
  · intro r
    constructor
    · simpa [B] using picked_mem B hB (Nat.pair i (Nat.pair c r))
    · dsimp [f]
      rw [Function.leftInverse_invFun he (Nat.pair i (Nat.pair c r))]
      simp

/-- Every positive finite number of colors can be used infinitely often in every set. -/
theorem finite_color_splitting (A : ℕ → Set α) (hA : ∀ i, (A i).Infinite)
    (q : ℕ) (hq : 0 < q) :
    ∃ f : α → Fin q, ∀ i (c : Fin q), {x : α | x ∈ A i ∧ f x = c}.Infinite := by
  obtain ⟨f, hf⟩ := infinitely_many_each_color A hA
  let g : α → Fin q := fun x => ⟨f x % q, Nat.mod_lt _ hq⟩
  refine ⟨g, fun i c => (hf i c.val).mono ?_⟩
  intro x hx
  refine ⟨hx.1, ?_⟩
  apply Fin.ext
  simp [g, hx.2, Nat.mod_eq_of_lt c.isLt]

/-- Complete countable-index case of Erdos 602. No intersection restriction is needed. -/
theorem bernstein_propertyB (A : ℕ → Set α) (hA : ∀ i, (A i).Infinite) :
    ∃ f : α → Fin 2, ∀ i, ¬ (∀ x ∈ A i, ∀ y ∈ A i, f x = f y) := by
  obtain ⟨f, hf⟩ := finite_color_splitting A hA 2 (by decide)
  refine ⟨f, fun i hmono => ?_⟩
  obtain ⟨x, hx, hfx⟩ := (hf i 0).nonempty
  obtain ⟨y, hy, hfy⟩ := (hf i 1).nonempty
  have h := hmono x hx y hy
  rw [hfx, hfy] at h
  exact (by decide : (0 : Fin 2) ≠ 1) h

#print axioms fresh_spec
#print axioms history_mono
#print axioms picked_mem
#print axioms picked_ne_of_lt
#print axioms picked_injective
#print axioms infinitely_many_each_color
#print axioms finite_color_splitting
#print axioms bernstein_propertyB
end JustinSunPrize.JSP000489
