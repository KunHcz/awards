/-
SPDX-License-Identifier: Apache-2.0

Erdos 751: extend the finite theorem to arbitrary vertex types.
Mathematics: de Bruijn--Erdos compactness and Bondy--Vince (1998).
The imported finite proof is by SpringSense Innovation Institute; it is fetched
unchanged from a pinned public source and is not redistributed in this package.
Only the extension and its verification materials are new contributions here.
-/
import Erdos751.Main
import Mathlib.Combinatorics.SimpleGraph.Finsubgraph

namespace Erdos751Extension

open SimpleGraph
universe u

/-- Finite-color compactness, with no finiteness assumption on the vertex type. -/
theorem colorable_of_finite_subgraphs {V : Type u} (G : SimpleGraph V) (k : ℕ)
    (h : ∀ H : G.Subgraph, H.verts.Finite → H.coe.Colorable k) : G.Colorable k := by
  classical
  exact nonempty_hom_of_forall_finite_subgraph_hom (fun H hH => (h H hH).some)

/-- A failure of a finite coloring has a finite subgraph witness. -/
theorem finite_noncolorable_witness {V : Type u} (G : SimpleGraph V) (k : ℕ)
    (hG : ¬ G.Colorable k) :
    ∃ H : G.Subgraph, H.verts.Finite ∧ ¬ H.coe.Colorable k := by
  classical
  by_contra! h
  exact hG (colorable_of_finite_subgraphs G k h)

/-- Map a genuine simple cycle along an injective graph homomorphism. -/
theorem lift_cycle {V W : Type u} {G : SimpleGraph V} {F : SimpleGraph W}
    (f : G →g F) (hf : Function.Injective f) (C : Erdos751.BV.Cycle (G := G)) :
    ∃ D : Erdos751.BV.Cycle (G := F), D.length = C.length := by
  let D : Erdos751.BV.Cycle (G := F) :=
    { base := f C.base
      walk := C.walk.map f
      isCycle := C.isCycle.map hf
      len_ge_three := by simpa using C.len_ge_three }
  exact ⟨D, by simp [Erdos751.BV.Cycle.length, D]⟩

/-- Any graph requiring at least four colors has two cycle lengths one or two apart.
The vertex type may be infinite or uncountable. -/
theorem close_cycles_of_not_three_colorable {V : Type u} (G : SimpleGraph V)
    (hG : ¬ G.Colorable 3) :
    ∃ C D : Erdos751.BV.Cycle (G := G),
      Nat.dist C.length D.length = 1 ∨ Nat.dist C.length D.length = 2 := by
  classical
  obtain ⟨H, hH, hHC⟩ := finite_noncolorable_witness G 3 hG
  letI : Fintype H.verts := hH.fintype
  have hχ : (4 : ℕ∞) ≤ H.coe.chromaticNumber := by
    have hnot : ¬ H.coe.chromaticNumber ≤ (3 : ℕ) := by
      intro hle
      exact hHC (chromaticNumber_le_iff_colorable.mp hle)
    exact (ENat.add_one_le_iff (by norm_num)).mpr (lt_of_not_ge hnot)
  obtain ⟨C, D, hdist⟩ := Erdos751.Main.erdos_751_strong H.coe hχ
  obtain ⟨C', hC'⟩ := lift_cycle H.hom H.hom_injective C
  obtain ⟨D', hD'⟩ := lift_cycle H.hom H.hom_injective D
  exact ⟨C', D', by simpa [hC', hD'] using hdist⟩

/-- Standard walk-based formulation, independent of the imported cycle wrapper. -/
def CycleLength {V : Type u} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ v : V, ∃ w : G.Walk v v, w.IsCycle ∧ w.length = n

/-- The full arbitrary-graph conclusion in ordered length form. -/
theorem close_cycle_lengths {V : Type u} (G : SimpleGraph V)
    (hχ : (4 : ℕ∞) ≤ G.chromaticNumber) :
    ∃ m n : ℕ, CycleLength G m ∧ CycleLength G n ∧ m < n ∧ n ≤ m + 2 := by
  have hn : ¬ G.Colorable 3 := by
    intro hc
    have hle := hc.chromaticNumber_le
    have : (4 : ℕ∞) ≤ 3 := le_trans hχ hle
    norm_num at this
  obtain ⟨C, D, hdist⟩ := close_cycles_of_not_three_colorable G hn
  have hC : CycleLength G C.length := ⟨C.base, C.walk, C.isCycle, rfl⟩
  have hD : CycleLength G D.length := ⟨D.base, D.walk, D.isCycle, rfl⟩
  by_cases hle : C.length ≤ D.length
  · refine ⟨C.length, D.length, hC, hD, ?_, ?_⟩ <;>
      simp only [Nat.dist_eq_sub_of_le hle] at hdist <;> omega
  · have hle' : D.length ≤ C.length := by omega
    refine ⟨D.length, C.length, hD, hC, ?_, ?_⟩ <;>
      simp only [Nat.dist_eq_sub_of_le_right hle'] at hdist <;> omega

/-- No four-chromatic graph has all distinct cycle lengths separated by at least three. -/
theorem not_three_separated {V : Type u} (G : SimpleGraph V)
    (hχ : G.chromaticNumber = 4) :
    ¬ (∀ m n : ℕ, CycleLength G m → CycleLength G n → m < n → m + 3 ≤ n) := by
  obtain ⟨m, n, hm, hn, hmn, hnear⟩ := close_cycle_lengths G (by rw [hχ])
  intro h
  have := h m n hm hn hmn
  omega

/-- The first original question has a negative answer, over all vertex types. -/
theorem answer :
    ¬ (∀ k : ℕ, ∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = 4 ∧
      ∀ m n : ℕ, CycleLength G m → CycleLength G n → m < n → m + k ≤ n) := by
  rintro h
  obtain ⟨V, G, hχ, hgap⟩ := h 3
  exact not_three_separated G hχ hgap

/-- Requiring every cycle to be long cannot restore the impossible separation. -/
theorem answer_with_girth :
    ¬ (∀ k g : ℕ, ∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = 4 ∧
      (∀ m : ℕ, CycleLength G m → g ≤ m) ∧
      ∀ m n : ℕ, CycleLength G m → CycleLength G n → m < n → m + k ≤ n) := by
  rintro h
  obtain ⟨V, G, hχ, _, hgap⟩ := h 3 0
  exact not_three_separated G hχ hgap

#print axioms Erdos751.Main.erdos_751_strong
#print axioms colorable_of_finite_subgraphs
#print axioms finite_noncolorable_witness
#print axioms lift_cycle
#print axioms close_cycles_of_not_three_colorable
#print axioms close_cycle_lengths
#print axioms not_three_separated
#print axioms answer
#print axioms answer_with_girth

end Erdos751Extension
