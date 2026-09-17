/- SPDX-License-Identifier: Apache-2.0
Erdős 1008: the sharp rectangular Folkman obstruction.
The mathematical counting argument is classical; this is its formal implementation.
-/
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Copy

namespace Erdos1008
open Finset SimpleGraph

variable {α β : Type}

/-- The actual bipartite simple graph specified by its right neighborhoods. -/
def incidence (F : β → Finset α) : SimpleGraph (α ⊕ β) where
  Adj
    | .inl a, .inr b => a ∈ F b
    | .inr b, .inl a => a ∈ F b
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

instance [DecidableEq α] (F : β → Finset α) : DecidableRel (incidence F).Adj := by
  intro x y
  cases x <;> cases y <;> dsimp [incidence] <;> infer_instance

/-- Each pair of distinct left vertices has at most one common right neighbor. -/
def PairUnique (F : β → Finset α) : Prop :=
  ∀ b c : β, ∀ S : Finset α, S.card = 2 → S ⊆ F b → S ⊆ F c → b = c

theorem incidence_le (F : β → Finset α) : incidence F ≤ completeBipartiteGraph α β := by
  intro x y h
  cases x <;> cases y <;> simp_all [incidence, completeBipartiteGraph]

/-- A rectangle supplies an injective copy of the ordinary four-cycle. -/
theorem rectangle_copy (F : β → Finset α) (a a' : α) (b b' : β)
    (ha : a ≠ a') (hb : b ≠ b')
    (h00 : a ∈ F b) (h01 : a ∈ F b') (h10 : a' ∈ F b) (h11 : a' ∈ F b') :
    cycleGraph 4 ⊑ incidence F := by
  let f : Fin 4 → α ⊕ β := ![.inl a, .inr b, .inl a', .inr b']
  refine ⟨{ toHom := { toFun := f, map_rel' := ?_ }, injective' := ?_ }⟩
  · intro i j hij
    have hcycle : ∀ i j : Fin 4, (cycleGraph 4).Adj i j →
        (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) ∨ (i=1 ∧ j=2) ∨ (i=2 ∧ j=1) ∨
        (i=2 ∧ j=3) ∨ (i=3 ∧ j=2) ∨ (i=3 ∧ j=0) ∨ (i=0 ∧ j=3) := by decide
    rcases hcycle i j hij with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals first | exact h00 | exact h01 | exact h10 | exact h11
  · intro i j heq
    fin_cases i <;> fin_cases j <;> simp_all [f, ha.symm, hb.symm]

theorem pairUnique_of_free (F : β → Finset α) (hF : (cycleGraph 4).Free (incidence F)) :
    PairUnique F := by
  classical
  intro b c S hS hb hc
  by_contra hbc
  obtain ⟨a,a',haa,rfl⟩ := Finset.card_eq_two.mp hS
  exact hF (rectangle_copy F a a' b c haa hbc
    (hb (by simp)) (hc (by simp)) (hb (by simp)) (hc (by simp)))

/-- The combinatorial pair condition is sufficient for genuine four-cycle avoidance. -/
theorem free_of_pairUnique (F : β → Finset α) (hF : PairUnique F) :
    (cycleGraph 4).Free (incidence F) := by
  classical
  rintro ⟨f⟩
  have h01 := f.toHom.map_adj (show (cycleGraph 4).Adj 0 1 by decide)
  have h12 := f.toHom.map_adj (show (cycleGraph 4).Adj 1 2 by decide)
  have h23 := f.toHom.map_adj (show (cycleGraph 4).Adj 2 3 by decide)
  have h30 := f.toHom.map_adj (show (cycleGraph 4).Adj 3 0 by decide)
  change (incidence F).Adj (f 0) (f 1) at h01
  change (incidence F).Adj (f 1) (f 2) at h12
  change (incidence F).Adj (f 2) (f 3) at h23
  change (incidence F).Adj (f 3) (f 0) at h30
  have h02 : f 0 ≠ f 2 := fun h => (by decide : (0 : Fin 4) ≠ 2) (f.injective h)
  have h13 : f 1 ≠ f 3 := fun h => (by decide : (1 : Fin 4) ≠ 3) (f.injective h)
  cases h0 : f 0 with
  | inl a =>
    cases h1 : f 1 with
    | inl x => rw [h0,h1] at h01; exact h01
    | inr b =>
      cases h2 : f 2 with
      | inr x => rw [h1,h2] at h12; exact h12
      | inl a' =>
        cases h3 : f 3 with
        | inl x => rw [h2,h3] at h23; exact h23
        | inr c =>
          rw [h0,h1] at h01
          rw [h1,h2] at h12
          rw [h2,h3] at h23
          rw [h3,h0] at h30
          have ha : a ≠ a' := by intro h; apply h02; rw [h0,h2,h]
          have hb := hF b c {a,a'} (by simp [ha])
            (Finset.insert_subset_iff.mpr ⟨h01,Finset.singleton_subset_iff.mpr h12⟩)
            (Finset.insert_subset_iff.mpr ⟨h30,Finset.singleton_subset_iff.mpr h23⟩)
          apply h13
          rw [h1,h3,hb]
  | inr b =>
    cases h1 : f 1 with
    | inr x => rw [h0,h1] at h01; exact h01
    | inl a =>
      cases h2 : f 2 with
      | inl x => rw [h1,h2] at h12; exact h12
      | inr c =>
        cases h3 : f 3 with
        | inr x => rw [h2,h3] at h23; exact h23
        | inl a' =>
          rw [h0,h1] at h01
          rw [h1,h2] at h12
          rw [h2,h3] at h23
          rw [h3,h0] at h30
          have ha : a ≠ a' := by intro h; apply h13; rw [h1,h3,h]
          have hb := hF b c {a,a'} (by simp [ha])
            (Finset.insert_subset_iff.mpr ⟨h01,Finset.singleton_subset_iff.mpr h30⟩)
            (Finset.insert_subset_iff.mpr ⟨h12,Finset.singleton_subset_iff.mpr h23⟩)
          apply h02
          rw [h0,h2,hb]

/-- The number of incident pairs, counted once each. -/
def incidenceCount [Fintype β] (F : β → Finset α) : ℕ := ∑ b, (F b).card

/-- All right-neighborhood pairs are disjoint subsets of the left-pair universe. -/
theorem sum_pairs_le [Fintype α] [Fintype β] (F : β → Finset α) (hF : PairUnique F) :
    (∑ b, ((F b).card).choose 2) ≤ (Fintype.card α).choose 2 := by
  classical
  let U := Finset.univ.biUnion (fun b : β => (F b).powersetCard 2)
  have hd : (↑(Finset.univ : Finset β) : Set β).PairwiseDisjoint (fun b => (F b).powersetCard 2) := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro S hSb hSc
    have hb' := Finset.mem_powersetCard.mp hSb
    have hc' := Finset.mem_powersetCard.mp hSc
    exact hbc (hF b c S hb'.2 hb'.1 hc'.1)
  have hsub : U ⊆ (Finset.univ : Finset α).powersetCard 2 := by
    intro S hS
    obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp hS
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp hb).2⟩
  have hc := Finset.card_le_card hsub
  change #(Finset.univ.biUnion (fun b : β => (F b).powersetCard 2)) ≤ _ at hc
  rw [Finset.card_biUnion hd] at hc
  simpa only [Finset.card_powersetCard, Finset.card_univ] using hc

/-- Degree d is at most one plus the number of its unordered pairs, including d=0. -/
theorem degree_le_one_add_pairs (d : ℕ) : d ≤ 1 + d.choose 2 := by
  rw [Nat.choose_two_right]
  have h : d * (d-1) ≥ 2*(d-1) := by
    rcases lt_or_ge d 2 with h | h
    · interval_cases d <;> norm_num
    · exact Nat.mul_le_mul_right _ h
  omega

/-- The full rectangular upper bound requires no restriction on the two part sizes. -/
theorem incidence_upper [Fintype α] [Fintype β] (F : β → Finset α) (hF : PairUnique F) :
    incidenceCount F ≤ Fintype.card β + (Fintype.card α).choose 2 := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset β))
    (fun b _ => degree_le_one_add_pairs (F b).card)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  exact h.trans (Nat.add_le_add_left (sum_pairs_le F hF) _)

open scoped Classical in
/-- A right vertex has exactly the specified neighbors in the ordinary simple graph. -/
theorem incidence_degree [Fintype α] [Fintype β] (F : β → Finset α) (b : β) :
    (incidence F).degree (.inr b) = (F b).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have he : (incidence F).neighborFinset (.inr b) = (F b).image Sum.inl := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    cases x <;> simp [incidence]
  rw [he, Finset.card_image_of_injective _ Sum.inl_injective]

/-- Unordered edges are counted once by summing right degrees, not twice. -/
theorem incidence_edges [Fintype α] [Fintype β] (F : β → Finset α) :
    (incidence F).edgeSet.ncard = incidenceCount F := by
  classical
  let S : Finset (α ⊕ β) := Finset.univ.image Sum.inl
  let T : Finset (α ⊕ β) := Finset.univ.image Sum.inr
  have hB : (incidence F).IsBipartiteWith S T := by
    constructor
    · apply Set.disjoint_left.mpr
      intro x hx hy
      cases x <;> simp_all [S,T]
    · intro x y hxy
      cases x <;> cases y <;> simp_all [incidence,S,T]
  have h := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hB
  rw [Finset.sum_image (fun _ _ _ _ he => Sum.inr_injective he)] at h
  change (∑ b, (incidence F).degree (.inr b)) = _ at h
  simp only [incidence_degree] at h
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  exact h.symm

open scoped Classical in
/-- Read the right neighborhoods of a subgraph of the complete bipartite graph. -/
noncomputable def neighbors [Fintype α] (H : SimpleGraph (α ⊕ β)) (b : β) : Finset α :=
  Finset.univ.filter (fun a => H.Adj (.inl a) (.inr b))

/-- The neighborhood model recovers every bipartite subgraph without losing any edges. -/
theorem incidence_neighbors [Fintype α] (H : SimpleGraph (α ⊕ β))
    (hH : H ≤ completeBipartiteGraph α β) : incidence (neighbors H) = H := by
  classical
  ext x y
  cases x with
  | inl a =>
    cases y with
    | inl a' =>
      have hh : ¬H.Adj (.inl a) (.inl a') := by
        intro h; have := hH h; simp [completeBipartiteGraph] at this
      simp [incidence,hh]
    | inr b => simp [incidence,neighbors]
  | inr b =>
    cases y with
    | inl a => simp [incidence,neighbors,H.adj_comm]
    | inr b' =>
      have hh : ¬H.Adj (.inr b) (.inr b') := by
        intro h; have := hH h; simp [completeBipartiteGraph] at this
      simp [incidence,hh]

/-- Upper bound for every literal C4-free bipartite simple graph, all part sizes. -/
theorem rectangular_upper [Fintype α] [Fintype β] (H : SimpleGraph (α ⊕ β))
    (hH : H ≤ completeBipartiteGraph α β) (hfree : (cycleGraph 4).Free H) :
    H.edgeSet.ncard ≤ Fintype.card β + (Fintype.card α).choose 2 := by
  have he := incidence_neighbors H hH
  rw [← he, incidence_edges]
  exact incidence_upper _ (pairUnique_of_free _ (he.symm ▸ hfree))

/-- One vertex for each unordered pair of distinct left vertices. -/
abbrev LeftPair (α : Type) [Fintype α] := ↥((Finset.univ : Finset α).powersetCard 2)

/-- Pair vertices have degree two; the extra right vertices are leaves. -/
def pairNeighbors [Fintype α] (a0 : α) (q : ℕ) : (LeftPair α ⊕ Fin q) → Finset α
  | .inl S => S.val
  | .inr _ => {a0}

theorem leftPair_card [Fintype α] (S : LeftPair α) : S.val.card = 2 :=
  (Finset.mem_powersetCard.mp S.property).2

theorem pairNeighbors_unique [Fintype α] (a0 : α) (q : ℕ) : PairUnique (pairNeighbors a0 q) := by
  classical
  intro b c S hS hb hc
  cases b with
  | inl b =>
    cases c with
    | inl c =>
      have heb : S = b.val := Finset.eq_of_subset_of_card_le hb (by rw [leftPair_card,hS])
      have hec : S = c.val := Finset.eq_of_subset_of_card_le hc (by rw [leftPair_card,hS])
      exact congrArg Sum.inl (Subtype.ext (heb.symm.trans hec))
    | inr c =>
      have h := Finset.card_le_card hc
      change S.card ≤ ({a0} : Finset α).card at h
      simp only [hS, Finset.card_singleton] at h
      omega
  | inr b =>
    have h := Finset.card_le_card hb
    change S.card ≤ ({a0} : Finset α).card at h
    simp only [hS, Finset.card_singleton] at h
    omega

theorem pairNeighbors_count [Fintype α] (a0 : α) (q : ℕ) :
    incidenceCount (pairNeighbors a0 q) = 2 * (Fintype.card α).choose 2 + q := by
  classical
  simp only [incidenceCount, Fintype.sum_sum_type, pairNeighbors, leftPair_card,
    Finset.card_singleton, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  simp only [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, mul_comm]

theorem pairUnique_reindex {γ : Type} (F : γ → Finset α) (e : β ≃ γ) (hF : PairUnique F) :
    PairUnique (F ∘ e) := by
  intro b c S hS hb hc
  exact e.injective (hF (e b) (e c) S hS hb hc)

theorem incidenceCount_reindex [Fintype β] {γ : Type} [Fintype γ]
    (F : γ → Finset α) (e : β ≃ γ) : incidenceCount (F ∘ e) = incidenceCount F :=
  Equiv.sum_comp e (fun c => (F c).card)

/-- A graph attaining the bound, for every s>=1 and t>=choose(s,2). -/
theorem rectangular_attained (s t : ℕ) (hs : 0 < s) (ht : s.choose 2 ≤ t) :
    ∃ H : SimpleGraph (Fin s ⊕ Fin t), H ≤ completeBipartiteGraph (Fin s) (Fin t) ∧
      (cycleGraph 4).Free H ∧ H.edgeSet.ncard = t + s.choose 2 := by
  classical
  let a0 : Fin s := ⟨0,hs⟩
  let γ := LeftPair (Fin s) ⊕ Fin (t-s.choose 2)
  have hc : Fintype.card γ = Fintype.card (Fin t) := by
    simp only [γ, Fintype.card_sum, Fintype.card_coe, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin]
    omega
  let e : Fin t ≃ γ := Fintype.equivOfCardEq hc.symm
  let F := pairNeighbors a0 (t-s.choose 2) ∘ e
  refine ⟨incidence F, incidence_le F, free_of_pairUnique F
    (pairUnique_reindex _ e (pairNeighbors_unique a0 _)), ?_⟩
  rw [incidence_edges, incidenceCount_reindex, pairNeighbors_count, Fintype.card_fin]
  omega

/-- Exact maximum: a witness attains the bound and every eligible graph obeys it. -/
theorem rectangular_exact (s t : ℕ) (hs : 0 < s) (ht : s.choose 2 ≤ t) :
    (∃ H : SimpleGraph (Fin s ⊕ Fin t), H ≤ completeBipartiteGraph (Fin s) (Fin t) ∧
      (cycleGraph 4).Free H ∧ H.edgeSet.ncard = t+s.choose 2) ∧
    (∀ H : SimpleGraph (Fin s ⊕ Fin t), H ≤ completeBipartiteGraph (Fin s) (Fin t) →
      (cycleGraph 4).Free H → H.edgeSet.ncard ≤ t+s.choose 2) := by
  refine ⟨rectangular_attained s t hs ht, ?_⟩
  intro H hH hf
  simpa only [Fintype.card_fin] using rectangular_upper H hH hf

/-- The host graph has the usual s*t unordered edges. -/
theorem complete_edges (s t : ℕ) :
    (completeBipartiteGraph (Fin s) (Fin t)).edgeSet.ncard = s*t := by
  classical
  have he : incidence (fun _ : Fin t => (Finset.univ : Finset (Fin s))) =
      completeBipartiteGraph (Fin s) (Fin t) := by
    ext x y
    cases x <;> cases y <;> simp [incidence,completeBipartiteGraph]
  rw [← he, incidence_edges]
  simp [incidenceCount, Nat.mul_comm]

/-- Folkman's complete-bipartite obstruction, with its exact original statement. -/
theorem folkman (n : ℕ) :
    (completeBipartiteGraph (Fin n) (Fin (n^2))).edgeSet.ncard = n^3 ∧
    ∀ H ≤ completeBipartiteGraph (Fin n) (Fin (n^2)),
      n^2+n.choose 2 < H.edgeSet.ncard → cycleGraph 4 ⊑ H := by
  refine ⟨by rw [complete_edges]; ring, ?_⟩
  intro H hH hmany
  by_contra hfree
  have h := rectangular_upper H hH hfree
  simp only [Fintype.card_fin] at h
  omega

/-- The bound for the Folkman family is attained, not just asymptotically sharp. -/
theorem folkman_exact (n : ℕ) (hn : 0 < n) :
    (∃ H : SimpleGraph (Fin n ⊕ Fin (n^2)),
      H ≤ completeBipartiteGraph (Fin n) (Fin (n^2)) ∧
      (cycleGraph 4).Free H ∧ H.edgeSet.ncard = n^2+n.choose 2) ∧
    (∀ H : SimpleGraph (Fin n ⊕ Fin (n^2)),
      H ≤ completeBipartiteGraph (Fin n) (Fin (n^2)) →
      (cycleGraph 4).Free H → H.edgeSet.ncard ≤ n^2+n.choose 2) :=
  rectangular_exact n (n^2) hn (Nat.choose_le_pow n 2)

/-- A real-power identity lets the asymptotic obstruction use integer fourth powers. -/
theorem fourth_power_scale (k : ℕ) :
    (((k^4)^3 : ℕ) : ℝ) ^ (3/4 : ℝ) = (k : ℝ)^9 := by
  push_cast
  rw [← pow_mul]
  norm_num only [Nat.reduceMul]
  rw [← Real.rpow_natCast_mul (Nat.cast_nonneg k)]
  norm_num

/-- Every positive proposed constant fails on a concrete member of the Folkman family. -/
theorem no_uniform_three_quarters :
    ¬ ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∃ H ≤ G, (cycleGraph 4).Free H ∧
        c * (G.edgeSet.ncard : ℝ) ^ (3/4 : ℝ) ≤ (H.edgeSet.ncard : ℝ) := by
  rintro ⟨c,hc,h⟩
  obtain ⟨k,hk⟩ := exists_nat_gt (max (1 : ℝ) (2/c))
  have hk1 : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hck : 2 < c*(k : ℝ) := by
    have hlt := (le_max_right (1 : ℝ) (2/c)).trans_lt hk
    have hmul := (div_lt_iff₀ hc).mp hlt
    nlinarith
  obtain ⟨H,hH,hfree,hlarge⟩ := h (Fin (k^4) ⊕ Fin ((k^4)^2))
    (completeBipartiteGraph (Fin (k^4)) (Fin ((k^4)^2)))
  have hu := rectangular_upper H hH hfree
  simp only [Fintype.card_fin] at hu
  have hchoose := Nat.choose_le_pow (k^4) 2
  have hn : H.edgeSet.ncard ≤ 2*k^8 := by
    have hp : (k^4)^2 = k^8 := by ring
    omega
  have hur : (H.edgeSet.ncard : ℝ) ≤ 2*(k : ℝ)^8 := by exact_mod_cast hn
  rw [(folkman (k^4)).1, fourth_power_scale] at hlarge
  have hk8 : (0 : ℝ) < (k : ℝ)^8 := pow_pos (by linarith) _
  have hh := mul_lt_mul_of_pos_right hck hk8
  have hp : c*(k : ℝ)*(k : ℝ)^8 = c*(k : ℝ)^9 := by ring
  rw [hp] at hh
  linarith

/-- Direct logical form of the negative answer in the reference problem statement. -/
theorem three_quarters_answer : False ↔
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∃ H ≤ G, (cycleGraph 4).Free H ∧
        c * (G.edgeSet.ncard : ℝ) ^ (3/4 : ℝ) ≤ (H.edgeSet.ncard : ℝ) :=
  ⟨False.elim, no_uniform_three_quarters⟩

/-- A readable numerical instance, proved by the universal construction. -/
theorem ten_by_hundred_attained :
    ∃ H : SimpleGraph (Fin 10 ⊕ Fin 100),
      H ≤ completeBipartiteGraph (Fin 10) (Fin 100) ∧
      (cycleGraph 4).Free H ∧ H.edgeSet.ncard = 145 := by
  simpa [Nat.choose_two_right] using
    rectangular_attained 10 100 (by norm_num) (by norm_num [Nat.choose_two_right])

/-- No choice of a different subgraph can beat the displayed example. -/
theorem ten_by_hundred_upper (H : SimpleGraph (Fin 10 ⊕ Fin 100))
    (hH : H ≤ completeBipartiteGraph (Fin 10) (Fin 100))
    (hfree : (cycleGraph 4).Free H) : H.edgeSet.ncard ≤ 145 := by
  simpa [Nat.choose_two_right] using rectangular_upper H hH hfree

#print axioms incidence_le
#print axioms rectangle_copy
#print axioms pairUnique_of_free
#print axioms free_of_pairUnique
#print axioms sum_pairs_le
#print axioms degree_le_one_add_pairs
#print axioms incidence_upper
#print axioms incidence_degree
#print axioms incidence_edges
#print axioms incidence_neighbors
#print axioms rectangular_upper
#print axioms leftPair_card
#print axioms pairNeighbors_unique
#print axioms pairNeighbors_count
#print axioms pairUnique_reindex
#print axioms incidenceCount_reindex
#print axioms rectangular_attained
#print axioms rectangular_exact
#print axioms complete_edges
#print axioms folkman
#print axioms folkman_exact
#print axioms fourth_power_scale
#print axioms no_uniform_three_quarters
#print axioms three_quarters_answer
#print axioms ten_by_hundred_attained
#print axioms ten_by_hundred_upper

end Erdos1008
