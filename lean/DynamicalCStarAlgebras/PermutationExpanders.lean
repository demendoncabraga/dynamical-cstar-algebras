import DynamicalCStarAlgebras.GraphExpansion
import Mathlib

/-!
Adapted from the checked finite counting construction in
the same-author sibling paper-formalization project, specifically
`propertyH_lean/lean/PropertyH/PermutationExpanders.lean`. The expander predicate is adapted from `PropertyH/Expanders.lean`. The proofs below are included in full and checked with this repository's
Lean/Mathlib pins; no declaration from the sibling project is imported.
-/

noncomputable section
namespace DynamicalCStarAlgebras.PermutationExpanders

/-- Positive vertex expansion together with a uniform graph-degree bound. -/
def IsVertexExpander {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : ℝ) : Prop :=
  0 < h ∧ (∀ v, (G.neighborSet v).ncard ≤ k) ∧
    ∀ A : Finset V, 2 * A.card ≤ Fintype.card V →
      h * (A.card : ℝ) ≤ (({v | v ∉ A ∧ ∃ u ∈ A, G.Adj v u} : Set V).ncard : ℝ)


/-- The simple graph underlying finitely many permutation edges; loops are discarded. -/
def permutationGraph {V I : Type*} (σ : I → Equiv.Perm V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ i, σ i u = v ∨ σ i v = u
  symm := ⟨fun u v h => ⟨h.1.symm, by obtain ⟨i, hi⟩ := h.2; exact ⟨i, hi.symm⟩⟩⟩
  loopless := ⟨fun v h => h.1 rfl⟩

/-- A union of d permutation edges has maximum degree at most 2d. -/
theorem permutationGraph_degree_le {V I : Type*} [Fintype V] [Fintype I]
    (σ : I → Equiv.Perm V) (v : V) :
    ((permutationGraph σ).neighborSet v).ncard ≤ 2 * Fintype.card I := by
  classical
  let S : Finset V := (Finset.univ.image fun i => σ i v) ∪ (Finset.univ.image fun i => (σ i).symm v)
  have hsub : (permutationGraph σ).neighborSet v ⊆ (S : Set V) := by
    intro u hu
    obtain ⟨_, i, hi⟩ := hu
    rcases hi with hi | hi
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (σ i).symm_apply_eq.mpr hi.symm⟩)
  have hn := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset] at hn
  have hu := Finset.card_union_le (Finset.univ.image fun i => σ i v)
    (Finset.univ.image fun i => (σ i).symm v)
  have h1 := Finset.card_image_le (s := (Finset.univ : Finset I)) (f := fun i => σ i v)
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset I)) (f := fun i => (σ i).symm v)
  simp only [Finset.card_univ] at h1 h2
  change ((permutationGraph σ).neighborSet v).ncard ≤ _
  dsimp [S] at hn
  omega

/-- Forward permutation images outside A are part of the graph's vertex boundary. -/
theorem forward_boundary_subset {V I : Type*} (σ : I → Equiv.Perm V) (A : Finset V) :
    {v | v ∉ A ∧ ∃ i, ∃ u ∈ A, σ i u = v} ⊆
      {v | v ∉ A ∧ ∃ u ∈ A, (permutationGraph σ).Adj v u} := by
  rintro v ⟨hv, i, u, hu, heq⟩
  exact ⟨hv, u, hu, (fun h => hv (h ▸ hu)), i, Or.inr heq⟩

/-- Directed image expansion is enough for the undirected bounded-degree model. -/
theorem isVertexExpander_of_forward {V I : Type*} [Fintype V] [Fintype I]
    (σ : I → Equiv.Perm V) (h : ℝ) (hh : 0 < h)
    (hex : ∀ A : Finset V, 2 * A.card ≤ Fintype.card V →
      h * (A.card : ℝ) ≤ ({v | v ∉ A ∧ ∃ i, ∃ u ∈ A, σ i u = v} : Set V).ncard) :
    IsVertexExpander (permutationGraph σ) (2 * Fintype.card I) h := by
  refine ⟨hh, permutationGraph_degree_le σ, fun A hA => ?_⟩
  exact (hex A hA).trans (by exact_mod_cast Set.ncard_le_ncard (forward_boundary_subset σ A))

/-- For a fixed pair of sets, all permutation choices are counted independently. -/
theorem card_permutation_families_into {V : Type*} [Fintype V] [DecidableEq V]
    (d : ℕ) (A B : Finset V) :
    (Finset.univ.filter fun σ : Fin d → Equiv.Perm V => ∀ i, ∀ u ∈ A, σ i u ∈ B).card =
      (Finset.univ.filter fun σ : Equiv.Perm V => ∀ u ∈ A, σ u ∈ B).card ^ d := by
  classical
  let S := Finset.univ.filter fun σ : Equiv.Perm V => ∀ u ∈ A, σ u ∈ B
  have heq : (Finset.univ.filter fun σ : Fin d → Equiv.Perm V => ∀ i, ∀ u ∈ A, σ i u ∈ B) =
      Fintype.piFinset (fun _ : Fin d => S) := by
    ext σ
    simp [S]
  rw [heq, Fintype.card_piFinset]
  simp [S]

/-- Union bound for families trapped in any one of a finite list of vertex cuts. -/
theorem card_bad_permutation_families_le {V : Type*} [Fintype V] [DecidableEq V]
    (d : ℕ) (cuts : Finset (Finset V × Finset V)) :
    (Finset.univ.filter fun σ : Fin d → Equiv.Perm V =>
      ∃ P ∈ cuts, ∀ i, ∀ u ∈ P.1, σ i u ∈ P.2).card ≤
        ∑ P ∈ cuts, (Finset.univ.filter fun σ : Equiv.Perm V =>
          ∀ u ∈ P.1, σ u ∈ P.2).card ^ d := by
  classical
  have heq : (Finset.univ.filter fun σ : Fin d → Equiv.Perm V =>
      ∃ P ∈ cuts, ∀ i, ∀ u ∈ P.1, σ i u ∈ P.2) =
      cuts.biUnion (fun P => Finset.univ.filter fun σ : Fin d → Equiv.Perm V =>
        ∀ i, ∀ u ∈ P.1, σ i u ∈ P.2) := by
    ext σ
    simp
  rw [heq]
  exact Finset.card_biUnion_le.trans_eq (Finset.sum_congr rfl (fun P _ =>
    card_permutation_families_into d P.1 P.2))

/-- A strict finite counting bound produces a family avoiding every forbidden cut. -/
theorem exists_permutation_family_avoiding {V : Type*} [Fintype V] [DecidableEq V]
    (d : ℕ) (cuts : Finset (Finset V × Finset V))
    (hcount : (∑ P ∈ cuts, (Finset.univ.filter fun σ : Equiv.Perm V =>
      ∀ u ∈ P.1, σ u ∈ P.2).card ^ d) < (Fintype.card V).factorial ^ d) :
    ∃ σ : Fin d → Equiv.Perm V, ∀ P ∈ cuts, ∃ i, ∃ u ∈ P.1, σ i u ∉ P.2 := by
  classical
  have hlt := (card_bad_permutation_families_le d cuts).trans_lt hcount
  have htot : (Finset.univ : Finset (Fin d → Equiv.Perm V)).card =
      (Fintype.card V).factorial ^ d := by simp [Fintype.card_perm]
  rw [← htot] at hlt
  obtain ⟨σ, _, hσ⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨σ, ?_⟩
  simpa using hσ

/-- Escaping every set of size less than 3|A|/2 ensures expansion by 1/2. -/
theorem isVertexExpander_of_escape {V I : Type*} [Fintype V] [Fintype I]
    [DecidableEq V] (σ : I → Equiv.Perm V)
    (hescape : ∀ A B : Finset V, 0 < A.card → 2 * A.card ≤ Fintype.card V →
      A ⊆ B → 2 * B.card < 3 * A.card → ∃ i, ∃ u ∈ A, σ i u ∉ B) :
    IsVertexExpander (permutationGraph σ) (2 * Fintype.card I) (1/2) := by
  classical
  apply isVertexExpander_of_forward σ (1/2) (by norm_num)
  intro A hA
  let F := Finset.univ.filter fun v => v ∉ A ∧ ∃ i, ∃ u ∈ A, σ i u = v
  have hF : ({v | v ∉ A ∧ ∃ i, ∃ u ∈ A, σ i u = v} : Set V) = (F : Set V) := by
    ext v
    simp [F]
  rw [hF, Set.ncard_coe_finset]
  by_contra! hf
  have hpos : 0 < A.card := by
    by_contra! hzero
    have hz : A.card = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero] at hf
    exact (not_lt_of_ge (Nat.cast_nonneg F.card)) hf
  have hdis : Disjoint A F := by
    apply Finset.disjoint_left.mpr
    intro v hv hvF
    exact (Finset.mem_filter.mp hvF).2.1 hv
  have hcard : (A ∪ F).card = A.card + F.card := Finset.card_union_of_disjoint hdis
  have hsmall : 2 * (A ∪ F).card < 3 * A.card := by
    rw [hcard]
    have hh : (2 : ℝ) * F.card < A.card := by linarith
    have hn : 2 * F.card < A.card := by exact_mod_cast hh
    omega
  obtain ⟨i, u, hu, hnot⟩ := hescape A (A ∪ F) hpos hA (Finset.subset_union_left) hsmall
  apply hnot
  by_cases him : σ i u ∈ A
  · exact Finset.mem_union_left _ him
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, him, i, u, hu, rfl⟩)
end DynamicalCStarAlgebras.PermutationExpanders
