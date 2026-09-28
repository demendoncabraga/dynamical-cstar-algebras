import DynamicalCStarAlgebras.ExpanderGraphUnion

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- Two maps are close when their pointwise pairs form a controlled relation. -/
def CoarseClose {X Y : Type*} (D : CoarseStructure Y) (f g : X → Y) : Prop :=
  Set.range (fun x => (f x, g x)) ∈ D.controlled

/-- The coarse-equivalence definition of Section 2.1. -/
def AreCoarselyEquivalent {X Y : Type*} (C : CoarseStructure X)
    (D : CoarseStructure Y) : Prop :=
  ∃ (f : X → Y) (g : Y → X), IsCoarseMap C D f ∧ IsCoarseMap D C g ∧
    CoarseClose C id (g ∘ f) ∧ CoarseClose D id (f ∘ g)

/-- A coarse equivalence for which the forward map can be chosen bijective. -/
def AreBijectivelyCoarselyEquivalent {X Y : Type*} (C : CoarseStructure X)
    (D : CoarseStructure Y) : Prop :=
  ∃ (f : X → Y) (g : Y → X), Function.Bijective f ∧ IsCoarseMap C D f ∧
    IsCoarseMap D C g ∧ CoarseClose C id (g ∘ f) ∧ CoarseClose D id (f ∘ g)

/-- A bijective coarse equivalence is a coarse equivalence in the manuscript's sense. -/
theorem AreBijectivelyCoarselyEquivalent.coarselyEquivalent {X Y : Type*}
    {C : CoarseStructure X} {D : CoarseStructure Y}
    (h : AreBijectivelyCoarselyEquivalent C D) : AreCoarselyEquivalent C D := by
  obtain ⟨f, g, _, hf, hg, hleft, hright⟩ := h
  exact ⟨f, g, hf, hg, hleft, hright⟩

/-- A countable partition into finite metric components with the separation
condition of Section 2.3. Its component metrics are the restrictions of the ambient metric. -/
structure CoarseDisjointUnion (X : Type*) [PseudoMetricSpace X] where
  component : X → ℕ
  finite : ∀ n, Finite {x : X // component x = n}
  separated : ∀ r : ℝ, ∃ N : ℕ, ∀ x y : X,
    component x ≠ component y → N ≤ component x + component y → r ≤ dist x y

/-- A map preserving internal component distances is coarse, independently of
its behavior on the finitely many close pairs from distinct components. -/
theorem CoarseDisjointUnion.isCoarseMap_of_componentwise_isometry
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (D : CoarseDisjointUnion X) (f : X → Y)
    (hf : ∀ x y, D.component x = D.component y → dist (f x) (f y) = dist x y) :
    IsCoarseMap (CoarseStructure.ofPseudoMetric X) (CoarseStructure.ofPseudoMetric Y) f := by
  intro E hE
  obtain ⟨R, hR⟩ := hE
  obtain ⟨N, hN⟩ := D.separated (R + 1)
  let F : Set X := ⋃ n ∈ (Finset.range N : Set ℕ), {x | D.component x = n}
  have hF : F.Finite := (Finset.range N).finite_toSet.biUnion
    (fun n _ => @Set.toFinite X {x | D.component x = n} (D.finite n))
  obtain ⟨M, hM⟩ := ((hF.prod hF).image (fun p : X × X => dist (f p.1) (f p.2))).bddAbove
  refine ⟨max R M, ?_⟩
  rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
  by_cases hc : D.component x = D.component y
  · exact (hf x y hc ▸ hR (x, y) hxy).trans (le_max_left R M)
  · have hsum : D.component x + D.component y < N := by
      by_contra hn
      have hs := hN x y hc (by omega)
      have hr := hR (x, y) hxy
      linarith
    have hmem (z : X) (hz : D.component z < N) : z ∈ F :=
      Set.mem_iUnion.mpr ⟨D.component z, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hz, rfl⟩⟩
    exact (hM ⟨(x, y), ⟨hmem x (by omega), hmem y (by omega)⟩, rfl⟩).trans (le_max_right R M)

/-- Any two coarse disjoint unions of the same finite metric spaces are bijectively
coarsely equivalent, including when some components are empty. -/
theorem CoarseDisjointUnion.bijectivelyCoarselyEquivalent
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (D : CoarseDisjointUnion X) (F : CoarseDisjointUnion Y) (e : X ≃ Y)
    (hcomponent : ∀ x, F.component (e x) = D.component x)
    (hdist : ∀ x y, D.component x = D.component y → dist (e x) (e y) = dist x y) :
    AreBijectivelyCoarselyEquivalent (CoarseStructure.ofPseudoMetric X)
      (CoarseStructure.ofPseudoMetric Y) ∧
    AreCoarselyEquivalent (CoarseStructure.ofPseudoMetric X) (CoarseStructure.ofPseudoMetric Y) := by
  have he : AreBijectivelyCoarselyEquivalent (CoarseStructure.ofPseudoMetric X)
      (CoarseStructure.ofPseudoMetric Y) := by
    refine ⟨e, e.symm, e.bijective, D.isCoarseMap_of_componentwise_isometry e hdist,
      F.isCoarseMap_of_componentwise_isometry e.symm ?_, ?_, ?_⟩
    · intro x y hxy
      have hc : D.component (e.symm x) = D.component (e.symm y) := by
        simpa only [← hcomponent, Equiv.apply_symm_apply] using hxy
      simpa only [Equiv.apply_symm_apply] using (hdist (e.symm x) (e.symm y) hc).symm
    · exact (CoarseStructure.ofPseudoMetric X).subset
        (by rintro _ ⟨x, rfl⟩; simp) (CoarseStructure.ofPseudoMetric X).diagonal
    · exact (CoarseStructure.ofPseudoMetric Y).subset
        (by rintro _ ⟨y, rfl⟩; simp) (CoarseStructure.ofPseudoMetric Y).diagonal
  exact ⟨he, he.coarselyEquivalent⟩

end DynamicalCStarAlgebras
