import DynamicalCStarAlgebras.ValleePoussin

namespace DynamicalCStarAlgebras

universe u

/-- The invariant-subalgebra equality in Theorem A. -/
theorem continuityPoints_inter_eq_closure_finitePropagation {X : Type u} (h : X → ℝ)
    (A : NonUnitalStarSubalgebra ℂ (Operator X)) (hA : IsClosed (A : Set (Operator X)))
    (hinv : ∀ t a, a ∈ A → diagonalFlow h t a ∈ A) :
    continuityPoints h ∩ (A : Set (Operator X)) =
      closure {a : Operator X | @HasFinitePropagation X (realPullbackPseudoMetric h) a ∧ a ∈ A} := by
  apply Set.Subset.antisymm
  · exact fun a ha => continuityPoint_mem_closure_finitePropagation h A hA hinv a ha.1 ha.2
  · exact closure_minimal (fun a ha => ⟨finitePropagation_mem_continuityPoints h a ha.1, ha.2⟩)
      ((isClosed_continuityPoints h).inter hA)

theorem continuityPoints_eq_uniformRoe_pullback {X : Type u} (h : X → ℝ) :
    continuityPoints h = uniformRoe (@CoarseStructure.ofPseudoMetric X (realPullbackPseudoMetric h)) := by
  rw [@uniformRoe_metric_eq X (realPullbackPseudoMetric h)]
  simpa using continuityPoints_inter_eq_closure_finitePropagation h ⊤ isClosed_univ
    (fun _ _ _ => trivial)

/-- Theorem A, including the general invariant-subalgebra assertion. -/
theorem theoremA {X : Type u} (h : X → ℝ) :
    continuityPoints h = uniformRoe (@CoarseStructure.ofPseudoMetric X (realPullbackPseudoMetric h)) ∧
    ∀ A : NonUnitalStarSubalgebra ℂ (Operator X), IsClosed (A : Set (Operator X)) →
      (∀ t a, a ∈ A → diagonalFlow h t a ∈ A) →
      continuityPoints h ∩ (A : Set (Operator X)) =
        closure {a : Operator X | @HasFinitePropagation X (realPullbackPseudoMetric h) a ∧ a ∈ A} :=
  ⟨continuityPoints_eq_uniformRoe_pullback h, continuityPoints_inter_eq_closure_finitePropagation h⟩

end DynamicalCStarAlgebras
