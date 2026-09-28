import DynamicalCStarAlgebras.RoeContinuity

namespace DynamicalCStarAlgebras

universe u

/-- The common continuity points of every coarse real-valued diagonal pre-flow. -/
def coarseContinuityPoints {X : Type u} (C : CoarseStructure X) : Set (Operator X) :=
  {a | ∀ h : X → ℝ, IsCoarseReal C h → a ∈ continuityPoints h}

noncomputable def coarseContinuityPointsStarSubalgebra {X : Type u} (C : CoarseStructure X) :
    StarSubalgebra ℂ (Operator X) :=
  ⨅ h : {h : X → ℝ // IsCoarseReal C h}, continuityPointsStarSubalgebra h.val

theorem coe_coarseContinuityPointsStarSubalgebra {X : Type u} (C : CoarseStructure X) :
    (coarseContinuityPointsStarSubalgebra C : Set (Operator X)) = coarseContinuityPoints C := by
  ext a
  simp only [coarseContinuityPointsStarSubalgebra, StarSubalgebra.coe_iInf,
    coe_continuityPointsStarSubalgebra, Set.mem_iInter, coarseContinuityPoints,
    Set.mem_ofPred_eq, Subtype.forall]

theorem coarseContinuityPointsStarSubalgebra_isClosed {X : Type u} (C : CoarseStructure X) :
    IsClosed (coarseContinuityPointsStarSubalgebra C : Set (Operator X)) := by
  rw [coarseContinuityPointsStarSubalgebra, StarSubalgebra.coe_iInf]
  exact isClosed_iInter fun _h => continuityPointsStarSubalgebra_isClosed _

theorem uniformRoe_subset_coarseContinuityPoints {X : Type u} (C : CoarseStructure X) :
    uniformRoe C ⊆ coarseContinuityPoints C := by
  intro a ha h hh
  exact uniformRoe_restrictReal_subset_continuityPoints C h
    (uniformRoe_mono (show C.IsSubstructure (C.restrictReal h) from
      fun E hE => ⟨hE, hh E hE⟩) ha)

end DynamicalCStarAlgebras
