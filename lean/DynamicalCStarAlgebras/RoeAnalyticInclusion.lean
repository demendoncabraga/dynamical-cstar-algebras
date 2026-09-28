import DynamicalCStarAlgebras.EntireCharacterization

noncomputable section

namespace DynamicalCStarAlgebras

universe u

/-- The forward direction of Theorem thm:roeentire holds for every coarse space. -/
theorem HasControlledPropagation.isEntireExponentialType {X : Type u} {C : CoarseStructure X}
    {a : Operator X} (ha : HasControlledPropagation C a) {h : X → ℝ} (hh : IsCoarseReal C h) :
    IsEntireExponentialType h a :=
  finitePropagation_isEntireExponentialType h a
    ((@controlled_iff_finitePropagation X (realPullbackPseudoMetric h) a).mp (hh _ ha))

/-- The uniform Roe-to-AP_exp inclusion in Theorem B, with arbitrary coarse-space generality. -/
theorem uniformRoe_subset_exponentialAnalyticPoints {X : Type u} (C : CoarseStructure X) :
    uniformRoe C ⊆ exponentialAnalyticPoints C :=
  closure_mono fun _ ha _ hh => ha.isEntireExponentialType hh

end DynamicalCStarAlgebras
