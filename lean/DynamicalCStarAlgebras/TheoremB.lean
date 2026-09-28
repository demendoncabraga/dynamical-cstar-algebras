import DynamicalCStarAlgebras.SeparatedBlockSelection

namespace DynamicalCStarAlgebras

/-- A non-quasi-local operator on a uniformly locally finite metric space is
not a continuity point for some coarse real flow. The witness is even 1-Lipschitz. -/
theorem nonQuasiLocal_coarse_discontinuous {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) (a : Operator X)
    (ha : a ∉ quasiLocal (CoarseStructure.ofPseudoMetric X)) :
    ∃ h : X → ℝ, IsCoarseReal (CoarseStructure.ofPseudoMetric X) h ∧
      a ∉ continuityPoints h := by
  obtain ⟨ε, A, B, hε, _, hnorm, hself, hsep⟩ := nonQuasiLocal_separated_blocks hX a ha
  obtain ⟨h, _, hh, hbad⟩ := separated_blocks_detect_discontinuity a A B hε hnorm hself hsep
  exact ⟨h, hh, hbad⟩

/-- The dynamical characterization of the quasi-local algebra. -/
theorem quasiLocal_eq_coarseContinuityPoints {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) :
    quasiLocal (CoarseStructure.ofPseudoMetric X) =
      coarseContinuityPoints (CoarseStructure.ofPseudoMetric X) := by
  refine Set.Subset.antisymm (quasiLocal_subset_coarseContinuityPoints _) fun a ha => ?_
  by_contra hbad
  obtain ⟨h, hh, hnot⟩ := nonQuasiLocal_coarse_discontinuous hX a hbad
  exact hnot (ha h hh)

/-- Theorem B: dynamical characterizations of the quasi-local and uniform Roe algebras,
including the entire-analytic characterization under exponential volume growth. -/
theorem theoremB {X : Type*} [MetricSpace X] (hX : UniformlyLocallyFinite X) :
    (quasiLocal (CoarseStructure.ofPseudoMetric X) =
      coarseContinuityPoints (CoarseStructure.ofPseudoMetric X)) ∧
    (uniformRoe (CoarseStructure.ofPseudoMetric X) =
      exponentialAnalyticPoints (CoarseStructure.ofPseudoMetric X)) ∧
    (AtMostExponentialGrowth X → uniformRoe (CoarseStructure.ofPseudoMetric X) =
      entireAnalyticPoints (CoarseStructure.ofPseudoMetric X)) :=
  ⟨quasiLocal_eq_coarseContinuityPoints hX, uniformRoe_eq_exponentialAnalyticPoints,
    uniformRoe_eq_entireAnalyticPoints_of_exponentialGrowth⟩

end DynamicalCStarAlgebras
