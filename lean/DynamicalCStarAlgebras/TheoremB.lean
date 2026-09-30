import DynamicalCStarAlgebras.BoundedDegreeEmbedding

namespace DynamicalCStarAlgebras

/-- Entire analyticity for every coarse real height characterizes the uniform Roe algebra
on every uniformly locally finite metric space, with no volume-growth assumption. -/
theorem uniformRoe_eq_entireAnalyticPoints {X : Type*} [MetricSpace X]
    (hX : UniformlyLocallyFinite X) :
    uniformRoe (CoarseStructure.ofPseudoMetric X) =
      entireAnalyticPoints (CoarseStructure.ofPseudoMetric X) := by
  obtain ⟨m, hm, he⟩ := exists_exponentialGrowth_metric hX
  have h := @uniformRoe_eq_entireAnalyticPoints_of_exponentialGrowth X m.toPseudoMetricSpace hm
  simpa only [he] using h

/-- Revised Theorem B: the two dynamical characterizations for all uniformly locally
finite metric spaces. -/
theorem theoremB {X : Type*} [MetricSpace X] (hX : UniformlyLocallyFinite X) :
    (quasiLocal (CoarseStructure.ofPseudoMetric X) =
      coarseContinuityPoints (CoarseStructure.ofPseudoMetric X)) ∧
    (uniformRoe (CoarseStructure.ofPseudoMetric X) =
      entireAnalyticPoints (CoarseStructure.ofPseudoMetric X)) :=
  ⟨quasiLocal_eq_coarseContinuityPoints hX, uniformRoe_eq_entireAnalyticPoints hX⟩

/-- Corollary after Theorem B: the common entire and exponential-type analytic
algebras coincide after taking norm closures. -/
theorem entireAnalyticPoints_eq_exponentialAnalyticPoints {X : Type*} [MetricSpace X]
    (hX : UniformlyLocallyFinite X) :
    entireAnalyticPoints (CoarseStructure.ofPseudoMetric X) =
      exponentialAnalyticPoints (CoarseStructure.ofPseudoMetric X) := by
  rw [← uniformRoe_eq_entireAnalyticPoints hX, uniformRoe_eq_exponentialAnalyticPoints]

end DynamicalCStarAlgebras
