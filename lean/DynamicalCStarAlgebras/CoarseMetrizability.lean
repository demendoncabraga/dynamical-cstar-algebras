import DynamicalCStarAlgebras.Coarse

/-! Metrizability in the sense of the coarse-geometry preliminaries,
`paper/main.tex:418`. This asks for a genuine metric on the same set. -/

namespace DynamicalCStarAlgebras

/-- A coarse structure is metrizable if it is the bounded-distance coarse structure
of some metric on its underlying set. -/
def CoarseStructure.IsMetrizable {X : Type*} (C : CoarseStructure X) : Prop :=
  ∃ d : MetricSpace X, C = @CoarseStructure.ofPseudoMetric X d.toPseudoMetricSpace

/-- The coarse structure associated to an actual metric is metrizable. -/
theorem CoarseStructure.ofMetric_isMetrizable (X : Type*) [MetricSpace X] :
    (CoarseStructure.ofPseudoMetric X).IsMetrizable :=
  ⟨inferInstance, rfl⟩

end DynamicalCStarAlgebras
