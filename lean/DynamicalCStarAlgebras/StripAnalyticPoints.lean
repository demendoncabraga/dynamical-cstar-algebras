import DynamicalCStarAlgebras.StripExponentialDecay

noncomputable section

namespace DynamicalCStarAlgebras

/-- Definition Defi.AP_band: norm closure after intersection over all coarse real maps. -/
def stripAnalyticPoints {X : Type*} (C : CoarseStructure X) : Set (Operator X) :=
  closure {a | ∀ h : X → ℝ, IsCoarseReal C h →
    ∃ δ : ℝ, 0 < δ ∧ ∃ F, IsStripExtension h a δ F}

/-- The forward inclusion of Theorem E, equivalently the conclusion of Thm.Band.In.Led. -/
theorem stripAnalyticPoints_subset_exponentialQuasiLocal {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) :
    stripAnalyticPoints (CoarseStructure.ofPseudoMetric X) ⊆ exponentialQuasiLocal :=
  closure_mono fun a ha => strip_analytic_hasExponentialDecay hX a
    (fun h hh => ha h (lipschitz_isCoarseReal hh))

end DynamicalCStarAlgebras
