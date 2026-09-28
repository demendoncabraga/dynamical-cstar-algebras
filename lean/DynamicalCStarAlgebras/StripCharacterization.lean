import DynamicalCStarAlgebras.CoarseGraphUnions

noncomputable section

namespace DynamicalCStarAlgebras

/-- Uniform Roe operators belong to the strip algebra for every coarse space. -/
theorem uniformRoe_subset_stripAnalyticPoints {X : Type*} (C : CoarseStructure X) :
    uniformRoe C ⊆ stripAnalyticPoints C := by
  apply closure_mono
  intro a ha h hh
  obtain ⟨F, hF, _⟩ := ha.isEntireExponentialType hh
  exact ⟨1, zero_lt_one, F, hF.onStrip 1⟩

/-- The reverse strip inclusion for exponentially decaying contractions on graph unions. -/
theorem exponential_contraction_mem_stripAnalyticPoints {X : Type*} [PseudoMetricSpace X]
    (D : CoarseGraphUnion X) (a : Operator X) (hnorm : ‖a‖ ≤ 1)
    (ha : HasExponentialDecay a) :
    a ∈ stripAnalyticPoints (CoarseStructure.ofPseudoMetric X) := by
  classical
  let inst (n : ℕ) : Fintype {x : X // D.component x = n} :=
    @Fintype.ofFinite _ (D.finite n)
  obtain ⟨c, hc, C, hC, hdecay⟩ := ha
  obtain ⟨b, _, hb, hbstrip⟩ := graph_blockDiagonal_part_mem_stripAnalyticPoints
    D.component D.graph D.connected D.dist_eq a hnorm hc hC.le
    (fun r hr => hdecay r hr.le)
  have hrem := uniformRoe_subset_stripAnalyticPoints (CoarseStructure.ofPseudoMetric X)
    (offBlock_mem_uniformRoe D.component a b
      (HasExponentialDecay.isQuasiLocal ⟨c, hc, C, hC, hdecay⟩) hb D.finite_separation)
  have hsum := (stripAnalyticPointsStarSubalgebra (CoarseStructure.ofPseudoMetric X)).add_mem
    hrem hbstrip
  simpa only [sub_add_cancel] using! hsum

/-- Scaling removes the contraction normalization in the graph reverse inclusion. -/
theorem HasExponentialDecay.mem_stripAnalyticPoints {X : Type*} [PseudoMetricSpace X]
    {a : Operator X} (ha : HasExponentialDecay a) (D : CoarseGraphUnion X) :
    a ∈ stripAnalyticPoints (CoarseStructure.ofPseudoMetric X) := by
  let t : ℝ := max 1 ‖a‖
  have ht : 0 < t := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let b : Operator X := ((t : ℂ)⁻¹) • a
  have hb : ‖b‖ ≤ 1 := by
    simp only [b, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    exact (inv_mul_le_iff₀ ht).mpr (by simpa only [mul_one] using le_max_right 1 ‖a‖)
  have hstrip := exponential_contraction_mem_stripAnalyticPoints D b hb (ha.smul _)
  have hscale := (stripAnalyticPointsStarSubalgebra (CoarseStructure.ofPseudoMetric X)).smul_mem
    hstrip (t : ℂ)
  simpa only [b, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ht.ne'), one_smul] using! hscale

/-- Theorem Led.In.Band: exponential quasi-locality is contained in AP_strip on graph unions. -/
theorem exponentialQuasiLocal_subset_stripAnalyticPoints {X : Type*} [PseudoMetricSpace X]
    (D : CoarseGraphUnion X) :
    exponentialQuasiLocal ⊆ stripAnalyticPoints (CoarseStructure.ofPseudoMetric X) :=
  closure_minimal (fun _ ha => ha.mem_stripAnalyticPoints D) isClosed_closure

/-- Theorem E, including the equality assertion for coarse disjoint unions of finite connected graphs. -/
theorem theoremE {X : Type*} [MetricSpace X] (hX : UniformlyLocallyFinite X) :
    stripAnalyticPoints (CoarseStructure.ofPseudoMetric X) ⊆ exponentialQuasiLocal ∧
      (Nonempty (CoarseGraphUnion X) →
        stripAnalyticPoints (CoarseStructure.ofPseudoMetric X) = exponentialQuasiLocal) :=
  ⟨stripAnalyticPoints_subset_exponentialQuasiLocal hX, fun ⟨D⟩ =>
    Set.Subset.antisymm (stripAnalyticPoints_subset_exponentialQuasiLocal hX)
      (exponentialQuasiLocal_subset_stripAnalyticPoints D)⟩

end DynamicalCStarAlgebras
