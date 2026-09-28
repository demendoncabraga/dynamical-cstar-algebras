import DynamicalCStarAlgebras.HaarUnitaryMoments
import Mathlib.Probability.Distributions.Gaussian.Multivariate

noncomputable section
open Classical MeasureTheory Set TopologicalSpace
namespace DynamicalCStarAlgebras

attribute [local instance] euclideanOperator_continuousStar

lemma exists_linearIsometryEquiv_apply_eq_of_norm_one {ι : Type*} [Fintype ι]
    (v w : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ∃ e : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι, e v = w := by
  let f := LinearIsometry.toSpanSingleton ℂ (EuclideanSpace ℂ ι) hv
  let g := LinearIsometry.toSpanSingleton ℂ (EuclideanSpace ℂ ι) hw
  let L := g.comp f.equivRange.symm.toLinearIsometry
  let e := LinearIsometryEquiv.ofSurjective L.extend
    (LinearMap.surjective_of_injective L.extend.injective)
  refine ⟨e, ?_⟩
  have hfv : f 1 = v := by simp [f, LinearIsometry.toSpanSingleton_apply]
  have he : e v = L (f.equivRange 1) := by
    change L.extend v = L (f.equivRange 1)
    rw [← hfv]
    exact L.extend_apply (f.equivRange 1)
  rw [he]
  simp [L, g, LinearIsometry.toSpanSingleton_apply]

instance euclideanUnitaryHaar_rightInvariant {ι : Type*} [Fintype ι] :
    (euclideanUnitaryHaar (ι := ι)).IsMulRightInvariant := by
  constructor
  intro U
  have he := Measure.haarMeasure_unique
    (Measure.map (fun V : EuclideanUnitary ι => V * U) euclideanUnitaryHaar)
    (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts (EuclideanUnitary ι))
  change Measure.map (fun V : EuclideanUnitary ι => V * U) euclideanUnitaryHaar =
    (Measure.map (fun V : EuclideanUnitary ι => V * U) euclideanUnitaryHaar) Set.univ •
      euclideanUnitaryHaar at he
  simpa only [Measure.map_apply (measurable_mul_const U) MeasurableSet.univ,
    Set.preimage_univ, measure_univ, one_smul] using he

lemma unitaryOrbitLaw_eq_of_norm_one {ι : Type*} [Fintype ι]
    (v w : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    unitaryOrbitLaw v = unitaryOrbitLaw w := by
  obtain ⟨e, he⟩ := exists_linearIsometryEquiv_apply_eq_of_norm_one v w hv hw
  let U := Unitary.linearIsometryEquiv.symm e
  have hU : (U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) v = w := he
  rw [← hU]
  change _ = Measure.map ((fun V : EuclideanUnitary ι =>
    (V : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) v) ∘ (fun V => V * U)) _
  rw [← Measure.map_map (measurable_unitary_apply v) (measurable_mul_const U),
    map_mul_right_eq_self]
  rfl

/-- A unitary-invariant probability measure on the unit sphere is the Haar orbit law. -/
theorem invariant_sphere_law_eq_unitaryOrbitLaw {ι : Type*} [Fintype ι]
    (μ : Measure (EuclideanSpace ℂ ι)) [IsProbabilityMeasure μ]
    (hunit : ∀ᵐ z ∂μ, ‖z‖ = 1)
    (hinv : ∀ e : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι, MeasurePreserving e μ μ)
    (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) : μ = unitaryOrbitLaw v := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hi (U : EuclideanUnitary ι) :
      (∫⁻ z, f ((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) z) ∂μ) = ∫⁻ z, f z ∂μ :=
    (hinv (Unitary.linearIsometryEquiv U)).lintegral_comp hf
  have hmeas : Measurable (fun p : EuclideanUnitary ι × EuclideanSpace ℂ ι =>
      f ((p.1 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) p.2)) :=
    hf.comp ((continuous_subtype_val.comp continuous_fst).clm_apply continuous_snd).measurable
  calc
    _ = ∫⁻ U : EuclideanUnitary ι, ∫⁻ z, f ((U : EuclideanSpace ℂ ι →L[ℂ]
        EuclideanSpace ℂ ι) z) ∂μ ∂euclideanUnitaryHaar := by simp only [hi, lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ z, ∫⁻ U : EuclideanUnitary ι, f ((U : EuclideanSpace ℂ ι →L[ℂ]
        EuclideanSpace ℂ ι) z) ∂euclideanUnitaryHaar ∂μ := lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ _z, (∫⁻ w, f w ∂unitaryOrbitLaw v) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hunit] with z hz
      rw [← lintegral_map hf (measurable_unitary_apply z)]
      change (∫⁻ w, f w ∂unitaryOrbitLaw z) = _
      rw [unitaryOrbitLaw_eq_of_norm_one z v hz hv]
    _ = _ := by simp only [lintegral_const, measure_univ, mul_one]

/-- Radial normalization, defined to be zero at the origin. -/
def gaussianSphereNormalize {ι : Type*} [Fintype ι] (z : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι := ‖z‖⁻¹ • z

lemma measurable_gaussianSphereNormalize {ι : Type*} [Fintype ι] :
    Measurable (gaussianSphereNormalize (ι := ι)) :=
  measurable_norm.inv.smul measurable_id

lemma gaussianSphereNormalize_norm {ι : Type*} [Fintype ι]
    {z : EuclideanSpace ℂ ι} (hz : z ≠ 0) : ‖gaussianSphereNormalize z‖ = 1 := by
  rw [gaussianSphereNormalize, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]

lemma stdGaussian_ne_zero_ae {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    ∀ᵐ z ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℂ ι), z ≠ 0 := by
  let L : EuclideanSpace ℂ ι →L[ℝ] ℝ := innerSL ℝ v
  have hL : ‖L‖ = 1 := by simpa only [L, innerSL_apply_norm] using hv
  have hm : (ProbabilityTheory.stdGaussian (EuclideanSpace ℂ ι)).map L =
      ProbabilityTheory.gaussianReal 0 1 := by
    rw [ProbabilityTheory.IsGaussian.map_eq_gaussianReal,
      ProbabilityTheory.integral_strongDual_stdGaussian,
      ProbabilityTheory.variance_dual_stdGaussian, hL]
    norm_num
  let := ProbabilityTheory.nullSingletonClass_gaussianReal (μ := 0) (v := 1) (by norm_num)
  have hz : (ProbabilityTheory.stdGaussian (EuclideanSpace ℂ ι)) (L ⁻¹' {0}) = 0 := by
    rw [← Measure.map_apply L.continuous.measurable (measurableSet_singleton 0), hm]
    exact measure_singleton 0
  apply ae_iff.mpr
  apply measure_mono_null _ hz
  intro z hz
  simp only [Set.mem_ofPred_eq, not_not] at hz
  simp only [Set.mem_preimage, Set.mem_singleton_iff, hz, map_zero]

/-- The direction law of the standard Gaussian on the underlying real space. -/
def gaussianDirectionLaw {ι : Type*} [Fintype ι] : Measure (EuclideanSpace ℂ ι) :=
  Measure.map gaussianSphereNormalize (ProbabilityTheory.stdGaussian (EuclideanSpace ℂ ι))

instance gaussianDirectionLaw_probability {ι : Type*} [Fintype ι] :
    IsProbabilityMeasure (gaussianDirectionLaw (ι := ι)) :=
  Measure.isProbabilityMeasure_map measurable_gaussianSphereNormalize.aemeasurable

lemma gaussianDirectionLaw_norm_one {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    ∀ᵐ z ∂gaussianDirectionLaw (ι := ι), ‖z‖ = 1 := by
  apply (ae_map_iff measurable_gaussianSphereNormalize.aemeasurable (by measurability)).mpr
  exact (stdGaussian_ne_zero_ae v hv).mono fun _ hz => gaussianSphereNormalize_norm hz

lemma gaussianDirectionLaw_isometryInvariant {ι : Type*} [Fintype ι]
    (e : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι) :
    MeasurePreserving e gaussianDirectionLaw gaussianDirectionLaw := by
  let eR : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι :=
    { e.toLinearEquiv.restrictScalars ℝ with norm_map' := e.norm_map }
  have he : (e : EuclideanSpace ℂ ι → EuclideanSpace ℂ ι) ∘ gaussianSphereNormalize =
      gaussianSphereNormalize ∘ eR := by
    funext z
    change eR (‖z‖⁻¹ • z) = ‖eR z‖⁻¹ • eR z
    rw [eR.map_smul, eR.norm_map]
  refine ⟨e.continuous.measurable, ?_⟩
  rw [gaussianDirectionLaw,
    Measure.map_map e.continuous.measurable measurable_gaussianSphereNormalize, he,
    ← Measure.map_map measurable_gaussianSphereNormalize eR.continuous.measurable,
    ProbabilityTheory.stdGaussian_map]

/-- The normalized real Gaussian has exactly the Haar-unitary orbit distribution. -/
theorem gaussianDirectionLaw_eq_unitaryOrbitLaw {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    gaussianDirectionLaw = unitaryOrbitLaw v :=
  invariant_sphere_law_eq_unitaryOrbitLaw gaussianDirectionLaw
    (gaussianDirectionLaw_norm_one v hv) gaussianDirectionLaw_isometryInvariant v hv

end DynamicalCStarAlgebras
