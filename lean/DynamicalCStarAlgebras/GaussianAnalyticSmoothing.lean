import DynamicalCStarAlgebras.GenericContinuity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

noncomputable section
open MeasureTheory Filter Complex
open scoped Topology

namespace DynamicalCStarAlgebras

/-- A complex Gaussian translated by its analytic parameter. -/
def gaussianTranslateKernel (z : ℂ) (t : ℝ) : ℂ := Complex.exp (-((t : ℂ) - z) ^ 2)

lemma gaussianTranslateKernel_bound {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) (t : ℝ) :
    ‖gaussianTranslateKernel z t‖ ≤ Real.exp (2 * R ^ 2) * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
  rw [gaussianTranslateKernel, Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hr : z.re ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg z.re) hR).mpr ((Complex.abs_re_le_norm z).trans hz)
  have hi : z.im ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg z.im) hR).mpr ((Complex.abs_im_le_norm z).trans hz)
  simp only [neg_re, pow_two, mul_re, sub_re, ofReal_re, sub_im, ofReal_im, zero_sub,
    neg_mul, mul_neg, neg_neg]
  nlinarith [sq_nonneg (t - 2 * z.re)]

lemma gaussianTranslateKernel_hasDerivAt (z : ℂ) (t : ℝ) :
    HasDerivAt (fun w => gaussianTranslateKernel w t)
      ((2 * ((t : ℂ) - z)) * gaussianTranslateKernel z t) z := by
  have h := (((hasDerivAt_const z (t : ℂ)).sub (hasDerivAt_id z)).pow 2).neg.cexp
  simpa [gaussianTranslateKernel, mul_comm] using h

lemma gaussianTranslateKernel_integrable (z : ℂ) : Integrable (gaussianTranslateKernel z) := by
  have h := integrable_cexp_quadratic (b := (1 : ℂ)) (by norm_num) (2 * z) (-z ^ 2)
  convert h using 1
  ext t
  change Complex.exp _ = Complex.exp _
  congr 1
  ring

lemma gaussian_smoothing_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (hf : Continuous f) {M : ℝ} (hbound : ∀ t, ‖f t‖ ≤ M)
    (z : ℂ) : Integrable (fun t : ℝ => gaussianTranslateKernel z t • f t) := by
  apply ((gaussianTranslateKernel_integrable z).norm.mul_const M).mono'
  · exact ((by unfold gaussianTranslateKernel; fun_prop : Continuous (gaussianTranslateKernel z)).smul hf).aestronglyMeasurable
  · filter_upwards with t
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hbound t) (norm_nonneg _)

lemma gaussian_derivative_majorant_integrable (R M : ℝ) :
    Integrable (fun t : ℝ => (2 * Real.exp (2 * R ^ 2) * M) *
      ((‖t‖ + R) * Real.exp (-(1 / 2 : ℝ) * t ^ 2))) := by
  have hg := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  have ht : Integrable (fun t : ℝ => ‖t‖ * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) := by
    simpa only [norm_mul, Real.norm_eq_abs, Real.abs_exp] using
      (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).norm
  simpa only [add_mul, Pi.add_apply] using (ht.add (hg.const_mul R)).const_mul (2 * Real.exp (2 * R ^ 2) * M)

lemma gaussian_smoothing_derivative_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) {M R : ℝ} (hR : 0 ≤ R) (hbound : ∀ t, ‖f t‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ R) (t : ℝ) :
    ‖((2 * ((t : ℂ) - z)) * gaussianTranslateKernel z t) • f t‖ ≤
      (2 * Real.exp (2 * R ^ 2) * M) * ((‖t‖ + R) * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) := by
  have ht : ‖(t : ℂ) - z‖ ≤ ‖t‖ + R := by
    simpa only [Complex.norm_real] using (norm_sub_le (t : ℂ) z).trans
      (add_le_add le_rfl hz)
  rw [norm_smul, norm_mul, norm_mul, Complex.norm_ofNat]
  calc
    _ ≤ 2 * (‖t‖ + R) * (Real.exp (2 * R ^ 2) * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) * M := by
      gcongr
      · exact gaussianTranslateKernel_bound hR hz t
      · exact hbound t
    _ = _ := by ring

/-- Gaussian convolution of a bounded continuous Banach-space-valued function
extends to an entire function of the translated complex parameter. -/
theorem gaussian_smoothing_entire {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (f : ℝ → E) (hf : Continuous f) {M : ℝ} (hbound : ∀ t, ‖f t‖ ≤ M) :
    Differentiable ℂ (fun z : ℂ => ∫ t : ℝ, gaussianTranslateKernel z t • f t) := by
  intro z₀
  let R := ‖z₀‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hlocal {z : ℂ} (hz : z ∈ Metric.ball z₀ 1) : ‖z‖ ≤ R := by
    have hdist : ‖z - z₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
    have hnorm := norm_sub_norm_le z z₀
    dsimp [R]
    linarith
  have hmeas (z : ℂ) : AEStronglyMeasurable (fun t : ℝ => gaussianTranslateKernel z t • f t) := by
    exact ((by unfold gaussianTranslateKernel; fun_prop : Continuous (gaussianTranslateKernel z)).smul
      hf).aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable (fun t : ℝ =>
      ((2 * ((t : ℂ) - z₀)) * gaussianTranslateKernel z₀ t) • f t) := by
    apply Continuous.aestronglyMeasurable
    unfold gaussianTranslateKernel
    fun_prop
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => gaussianTranslateKernel z t • f t)
    (F' := fun z t => ((2 * ((t : ℂ) - z)) * gaussianTranslateKernel z t) • f t)
    (bound := fun t : ℝ => (2 * Real.exp (2 * R ^ 2) * M) *
      ((‖t‖ + R) * Real.exp (-(1 / 2 : ℝ) * t ^ 2)))
    (Metric.ball_mem_nhds z₀ (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall hmeas) (gaussian_smoothing_integrable f hf hbound z₀) hdmeas
    (Filter.Eventually.of_forall (fun t z hz =>
      gaussian_smoothing_derivative_bound f hR hbound (hlocal hz) t))
    (gaussian_derivative_majorant_integrable R M)
    (Filter.Eventually.of_forall (fun t z _ =>
      (gaussianTranslateKernel_hasDerivAt z t).smul_const (f t)))).2.differentiableAt

end DynamicalCStarAlgebras
