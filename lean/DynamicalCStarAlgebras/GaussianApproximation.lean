import DynamicalCStarAlgebras.GaussianAnalyticSmoothing

noncomputable section
open MeasureTheory Filter Complex
open scoped Topology
namespace DynamicalCStarAlgebras

lemma gaussianTranslateKernel_zero (t : ℝ) :
    gaussianTranslateKernel 0 t = (Real.exp (-t ^ 2) : ℂ) := by
  simp [gaussianTranslateKernel, Complex.ofReal_exp]

lemma integral_gaussianTranslateKernel_zero :
    (∫ t : ℝ, gaussianTranslateKernel 0 t) = (Real.sqrt Real.pi : ℂ) := by
  simp only [gaussianTranslateKernel_zero, integral_complex_ofReal]
  congr 1
  simpa using integral_gaussian (1 : ℝ)

/-- Normalized Gaussian averages of a bounded continuous function at shrinking
scales converge to its value at zero. -/
theorem gaussian_smoothing_approximation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℝ → E) (hf : Continuous f)
    {M : ℝ} (hbound : ∀ t, ‖f t‖ ≤ M) :
    Tendsto (fun n : ℕ => (Real.sqrt Real.pi : ℂ)⁻¹ •
      ∫ t : ℝ, gaussianTranslateKernel 0 t • f (t / ((n : ℝ) + 1))) atTop (𝓝 (f 0)) := by
  have hlim := tendsto_integral_of_dominated_convergence
    (fun t : ℝ => ‖gaussianTranslateKernel 0 t‖ * M)
    (F := fun n : ℕ => fun t : ℝ =>
      gaussianTranslateKernel 0 t • f (t / ((n : ℝ) + 1)))
    (f := fun t : ℝ => gaussianTranslateKernel 0 t • f 0)
    (fun n => (gaussian_smoothing_integrable (fun t => f (t / ((n : ℝ) + 1)))
      (hf.comp (by fun_prop)) (fun t => hbound _) 0).aestronglyMeasurable)
    ((gaussianTranslateKernel_integrable 0).norm.mul_const M)
    (fun n => Filter.Eventually.of_forall (fun t => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)))
    (Filter.Eventually.of_forall (fun t => by
      have ht : Tendsto (fun n : ℕ => t / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        simpa only [mul_one_div, mul_zero] using
          (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) :
            Tendsto (fun n : ℕ => t * (1 / ((n : ℝ) + 1))) atTop (𝓝 (t * 0)))
      exact tendsto_const_nhds.smul (hf.continuousAt.tendsto.comp ht)))
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 Real.pi_pos))
  simpa only [integral_smul_const, integral_gaussianTranslateKernel_zero,
    smul_smul, inv_mul_cancel₀ hπ, one_smul] using
    (tendsto_const_nhds.smul hlim : Tendsto
      (fun n : ℕ => (Real.sqrt Real.pi : ℂ)⁻¹ •
        ∫ t : ℝ, gaussianTranslateKernel 0 t • f (t / ((n : ℝ) + 1))) atTop
      (𝓝 ((Real.sqrt Real.pi : ℂ)⁻¹ • ∫ t : ℝ, gaussianTranslateKernel 0 t • f 0)))

end DynamicalCStarAlgebras
