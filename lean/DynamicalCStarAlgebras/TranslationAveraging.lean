import DynamicalCStarAlgebras.FejerAverages

namespace DynamicalCStarAlgebras

open MeasureTheory Filter
open scoped Topology

universe u

theorem fourierPlus_translate (f : ℝ → ℂ) (r ξ : ℝ) :
    fourierPlus (fun t => f (t - r)) ξ =
      Complex.exp (((r * ξ : ℝ) : ℂ) * Complex.I) * fourierPlus f ξ := by
  have he (t : ℝ) : Complex.exp ((((t + r) * ξ : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((r * ξ : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((t * ξ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [add_mul, Complex.ofReal_add, add_comm]
  simpa only [fourierPlus, add_sub_cancel_right, he,
    mul_left_comm _ (Complex.exp (((r * ξ : ℝ) : ℂ) * Complex.I)), integral_const_mul] using
    (integral_add_right_eq_self
      (fun t : ℝ => f (t - r) * Complex.exp (((t * ξ : ℝ) : ℂ) * Complex.I)) r).symm

theorem diagonalFlow_averagingOperator {X : Type u} (h : X → ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) (r : ℝ) (a : Operator X) :
    diagonalFlow h r (averagingOperator h hf a) =
      averagingOperator h (hf.comp_sub_right r) a := by
  refine operator_ext fun x y => ?_
  simp only [matrixEntry_diagonalFlow, matrixEntry_averagingOperator, fourierPlus_translate,
    mul_assoc]

theorem averagingOperator_sub_kernel {X : Type u} (h : X → ℝ) {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (a : Operator X) :
    averagingOperator h (hf.sub hg) a = averagingOperator h hf a - averagingOperator h hg a := by
  apply ContinuousLinearMap.ext
  exact fun v => by
    simpa only [averagingOperator_apply, sub_apply, Pi.sub_apply, sub_smul] using integral_sub
      (integrable_diagonalFlow_smul h hf a v) (integrable_diagonalFlow_smul h hg a v)

theorem diagonalFlow_averagingOperator_sub_norm_le {X : Type u} (h : X → ℝ)
    {f : ℝ → ℂ} (hf : Integrable f) (r : ℝ) (a : Operator X) :
    ‖diagonalFlow h r (averagingOperator h hf a) - averagingOperator h hf a‖ ≤
      (∫ t, ‖f (t - r) - f t‖) * ‖a‖ := by
  rw [diagonalFlow_averagingOperator, ← averagingOperator_sub_kernel]
  exact averagingOperator_norm_le h ((hf.comp_sub_right r).sub hf) a

theorem shifted_inv_one_add_sq_bound {r : ℝ} (hr : |r| ≤ 1) (t : ℝ) :
    (1 + (t - r) ^ 2)⁻¹ ≤ 3 * (1 + t ^ 2)⁻¹ := by
  have hr2 : r ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one r).mpr hr
  have hb : 1 + t ^ 2 ≤ 3 * (1 + (t - r) ^ 2) := by
    nlinarith [sq_nonneg (t - 2 * r), sq_nonneg (t - r)]
  rw [← one_div (1 + (t - r) ^ 2), ← div_eq_mul_inv]
  exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hb)

theorem translated_kernel_norm_sub_bound {f : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ t, ‖f t‖ ≤ C * (1 + t ^ 2)⁻¹) {r : ℝ} (hr : |r| ≤ 1) (t : ℝ) :
    ‖f (t - r) - f t‖ ≤ (4 * C) * (1 + t ^ 2)⁻¹ := by
  have hb := mul_le_mul_of_nonneg_left (shifted_inv_one_add_sq_bound hr t) hC
  nlinarith [norm_sub_le (f (t - r)) (f t), hf (t - r), hf t]

theorem tendsto_integral_norm_translate_sub {f : ℝ → ℂ} (hc : Continuous f)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t, ‖f t‖ ≤ C * (1 + t ^ 2)⁻¹) :
    Tendsto (fun r : ℝ => ∫ t, ‖f (t - r) - f t‖) (𝓝 0) (𝓝 0) := by
  have hr : ∀ᶠ r : ℝ in 𝓝 0, |r| ≤ 1 := by
    simpa only [Metric.closedBall, Real.dist_eq, sub_zero] using!
      (Metric.closedBall_mem_nhds (0 : ℝ) zero_lt_one)
  have hl : Tendsto (fun r : ℝ => ∫ t, ‖f (t - r) - f t‖) (𝓝 0)
      (𝓝 (∫ _t : ℝ, (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => (4 * C) * (1 + t ^ 2)⁻¹) ?_ ?_
      (integrable_inv_one_add_sq.const_mul (4 * C)) ?_
    · exact Eventually.of_forall fun r =>
        (((hc.comp (continuous_id.sub continuous_const)).sub hc).norm).aestronglyMeasurable
    · exact hr.mono fun r hr => Eventually.of_forall fun t => by
        simpa only [norm_norm] using translated_kernel_norm_sub_bound hC hb hr t
    · exact Eventually.of_forall fun t => by
        have ht : Continuous (fun r : ℝ => ‖f (t - r) - f t‖) := by fun_prop
        simpa only [sub_zero, sub_self, norm_zero] using
          ht.tendsto (0 : ℝ)
  simpa only [integral_zero] using hl

theorem averagingOperator_mem_continuityPoints {X : Type u} (h : X → ℝ)
    {f : ℝ → ℂ} (hf : Integrable f) (hc : Continuous f) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t, ‖f t‖ ≤ C * (1 + t ^ 2)⁻¹) (a : Operator X) :
    averagingOperator h hf a ∈ continuityPoints h := by
  apply (mem_continuityPoints_iff_continuousAt_zero h _).mpr
  rw [ContinuousAt, diagonalFlow_zero, tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun r => diagonalFlow_averagingOperator_sub_norm_le h hf r a)
    (by simpa only [zero_mul] using (tendsto_integral_norm_translate_sub hc hC hb).mul_const ‖a‖)

end DynamicalCStarAlgebras
