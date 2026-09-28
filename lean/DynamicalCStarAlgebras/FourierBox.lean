import DynamicalCStarAlgebras.Fejer

namespace DynamicalCStarAlgebras

open MeasureTheory Set
open scoped FourierTransform Convolution

noncomputable def intervalBox (r : ℝ) : ℝ → ℂ :=
  (Icc (-r) r).indicator (fun _ => 1)

theorem integrable_intervalBox (r : ℝ) : Integrable (intervalBox r) := by
  exact (integrable_indicator_iff measurableSet_Icc).mpr
    (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne))

theorem fourier_intervalBox_integral {r : ℝ} (hr : 0 ≤ r) (ξ : ℝ) :
    𝓕 (intervalBox r) ξ = ∫ t in -r..r, Complex.exp ((-2 * Real.pi * t * ξ : ℝ) * Complex.I) := by
  rw [Real.fourier_eq']
  simp only [intervalBox, smul_eq_mul, Real.inner_apply, ← mul_assoc]
  simp only [← indicator_mul_right _ (fun v : ℝ =>
    Complex.exp ((-2 * Real.pi * v * ξ : ℝ) * Complex.I)), mul_one,
    integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (neg_le_self hr)]

theorem integral_phase_interval (c r : ℝ) :
    (∫ t in -r..r, Complex.exp (((c * t : ℝ) : ℂ) * Complex.I)) =
      2 * (r : ℂ) * Real.sinc (c * r) := by
  by_cases hc : c = 0
  · simp [hc]
    ring
  · rw [intervalIntegral.integral_comp_mul_left (fun t : ℝ =>
      Complex.exp ((t : ℂ) * Complex.I)) hc, mul_neg, integral_exp_mul_I_eq_sinc]
    simp [Complex.real_smul, Complex.ofReal_mul, mul_assoc, mul_left_comm, hc]

theorem fourier_intervalBox {r : ℝ} (hr : 0 ≤ r) (ξ : ℝ) :
    𝓕 (intervalBox r) ξ = 2 * (r : ℂ) * Real.sinc (2 * Real.pi * ξ * r) := by
  rw [fourier_intervalBox_integral hr]
  simpa only [neg_mul, mul_neg, Real.sinc_neg, mul_assoc, mul_left_comm, mul_comm] using
    integral_phase_interval (-2 * Real.pi * ξ) r

theorem intervalBox_mul_sub (r x t : ℝ) :
    intervalBox r t * intervalBox r (x - t) =
      (Icc (max (-r) (x - r)) (min r (x + r))).indicator (fun _ => (1 : ℂ)) t := by
  simp only [intervalBox, indicator, mem_Icc, max_le_iff, le_min_iff]
  split_ifs <;> grind

theorem intervalBox_convolution (r x : ℝ) :
    (intervalBox r ⋆[ContinuousLinearMap.mul ℂ ℂ] intervalBox r) x =
      (max (2 * r - |x|) 0 : ℝ) := by
  simp only [convolution, ContinuousLinearMap.mul_apply', intervalBox_mul_sub,
    integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc,
    Complex.real_smul, mul_one]
  congr 1
  grind [abs_eq_max_neg]

noncomputable def intervalTriangle (r x : ℝ) : ℂ := (max (2 * r - |x|) 0 : ℝ)

theorem intervalTriangle_eq_convolution (r : ℝ) :
    intervalTriangle r = intervalBox r ⋆[ContinuousLinearMap.mul ℂ ℂ] intervalBox r :=
  funext fun x => (intervalBox_convolution r x).symm

theorem integrable_intervalTriangle (r : ℝ) : Integrable (intervalTriangle r) := by
  rw [intervalTriangle_eq_convolution]
  exact (integrable_intervalBox r).integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_intervalBox r)

theorem continuous_intervalTriangle (r : ℝ) : Continuous (intervalTriangle r) := by
  unfold intervalTriangle
  fun_prop

theorem fourier_intervalTriangle {r : ℝ} (hr : 0 ≤ r) (ξ : ℝ) :
    𝓕 (intervalTriangle r) ξ = (2 * (r : ℂ) * Real.sinc (2 * Real.pi * ξ * r)) ^ 2 := by
  rw [intervalTriangle_eq_convolution,
    Real.fourier_mul_convolution_eq (integrable_intervalBox r) (integrable_intervalBox r),
    fourier_intervalBox hr, pow_two]

theorem fourier_intervalTriangle_fejer {r : ℝ} (hr : 0 ≤ r) (ξ : ℝ) :
    𝓕 (intervalTriangle r) ξ = (2 * r : ℝ) * (fejerKernel (4 * Real.pi * r) ξ : ℂ) := by
  rw [fourier_intervalTriangle hr, fejerKernel]
  rw [show 4 * Real.pi * r * ξ / 2 = 2 * Real.pi * ξ * r by ring]
  push_cast
  field_simp
  ring

theorem integrable_fourier_intervalTriangle {r : ℝ} (hr : 0 < r) :
    Integrable (𝓕 (intervalTriangle r)) := by
  simpa only [funext (fourier_intervalTriangle_fejer hr.le)] using!
    (integrable_fejerKernel (by positivity : 0 < 4 * Real.pi * r)).ofReal.const_mul
      ((2 * r : ℝ) : ℂ)

theorem fejer_inverse_integral {r : ℝ} (hr : 0 < r) (x : ℝ) :
    (2 * r : ℝ) * (𝓕⁻ (fun t => (fejerKernel (4 * Real.pi * r) t : ℂ))) x =
      intervalTriangle r x := by
  have hi := (integrable_intervalTriangle r).fourierInv_fourier_eq (v := x)
    (integrable_fourier_intervalTriangle hr) (continuous_intervalTriangle r).continuousAt
  simpa only [funext (fourier_intervalTriangle_fejer hr.le), Real.fourierInv_eq',
    smul_eq_mul, mul_left_comm _ ((2 * r : ℝ) : ℂ), integral_const_mul] using hi

theorem integral_fejerKernel_scaled {r : ℝ} (hr : 0 < r) :
    ∫ t, fejerKernel (4 * Real.pi * r) t = 1 := by
  have hi := congrArg Complex.re (fejer_inverse_integral hr 0)
  simp [Real.fourierInv_eq', intervalTriangle, integral_complex_ofReal,
    max_eq_left (show 0 ≤ 2 * r by positivity)] at hi
  nlinarith

/-- Equation 2.03.Aug.26: the real-line Fejer kernel has total mass one. -/
theorem integral_fejerKernel {s : ℝ} (hs : 0 < s) : ∫ t, fejerKernel s t = 1 := by
  simpa only [mul_div_cancel₀ s (by positivity : 4 * Real.pi ≠ 0)] using
    integral_fejerKernel_scaled (by positivity : 0 < s / (4 * Real.pi))

theorem fourierPlus_eq_fourierInv (f : ℝ → ℂ) (ξ : ℝ) :
    fourierPlus f ξ = 𝓕⁻ f (ξ / (2 * Real.pi)) := by
  have he (t : ℝ) : 2 * Real.pi * (t * (ξ / (2 * Real.pi))) = t * ξ := by
    field_simp
  simp only [fourierPlus, Real.fourierInv_eq', Real.inner_apply, he, smul_eq_mul]
  simp only [mul_comm]

/-- Fourier inversion of the triangle, in the manuscript's Fourier convention. -/
theorem fourierPlus_fejer_scaled {r : ℝ} (hr : 0 < r) (ξ : ℝ) :
    fourierPlus (fun t => (fejerKernel (4 * Real.pi * r) t : ℂ)) ξ =
      (max (1 - |ξ| / (4 * Real.pi * r)) 0 : ℝ) := by
  have hi := fejer_inverse_integral hr (ξ / (2 * Real.pi))
  have he : max (2 * r - |ξ / (2 * Real.pi)|) 0 =
      2 * r * max (1 - |ξ| / (4 * Real.pi * r)) 0 := by
    rw [mul_max_of_nonneg _ _ (by positivity : 0 ≤ 2 * r), mul_zero]
    congr 1
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
    ring
  apply mul_left_cancel₀ (show ((2 * r : ℝ) : ℂ) ≠ 0 by exact_mod_cast (by positivity : 2 * r ≠ 0))
  simpa only [fourierPlus_eq_fourierInv, intervalTriangle, he, Complex.ofReal_mul] using hi

/-- Equation 2.03.Aug.26: the Fejer Fourier transform is the triangular cutoff. -/
theorem fourierPlus_fejerKernel {s : ℝ} (hs : 0 < s) (ξ : ℝ) :
    fourierPlus (fun t => (fejerKernel s t : ℂ)) ξ = (max (1 - |ξ| / s) 0 : ℝ) := by
  simpa only [mul_div_cancel₀ s (by positivity : 4 * Real.pi ≠ 0)] using
    fourierPlus_fejer_scaled (by positivity : 0 < s / (4 * Real.pi)) ξ

theorem integral_norm_fejerKernel {s : ℝ} (hs : 0 < s) :
    ∫ t, ‖fejerKernel s t‖ = 1 := by
  simpa only [Real.norm_of_nonneg (fejerKernel_nonneg hs.le _)] using integral_fejerKernel hs

end DynamicalCStarAlgebras
