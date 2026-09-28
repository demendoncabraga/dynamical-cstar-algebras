import DynamicalCStarAlgebras.Averaging

namespace DynamicalCStarAlgebras

open MeasureTheory

/-- The real-line Fejér kernel, with its continuous value at zero. -/
noncomputable def fejerKernel (s t : ℝ) : ℝ :=
  s / (2 * Real.pi) * Real.sinc (s * t / 2) ^ 2

theorem fejerKernel_zero (s : ℝ) : fejerKernel s 0 = s / (2 * Real.pi) := by
  simp [fejerKernel]

theorem fejerKernel_nonneg {s : ℝ} (hs : 0 ≤ s) (t : ℝ) : 0 ≤ fejerKernel s t :=
  mul_nonneg (div_nonneg hs (by positivity)) (sq_nonneg _)

theorem continuous_fejerKernel (s : ℝ) : Continuous (fejerKernel s) := by
  unfold fejerKernel
  fun_prop

theorem sinc_sq_le_one (x : ℝ) : Real.sinc x ^ 2 ≤ 1 := by
  exact (sq_le_one_iff_abs_le_one _).mpr (Real.abs_sinc_le_one x)

theorem mul_sinc_eq_sin (x : ℝ) : x * Real.sinc x = Real.sin x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (congrArg (x * ·) (Real.sinc_of_ne_zero hx)).trans (mul_div_cancel₀ _ hx)

theorem scaled_sinc_sq_bound {s : ℝ} (hs : 0 < s) (t : ℝ) :
    t ^ 2 * Real.sinc (s * t / 2) ^ 2 ≤ 4 / s ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hs)).mpr
  nlinarith [congrArg (fun x : ℝ => x ^ 2) (mul_sinc_eq_sin (s * t / 2)),
    Real.sin_sq_le_one (s * t / 2)]

theorem fejerKernel_le_integrable_bound {s : ℝ} (hs : 0 < s) (t : ℝ) :
    fejerKernel s t ≤ (s / (2 * Real.pi) * (1 + 4 / s ^ 2)) * (1 + t ^ 2)⁻¹ := by
  have hb : Real.sinc (s * t / 2) ^ 2 * (1 + t ^ 2) ≤ 1 + 4 / s ^ 2 := by
    nlinarith [sinc_sq_le_one (s * t / 2), scaled_sinc_sq_bound hs t]
  simpa only [fejerKernel, div_eq_mul_inv, mul_assoc] using mul_le_mul_of_nonneg_left
    ((le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr hb)
    (by positivity : 0 ≤ s / (2 * Real.pi))

theorem integrable_fejerKernel {s : ℝ} (hs : 0 < s) : Integrable (fejerKernel s) := by
  refine (integrable_inv_one_add_sq.const_mul (s / (2 * Real.pi) * (1 + 4 / s ^ 2))).mono'
    (continuous_fejerKernel s).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t =>
    (Real.norm_of_nonneg (fejerKernel_nonneg hs.le t)).le.trans
      (fejerKernel_le_integrable_bound hs t)

/-- The inverse-square bound used outside a neighborhood of zero. -/
theorem fejerKernel_tail_bound {s t : ℝ} (hs : 0 < s) (ht : t ≠ 0) :
    fejerKernel s t ≤ 2 / (s * Real.pi * t ^ 2) := by
  have hb := mul_le_mul_of_nonneg_left (scaled_sinc_sq_bound hs t)
    (by positivity : 0 ≤ s / (2 * Real.pi))
  convert (div_le_div_of_nonneg_right hb (sq_nonneg t)) using 1
  · rfl
  · simp [fejerKernel, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, ht]
  · field_simp
    norm_num

end DynamicalCStarAlgebras
