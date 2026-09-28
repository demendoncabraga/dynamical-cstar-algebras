import DynamicalCStarAlgebras.ExpanderDiameter

noncomputable section

namespace DynamicalCStarAlgebras

/-- The entropy square-root bound used in Eq.21.Aug.26.lb.2, with its exact factor two. -/
theorem sqrt_entropy_le_two_cuberoot {δ : ℝ} (hδ : 0 < δ) :
    Real.sqrt (δ * Real.log (1 / δ)) ≤ 2 * δ ^ (1 / 3 : ℝ) := by
  let q : ℝ := δ ^ (1 / 3 : ℝ)
  have hq : 0 < q := Real.rpow_pos_of_pos hδ _
  have hcube : q ^ 3 = δ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    norm_num
  have hlog := Real.log_le_rpow_div (show 0 ≤ 1 / δ by positivity)
    (by norm_num : (0 : ℝ) < 1 / 3)
  rw [one_div, Real.inv_rpow hδ.le] at hlog
  have hprod : δ * q⁻¹ = q ^ 2 := by
    rw [← hcube]
    field_simp
  have hbound : δ * Real.log (1 / δ) ≤ 3 * q ^ 2 := by
    have he := mul_le_mul_of_nonneg_left hlog hδ.le
    change δ * Real.log δ⁻¹ ≤ δ * (q⁻¹ / (1 / 3)) at he
    rw [show δ * (q⁻¹ / (1 / 3)) = 3 * (δ * q⁻¹) by ring, hprod] at he
    simpa only [one_div] using he
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · change δ * Real.log (1 / δ) ≤ (2 * q) ^ 2
    nlinarith [sq_nonneg q]

/-- The function t log(e/t) is increasing on (0,1]. -/
theorem entropy_mass_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1) :
    x * Real.log (Real.exp 1 / x) ≤ y * Real.log (Real.exp 1 / y) := by
  have hypos := hx.trans_le hxy
  have hl := Real.log_le_sub_one_of_pos (div_pos hypos hx)
  rw [Real.log_div hypos.ne' hx.ne'] at hl
  have hmain : x * (Real.log y - Real.log x) ≤ y - x := by
    calc
      _ ≤ x * (y / x - 1) := mul_le_mul_of_nonneg_left hl hx.le
      _ = y - x := by field_simp
  have hlogy := Real.log_nonpos hypos.le hy
  rw [Real.log_div (Real.exp_ne_zero _) hx.ne', Real.log_div (Real.exp_ne_zero _) hypos.ne', Real.log_exp]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxy) hlogy]

/-- Equation Eq.ddqd.q, with the same separation parameter and polynomial factor. -/
theorem entropy_mass_of_exponential_bound {κ r t : ℝ} (hκ : 1 < κ) (hr : 0 ≤ r)
    (ht : 0 < t) (hb : t ≤ κ ^ (-r / 2)) :
    t * Real.log (Real.exp 1 / t) ≤ (1 + r * Real.log κ / 2) * κ ^ (-r / 2) := by
  have hp : 0 < κ ^ (-r / 2) := Real.rpow_pos_of_pos (by linarith) _
  have hle : κ ^ (-r / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hκ.le (by linarith)
  have he := entropy_mass_mono ht hb hle
  rw [Real.log_div (Real.exp_ne_zero _) hp.ne', Real.log_exp,
    Real.log_rpow (by linarith : 0 < κ)] at he
  convert he using 1
  ring

end DynamicalCStarAlgebras
