import DynamicalCStarAlgebras.ExpanderNumerics

noncomputable section

namespace DynamicalCStarAlgebras

open Filter

/-- The square-root modulus estimate at the end of the expander projection proof
implies the claimed polynomial decay, with one constant for all positive radii. -/
theorem polynomialDecay_of_expander_modulus_bound {X : Type*} [PseudoMetricSpace X]
    (a : Operator X) {α C D c : ℝ} (hα : 0 ≤ α) (hC : 0 < C) (hD : 0 ≤ D) (hc : 0 < c)
    (ha : ∀ r : ℝ, 0 < r → quasiLocalModulus a r ≤
      C * Real.sqrt (D * r ^ (-2 * α) + (1 + c * r) * Real.exp (-c * r))) :
    HasPolynomialDecay α a := by
  let M := C * Real.sqrt (D + 1 + c)
  have hM : 0 < M := mul_pos hC (Real.sqrt_pos.mpr (by positivity))
  apply hasPolynomialDecay_of_eventually hα hM a
  filter_upwards [(isLittleO_exp_neg_mul_rpow_atTop hc (-2 * α - 1)).bound zero_lt_one,
    eventually_ge_atTop (1 : ℝ)] with r hb hr
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (Real.rpow_nonneg hrpos.le _), one_mul] at hb
  have hpow : r * r ^ (-2 * α - 1) = r ^ (-2 * α) := by
    nth_rw 1 [← Real.rpow_one r]
    rw [← Real.rpow_add hrpos]
    congr 1
    ring
  have htail : (1 + c * r) * Real.exp (-c * r) ≤ (1 + c) * r ^ (-2 * α) := by
    calc
      _ ≤ ((1 + c) * r) * Real.exp (-c * r) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_nonneg _)
      _ ≤ ((1 + c) * r) * r ^ (-2 * α - 1) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by rw [mul_assoc, hpow]
  have hsq : (r ^ (-α)) ^ 2 = r ^ (-2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hrpos.le]
    congr 1
    ring
  have hroot : Real.sqrt (D * r ^ (-2 * α) + (1 + c * r) * Real.exp (-c * r)) ≤
      Real.sqrt (D + 1 + c) * r ^ (-α) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt (by positivity), hsq]
      nlinarith
  exact (ha r hrpos).trans (by simpa only [M, mul_assoc] using mul_le_mul_of_nonneg_left hroot hC.le)

end DynamicalCStarAlgebras
