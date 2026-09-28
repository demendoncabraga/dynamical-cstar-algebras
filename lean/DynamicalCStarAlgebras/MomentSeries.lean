import DynamicalCStarAlgebras.StripAlgebra

noncomputable section

namespace DynamicalCStarAlgebras

/-- The bounded operators realizing all entrywise iterated commutators. -/
def IsDiagonalMomentSequence {X : Type*} (h : X → ℝ) (a : Operator X)
    (b : ℕ → Operator X) : Prop :=
  ∀ k x y, matrixEntry (b k) x y = ((h x - h y : ℝ) : ℂ) ^ k * matrixEntry a x y

/-- The operator Taylor series determined by the iterated commutators. -/
def diagonalMomentSeries {X : Type*} (b : ℕ → Operator X) :
    FormalMultilinearSeries ℂ ℂ (Operator X) :=
  fun k => ContinuousMultilinearMap.mkPiRing ℂ (Fin k)
    ((Complex.I ^ k / (k.factorial : ℂ)) • b k)

/-- Factorial moment growth becomes a geometric bound on Taylor coefficients. -/
theorem diagonalMomentSeries_norm_le {X : Type*} (b : ℕ → Operator X) {A B : ℝ}
    (hb : ∀ k, ‖b k‖ ≤ A * B ^ k * k.factorial) (k : ℕ) :
    ‖diagonalMomentSeries b k‖ ≤ A * B ^ k := by
  simp only [diagonalMomentSeries, ContinuousMultilinearMap.norm_mkPiRing, norm_smul,
    norm_div, norm_pow, Complex.norm_I, one_pow, Complex.norm_natCast]
  simpa only [one_div, ← div_eq_inv_mul] using
    (div_le_iff₀ (by positivity : (0 : ℝ) < k.factorial)).mpr (hb k)

/-- The Taylor series converges at least up to the reciprocal moment-growth rate. -/
theorem diagonalMomentSeries_le_radius {X : Type*} (b : ℕ → Operator X) {A B : ℝ}
    (hB : 0 < B) (hb : ∀ k, ‖b k‖ ≤ A * B ^ k * k.factorial) :
    ENNReal.ofReal B⁻¹ ≤ (diagonalMomentSeries b).radius := by
  apply (diagonalMomentSeries b).le_radius_of_bound A (r := Real.toNNReal B⁻¹)
  intro k
  simp only [Real.toNNReal_of_nonneg (inv_nonneg.mpr hB.le)]
  have hk := mul_le_mul_of_nonneg_right (diagonalMomentSeries_norm_le b hb k)
    (pow_nonneg (inv_nonneg.mpr hB.le) k)
  simpa only [mul_assoc, ← mul_pow, mul_inv_cancel₀ hB.ne', one_pow, mul_one] using! hk

/-- Points inside the reciprocal-rate disk belong to the convergence disk. -/
theorem diagonalMomentSeries_mem_ball {X : Type*} (b : ℕ → Operator X) {A B : ℝ}
    (hB : 0 < B) (hb : ∀ k, ‖b k‖ ≤ A * B ^ k * k.factorial)
    {z : ℂ} (hz : ‖z‖ < B⁻¹) : z ∈ Metric.eball 0 (diagonalMomentSeries b).radius := by
  rw [Metric.mem_eball, edist_dist, dist_zero_right]
  exact ((ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr hB)).mpr hz).trans_le
    (diagonalMomentSeries_le_radius b hB hb)

/-- Taylor series matrix coefficients sum to the prescribed complex-time flow. -/
theorem matrixEntry_diagonalMomentSeries_sum {X : Type*} {h : X → ℝ} {a : Operator X}
    {b : ℕ → Operator X} (hb : IsDiagonalMomentSequence h a b)
    {z : ℂ} (hz : z ∈ Metric.eball 0 (diagonalMomentSeries b).radius) (x y : X) :
    matrixEntry ((diagonalMomentSeries b).sum z) x y =
      Complex.exp (Complex.I * z * ((h x - h y : ℝ) : ℂ)) * matrixEntry a x y := by
  have hs := (matrixEntryCLM x y).hasSum ((diagonalMomentSeries b).hasSum hz)
  simp only [diagonalMomentSeries, ContinuousMultilinearMap.mkPiRing_apply,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_smul,
    matrixEntryCLM_apply, matrixEntry_smul, hb _ x y] at hs
  apply hs.unique
  simpa only [← Complex.exp_eq_exp_ℂ, mul_pow, div_eq_mul_inv, mul_assoc, mul_comm,
    mul_left_comm] using
    (NormedSpace.expSeries_div_hasSum_exp (Complex.I * z * ((h x - h y : ℝ) : ℂ))).mul_right
      (matrixEntry a x y)

end DynamicalCStarAlgebras
