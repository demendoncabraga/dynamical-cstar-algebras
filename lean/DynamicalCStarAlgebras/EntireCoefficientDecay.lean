import DynamicalCStarAlgebras.PropagationDetection

noncomputable section

namespace DynamicalCStarAlgebras

open Filter

/-- Values at two imaginary times bound both signs of a frequency. -/
theorem IsEntireExtension.absolute_coefficient_bound {X : Type*} {h : X → ℝ}
    {a : Operator X} {F : ℂ → Operator X} (hF : IsEntireExtension h a F)
    (s : ℝ) (x y : X) :
    Real.exp (s * |h x - h y|) * ‖matrixEntry a x y‖ ≤
      max ‖F ((s : ℂ) * Complex.I)‖ ‖F (-(s : ℂ) * Complex.I)‖ := by
  by_cases hxy : 0 ≤ h x - h y
  · simpa [Complex.mul_im, abs_of_nonneg hxy] using
      (hF.coefficient_bound (-(s : ℂ) * Complex.I) x y).trans (le_max_right _ _)
  · simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add, add_zero,
      abs_of_neg (lt_of_not_ge hxy), mul_neg, neg_mul] using
      (hF.coefficient_bound ((s : ℂ) * Complex.I) x y).trans
        (le_max_left _ ‖F (-(s : ℂ) * Complex.I)‖)

/-- A large exponentially weighted coefficient must occur far from the diagonal. -/
theorem dist_lt_of_weighted_coefficient {X : Type*} [PseudoMetricSpace X]
    (a : Operator X) {c R : ℝ} (hc : 0 ≤ c) {x y : X}
    (hlarge : Real.exp (c * R) * ‖a‖ <
      Real.exp (c * dist x y) * ‖matrixEntry a x y‖) : R < dist x y := by
  contrapose! hlarge
  exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlarge hc))
    (norm_matrixEntry_le a x y) (norm_nonneg _) (Real.exp_pos _).le

/-- Lemma lem:allrates: entire diagonal orbits force every exponential coefficient bound. -/
theorem entire_coefficient_all_rates {X : Type*} [PseudoMetricSpace X] (a : Operator X)
    (ha : ∀ h : X → ℝ, LipschitzWith 1 h → ∃ F, IsEntireExtension h a F)
    {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, Real.exp (c * dist x y) * ‖matrixEntry a x y‖ ≤ C := by
  by_contra hn
  push Not at hn
  choose x y hxy using fun n : ℕ =>
    hn ((n : ℝ) + Real.exp (c * n) * (‖a‖ + 1)) (by positivity)
  have hd : Tendsto (fun n => dist (x n) (y n)) atTop atTop :=
    tendsto_atTop_mono (fun n => (dist_lt_of_weighted_coefficient a hc.le
      (show Real.exp (c * n) * ‖a‖ <
        Real.exp (c * dist (x n) (y n)) * ‖matrixEntry a (x n) (y n)‖ by
          nlinarith [hxy n, Real.exp_pos (c * n), Nat.cast_nonneg (α := ℝ) n])).le)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨n, hn, h, hh, hb⟩ := lipschitz_detect x y hd
  obtain ⟨F, hF⟩ := ha h hh
  have hbound : ∀ i, Real.exp (c * dist (x (n i)) (y (n i))) *
      ‖matrixEntry a (x (n i)) (y (n i))‖ ≤
        max ‖F (((9 * c : ℝ) : ℂ) * Complex.I)‖
          ‖F (-((9 * c : ℝ) : ℂ) * Complex.I)‖ := fun i =>
    (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by nlinarith [hb i])) (norm_nonneg _)).trans
        (hF.absolute_coefficient_bound (9 * c) (x (n i)) (y (n i)))
  obtain ⟨i, hi⟩ := exists_nat_gt
    (max ‖F (((9 * c : ℝ) : ℂ) * Complex.I)‖ ‖F (-((9 * c : ℝ) : ℂ) * Complex.I)‖)
  linarith [hbound i, hxy (n i), (show (i : ℝ) ≤ (n i : ℝ) from Nat.cast_le.mpr (hn.id_le i)),
    show 0 ≤ Real.exp (c * (n i : ℝ)) * (‖a‖ + 1) by positivity]

end DynamicalCStarAlgebras
