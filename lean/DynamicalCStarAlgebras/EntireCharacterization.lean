import DynamicalCStarAlgebras.OperatorHolomorphy

noncomputable section

namespace DynamicalCStarAlgebras

universe u

theorem finiteMatrixForm_extension {X : Type u} (h : X → ℝ) (a : Operator X) {M : ℝ}
    (hprop : ∀ x y, M < |h x - h y| → matrixEntry a x y = 0)
    (z : ℂ) (v w : X →₀ ℂ) :
    finiteMatrixForm (matrixEntry (finitePropagationExtension h a hprop z)) v w =
      finiteOrbitForm h a z v w :=
  (finiteMatrixForm_matrixEntry _ v w).trans
    (inner_operatorOfFiniteForm _ (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
      (finiteOrbitForm_uniform_bound h a hprop z) v w)

theorem differentiable_finiteMatrixForm_extension {X : Type u} (h : X → ℝ) (a : Operator X) {M : ℝ}
    (hprop : ∀ x y, M < |h x - h y| → matrixEntry a x y = 0) (v w : X →₀ ℂ) :
    Differentiable ℂ (fun z => finiteMatrixForm (matrixEntry (finitePropagationExtension h a hprop z)) v w) := by
  simp only [finiteMatrixForm_extension, finiteOrbitForm_sum]
  fun_prop

theorem abs_im_le_of_mem_ball {c z : ℂ} (hz : z ∈ Metric.ball c 1) : |z.im| ≤ |c.im| + 1 := by
  have he : |z.im| ≤ ‖z - c‖ + |c.im| := calc
    |z.im| = |(z - c).im + c.im| := by simp
    _ ≤ |(z - c).im| + |c.im| := by
      simpa only [Real.norm_eq_abs] using norm_add_le (z - c).im c.im
    _ ≤ ‖z - c‖ + |c.im| := add_le_add (Complex.abs_im_le_norm (z - c)) le_rfl
  linarith [show ‖z - c‖ < 1 from (by simpa only [Metric.mem_ball, dist_eq_norm] using hz)]

theorem continuous_finitePropagationExtension {X : Type u} (h : X → ℝ) (a : Operator X)
    {M : ℝ} (hM : 0 ≤ M) (hprop : ∀ x y, M < |h x - h y| → matrixEntry a x y = 0) :
    Continuous (finitePropagationExtension h a hprop) :=
  continuous_operatorFamily (differentiable_finiteMatrixForm_extension h a hprop)
    (fun c => ⟨‖a‖ * Real.exp (M * (|c.im| + 1)), by positivity, fun z hz =>
      (norm_finitePropagationExtension_le h a hprop z).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (abs_im_le_of_mem_ball hz) hM)) (norm_nonneg a))⟩)

theorem differentiable_finitePropagationExtension {X : Type u} (h : X → ℝ) (a : Operator X)
    {M : ℝ} (hM : 0 ≤ M) (hprop : ∀ x y, M < |h x - h y| → matrixEntry a x y = 0) :
    Differentiable ℂ (finitePropagationExtension h a hprop) := by
  refine differentiable_operatorFamily (continuous_finitePropagationExtension h a hM hprop)
    fun x y => ?_
  simpa only [matrixEntry_finitePropagationExtension] using
    (show Differentiable ℂ (fun z : ℂ => Complex.exp (Complex.I * z * ((h x - h y : ℝ) : ℂ)) *
      matrixEntry a x y) by fun_prop)

/-- Reverse implication of Proposition Prop.analitic.iff.finite.dh.prop. -/
theorem finitePropagation_isEntireExponentialType {X : Type u} (h : X → ℝ) (a : Operator X)
    (ha : @HasFinitePropagation X (realPullbackPseudoMetric h) a) : IsEntireExponentialType h a := by
  obtain ⟨M, hM, hprop⟩ := ha
  have hp : ∀ x y, M < |h x - h y| → matrixEntry a x y = 0 :=
    fun x y hxy => hprop x y ((realPullbackPseudoMetric_dist h x y).symm ▸ hxy)
  exact ⟨finitePropagationExtension h a hp,
    ⟨differentiable_finitePropagationExtension h a hM.le hp, finitePropagationExtension_real h a hp⟩,
    ‖a‖ + 1, by positivity, M, hM, fun z =>
      (norm_finitePropagationExtension_le h a hp z).trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right zero_le_one) (Real.exp_pos _).le)⟩

/-- Proposition Prop.analitic.iff.finite.dh.prop, for arbitrary X and real h. -/
theorem isEntireExponentialType_iff_finitePropagation {X : Type u} (h : X → ℝ) (a : Operator X) :
    IsEntireExponentialType h a ↔ @HasFinitePropagation X (realPullbackPseudoMetric h) a :=
  ⟨IsEntireExponentialType.hasFinitePropagation, finitePropagation_isEntireExponentialType h a⟩

end DynamicalCStarAlgebras
