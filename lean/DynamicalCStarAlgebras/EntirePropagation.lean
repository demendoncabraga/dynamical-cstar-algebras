import DynamicalCStarAlgebras.AnalyticExtensions

noncomputable section

namespace DynamicalCStarAlgebras

universe u

/-- An entire extension of the diagonal orbit in Definition Def.BandAnalytic.functions. -/
structure IsEntireExtension {X : Type u} (h : X → ℝ) (a : Operator X)
    (F : ℂ → Operator X) : Prop where
  differentiable : Differentiable ℂ F
  on_real : ∀ t : ℝ, F t = diagonalFlow h t a

/-- Entire analyticity of exponential type, with both constants strictly positive. -/
def IsEntireExponentialType {X : Type u} (h : X → ℝ) (a : Operator X) : Prop :=
  ∃ F : ℂ → Operator X, IsEntireExtension h a F ∧
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 0 < K ∧
      ∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (K * |z.im|)

theorem IsEntireExtension.onStrip {X : Type u} {h : X → ℝ} {a : Operator X}
    {F : ℂ → Operator X} (hF : IsEntireExtension h a F) (δ : ℝ) :
    IsStripExtension h a δ F :=
  ⟨hF.differentiable.continuous.continuousOn, hF.differentiable.differentiableOn, hF.on_real⟩

theorem IsEntireExtension.matrixEntry_eq {X : Type u} {h : X → ℝ} {a : Operator X}
    {F : ℂ → Operator X} (hF : IsEntireExtension h a F) (z : ℂ) (x y : X) :
    matrixEntry (F z) x y =
      Complex.exp (Complex.I * z * ((h x - h y : ℝ) : ℂ)) * matrixEntry a x y :=
  (hF.onStrip (|z.im| + 1)).matrixEntry_eq (by positivity) (by linarith) x y

theorem norm_matrixEntry_le {X : Type u} (a : Operator X) (x y : X) :
    ‖matrixEntry a x y‖ ≤ ‖a‖ := by
  simpa only [matrixEntry, delta_norm, mul_one] using
    (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (a (delta y)) x).trans
      (a.le_opNorm (delta y))

/-- Exponential comparison forces the exponent on the left to be no larger. -/
theorem exponent_le_of_bound {b C d K : ℝ} (hb : 0 < b) (hC : 0 < C)
    (hbound : ∀ t : ℝ, 0 ≤ t → Real.exp (d * t) * b ≤ C * Real.exp (K * t)) : d ≤ K := by
  have hlog : ∀ t : ℝ, 0 ≤ t → d * t + Real.log b ≤ Real.log C + K * t :=
    fun t ht => by
      simpa only [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hb),
        Real.log_mul (ne_of_gt hC) (Real.exp_ne_zero _), Real.log_exp] using
          Real.log_le_log (mul_pos (Real.exp_pos _) hb) (hbound t ht)
  by_contra hn
  have hp : 0 < d - K := sub_pos.mpr (lt_of_not_ge hn)
  nlinarith [hlog ((|Real.log C - Real.log b| + 1) / (d - K))
    (div_nonneg (by positivity) hp.le),
    div_mul_cancel₀ (|Real.log C - Real.log b| + 1) (ne_of_gt hp),
    le_abs_self (Real.log C - Real.log b)]

theorem IsEntireExtension.coefficient_bound {X : Type u} {h : X → ℝ} {a : Operator X}
    {F : ℂ → Operator X} (hF : IsEntireExtension h a F) (z : ℂ) (x y : X) :
    Real.exp (-z.im * (h x - h y)) * ‖matrixEntry a x y‖ ≤ ‖F z‖ := by
  simpa [hF.matrixEntry_eq, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.mul_im] using
    norm_matrixEntry_le (F z) x y

/-- The propagation radius is bounded by the precise exponential-type constant K. -/
theorem IsEntireExtension.propagation_bound {X : Type u} {h : X → ℝ} {a : Operator X}
    {F : ℂ → Operator X} (hF : IsEntireExtension h a F) {C K : ℝ} (hC : 0 < C)
    (hbound : ∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (K * |z.im|))
    {x y : X} (hxy : matrixEntry a x y ≠ 0) : |h x - h y| ≤ K := by
  have hb : 0 < ‖matrixEntry a x y‖ := norm_pos_iff.mpr hxy
  have hp : h x - h y ≤ K := exponent_le_of_bound hb hC fun t ht => by
    simpa [Complex.mul_im, abs_of_nonneg ht, mul_comm] using
      (hF.coefficient_bound (-(t : ℂ) * Complex.I) x y).trans (hbound _)
  have hn : -(h x - h y) ≤ K := exponent_le_of_bound hb hC fun t ht => by
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_one, mul_zero, add_zero, zero_add, abs_of_nonneg ht, neg_mul, mul_neg, mul_comm] using
      (hF.coefficient_bound ((t : ℂ) * Complex.I) x y).trans (hbound _)
  exact abs_le.mpr ⟨neg_le.mp hn, hp⟩

/-- Forward implication of Proposition Prop.analitic.iff.finite.dh.prop. -/
theorem IsEntireExponentialType.hasFinitePropagation {X : Type u} {h : X → ℝ}
    {a : Operator X} (ha : IsEntireExponentialType h a) :
    @HasFinitePropagation X (realPullbackPseudoMetric h) a := by
  obtain ⟨F, hF, C, hC, K, hK, hbound⟩ := ha
  exact ⟨K, hK, fun x y hxy => Classical.byContradiction fun hn =>
    (not_lt_of_ge (hF.propagation_bound hC hbound hn))
      ((realPullbackPseudoMetric_dist h x y) ▸ hxy)⟩

end DynamicalCStarAlgebras
