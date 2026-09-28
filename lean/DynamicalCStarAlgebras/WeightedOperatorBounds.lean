import DynamicalCStarAlgebras.GapEstimate

noncomputable section

namespace DynamicalCStarAlgebras

/-- A weighted matrix has operator norm at most `C` precisely when all finite forms do. -/
def HasWeightedOperatorBound {X : Type*} (a : Operator X) (h : X → ℝ) (θ C : ℝ) : Prop :=
  ∀ v w : X →₀ ℂ,
    ‖finiteMatrixForm (fun x y => (Real.exp (θ * (h x - h y)) : ℂ) * matrixEntry a x y) v w‖ ≤
      C * ‖finiteVector v‖ * ‖finiteVector w‖

theorem hasWeightedOperatorBound_iff {X : Type*} (a : Operator X) (h : X → ℝ)
    (θ : ℝ) {C : ℝ} (hC : 0 ≤ C) : HasWeightedOperatorBound a h θ C ↔
      ∃ b : Operator X, ‖b‖ ≤ C ∧ ∀ x y,
        matrixEntry b x y = (Real.exp (θ * (h x - h y)) : ℂ) * matrixEntry a x y := by
  constructor
  · intro hb
    refine ⟨operatorOfFiniteForm _ hb, norm_operatorOfFiniteForm_le _ hC hb, ?_⟩
    intro x y
    exact (matrixEntry_operatorOfFiniteForm _ hC hb x y).trans (finiteMatrixForm_single_one _ x y)
  · rintro ⟨b, hb, he⟩ v w
    simp only [← he]
    exact (norm_finiteMatrixForm_matrixEntry_le b v w).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) (norm_nonneg _))

/-- Weighted finite forms are continuous for the product topology on real functions. -/
theorem continuous_weighted_finiteMatrixForm {X : Type*} (a : Operator X) (θ : ℝ)
    (v w : X →₀ ℂ) : Continuous (fun h : X → ℝ =>
      finiteMatrixForm (fun x y => (Real.exp (θ * (h x - h y)) : ℂ) * matrixEntry a x y) v w) := by
  simp only [finiteMatrixForm_apply]
  fun_prop

/-- The norm-bounded weighted-matrix sets in the Baire argument are closed. -/
theorem isClosed_hasWeightedOperatorBound {X : Type*} (a : Operator X) (θ C : ℝ) :
    IsClosed {h : X → ℝ | HasWeightedOperatorBound a h θ C} := by
  simp only [HasWeightedOperatorBound, Set.ofPred_forall]
  exact isClosed_iInter fun v => isClosed_iInter fun w =>
    isClosed_le (continuous_weighted_finiteMatrixForm a θ v w).norm continuous_const

/-- Imaginary values of a strip extension give the exponentially weighted matrices. -/
theorem IsStripExtension.weighted_entries {X : Type*} {h : X → ℝ} {a : Operator X}
    {δ : ℝ} {F : ℂ → Operator X} (hF : IsStripExtension h a δ F) (hδ : 0 < δ)
    {θ : ℝ} (hθ : |θ| ≤ δ) (x y : X) :
    matrixEntry (F (-(θ : ℂ) * Complex.I)) x y =
      (Real.exp (θ * (h x - h y)) : ℂ) * matrixEntry a x y := by
  rw [hF.matrixEntry_eq hδ (by simpa using hθ)]
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  calc
    _ = -(Complex.I * Complex.I) * ((θ : ℂ) * ((h x : ℂ) - (h y : ℂ))) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

/-- Every strip-analytic orbit belongs to one of the closed weighted-norm sets.
Index `n` represents the positive integer `n+1`, avoiding division by zero. -/
theorem IsStripExtension.exists_weighted_bound {X : Type*} {h : X → ℝ} {a : Operator X}
    {δ : ℝ} {F : ℂ → Operator X} (hF : IsStripExtension h a δ F) (hδ : 0 < δ) :
    ∃ n : ℕ, HasWeightedOperatorBound a h ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) := by
  obtain ⟨s, hs, hmax⟩ := hF.strip_maximum hδ
  obtain ⟨n, hn⟩ := exists_nat_gt (max δ⁻¹ ‖F ((s : ℂ) * Complex.I)‖)
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hwidth : |((n : ℝ) + 1)⁻¹| ≤ δ := by
    rw [abs_of_pos (inv_pos.mpr hnpos)]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hnpos).mpr
    have hb := mul_le_mul_of_nonneg_left ((le_max_left δ⁻¹ _).trans hn.le) hδ.le
    rw [mul_inv_cancel₀ hδ.ne'] at hb
    nlinarith
  refine ⟨n, (hasWeightedOperatorBound_iff a h _ hnpos.le).mpr
    ⟨F (-((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * Complex.I), ?_, hF.weighted_entries hδ hwidth⟩⟩
  exact (hmax _ (by simpa only [Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re,
    mul_one, mul_zero, add_zero, abs_neg] using hwidth)).trans
    ((le_max_right δ⁻¹ _).trans (by linarith))

end DynamicalCStarAlgebras
