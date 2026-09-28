import DynamicalCStarAlgebras.AnalyticAlgebra

noncomputable section

namespace DynamicalCStarAlgebras

open Filter

/-- A bounded entire function is controlled in a half-plane by its boundary values. -/
theorem norm_le_on_right_halfPlane {f : ℂ → ℂ} {A D : ℝ} (hf : Differentiable ℂ f)
    (hD : ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ D)
    (hA : ∀ t : ℝ, ‖f ((t : ℂ) * Complex.I)‖ ≤ A)
    {z : ℂ} (hz : 0 ≤ z.re) : ‖f z‖ ≤ A := by
  refine PhragmenLindelof.right_half_plane_of_bounded_on_real hf.diffContOnCl
    ⟨0, by norm_num, 0, ?_⟩
    (isBoundedUnder_of_eventually_le ((eventually_ge_atTop (0 : ℝ)).mono
      fun t ht => hD t (by simpa using ht))) hA hz
  exact Asymptotics.IsBigO.of_bound D (eventually_inf_principal.mpr
    (Eventually.of_forall fun w hw => by simpa using hD w hw.le))

/-- The sharp exponential bound in the upper half-plane. -/
theorem exponential_bound_upper {f : ℂ → ℂ} {A D M : ℝ} (hf : Differentiable ℂ f)
    (hD : ∀ z : ℂ, ‖f z‖ ≤ D * Real.exp (M * |z.im|))
    (hA : ∀ t : ℝ, ‖f t‖ ≤ A) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖f z‖ ≤ A * Real.exp (M * z.im) := by
  let g : ℂ → ℂ := fun w => Complex.exp (-(M : ℂ) * w) * f (Complex.I * w)
  have hg : Differentiable ℂ g :=
    (Complex.differentiable_exp.comp ((differentiable_const (-(M : ℂ))).mul differentiable_id)).mul
      (hf.comp ((differentiable_const Complex.I).mul differentiable_id))
  have hnorm (w : ℂ) : ‖g w‖ = Real.exp (-M * w.re) * ‖f (Complex.I * w)‖ := by
    simp [g, Complex.norm_exp, Complex.mul_re]
  have hgb (w : ℂ) (hw : 0 ≤ w.re) : ‖g w‖ ≤ D := by
    refine (hnorm w).trans_le ((mul_le_mul_of_nonneg_left (hD (Complex.I * w))
      (Real.exp_pos _).le).trans_eq ?_)
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
      abs_of_nonneg hw, mul_left_comm, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, mul_one]
  have hga (t : ℝ) : ‖g ((t : ℂ) * Complex.I)‖ ≤ A := by
    simpa [hnorm, Complex.mul_re, mul_comm (t : ℂ) Complex.I, ← mul_assoc] using hA (-t)
  have hp : Real.exp (-M * z.im) * ‖f z‖ ≤ A := by
    simpa [hnorm, Complex.mul_re, ← mul_assoc] using
      norm_le_on_right_halfPlane hg hgb hga (z := -Complex.I * z)
        (by simpa [Complex.mul_re] using hz)
  simpa only [← mul_assoc, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, one_mul,
    mul_comm (Real.exp (M * z.im)) A] using
      mul_le_mul_of_nonneg_left hp (Real.exp_pos (M * z.im)).le

/-- Phragmén–Lindelöf bound with the sharp real-axis constant, as used in fix2:eq.complexbound. -/
theorem exponential_bound_of_real_bound {f : ℂ → ℂ} {A D M : ℝ}
    (hf : Differentiable ℂ f) (hD : ∀ z : ℂ, ‖f z‖ ≤ D * Real.exp (M * |z.im|))
    (hA : ∀ t : ℝ, ‖f t‖ ≤ A) (z : ℂ) : ‖f z‖ ≤ A * Real.exp (M * |z.im|) := by
  by_cases hz : 0 ≤ z.im
  · simpa only [abs_of_nonneg hz] using exponential_bound_upper hf hD hA hz
  · simpa only [Function.comp_apply, Pi.neg_apply, id_eq, neg_neg, Complex.neg_im, abs_of_neg (lt_of_not_ge hz)] using
      exponential_bound_upper (hf.comp differentiable_id.neg)
        (fun w => by simpa only [Function.comp_apply, Pi.neg_apply, id_eq, Complex.neg_im, abs_neg] using hD (-w))
        (fun t => by simpa only [Function.comp_apply, Pi.neg_apply, id_eq, Complex.ofReal_neg] using hA (-t))
        (z := -z) (by simpa only [Complex.neg_im] using (neg_nonneg.mpr (le_of_not_ge hz)))

theorem norm_complex_phase_le {M ω : ℝ} (hω : |ω| ≤ M) (z : ℂ) :
    ‖Complex.exp (Complex.I * z * (ω : ℂ))‖ ≤ Real.exp (M * |z.im|) := by
  have he : -z.im * ω ≤ M * |z.im| :=
    (le_abs_self (-z.im * ω)).trans ((by rw [abs_mul, abs_neg] :
      |-z.im * ω| = |z.im| * |ω|).trans_le
        ((mul_le_mul_of_nonneg_left hω (abs_nonneg _)).trans_eq (mul_comm _ _)))
  simpa [Complex.norm_exp, Complex.mul_re, Complex.mul_im] using Real.exp_le_exp.mpr he

/-- The finite-exponential-sum bound used to extend finite-propagation operators. -/
theorem norm_sum_exponentials_le {ι : Type*} (s : Finset ι) (c : ι → ℂ) (ω : ι → ℝ)
    {A M : ℝ} (hω : ∀ j ∈ s, c j ≠ 0 → |ω j| ≤ M)
    (hA : ∀ t : ℝ, ‖∑ j ∈ s, c j * Complex.exp (Complex.I * (t : ℂ) * (ω j : ℂ))‖ ≤ A)
    (z : ℂ) :
    ‖∑ j ∈ s, c j * Complex.exp (Complex.I * z * (ω j : ℂ))‖ ≤ A * Real.exp (M * |z.im|) := by
  refine exponential_bound_of_real_bound
    (f := fun w => ∑ j ∈ s, c j * Complex.exp (Complex.I * w * (ω j : ℂ))) (D := ∑ j ∈ s, ‖c j‖) (by fun_prop) ?_ hA z
  intro w
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum ?_).trans_eq (Finset.sum_mul _ _ _).symm)
  exact fun j hj => Classical.byCases (fun hc : c j = 0 => by simp [hc])
    (fun hc => (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left
      (norm_complex_phase_le (hω j hj hc) w) (norm_nonneg _)))

end DynamicalCStarAlgebras
