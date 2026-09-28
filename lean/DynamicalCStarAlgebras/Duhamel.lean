import DynamicalCStarAlgebras.BoundedCommutators

noncomputable section

namespace DynamicalCStarAlgebras

open MeasureTheory

universe u

/-- A bounded operator realizing the manuscript's first entrywise commutator. -/
def HasDiagonalCommutator {X : Type u} (h : X → ℝ) (a b : Operator X) : Prop :=
  ∀ x y, matrixEntry b x y = ((h x - h y : ℝ) : ℂ) * matrixEntry a x y

theorem intervalIntegrable_diagonalFlow_apply {X : Type u} (h : X → ℝ)
    (b : Operator X) (v : HilbertSpace X) (t : ℝ) :
    IntervalIntegrable (fun s => Complex.I • diagonalFlow h s b v) volume 0 t :=
  ((continuous_const : Continuous (fun _ : ℝ => Complex.I)).smul
    (continuous_diagonalFlow_apply h b v)).intervalIntegrable 0 t

def duhamelLinearMap {X : Type u} (h : X → ℝ) (b : Operator X) (t : ℝ) :
    HilbertSpace X →ₗ[ℂ] HilbertSpace X where
  toFun v := ∫ s in 0..t, Complex.I • diagonalFlow h s b v
  map_add' v w := by
    simpa only [map_add, smul_add] using
      intervalIntegral.integral_add (intervalIntegrable_diagonalFlow_apply h b v t)
        (intervalIntegrable_diagonalFlow_apply h b w t)
  map_smul' c v := by
    simp only [map_smul, smul_comm Complex.I c, intervalIntegral.integral_smul,
      RingHom.id_apply]

theorem duhamelLinearMap_norm_le {X : Type u} (h : X → ℝ) (b : Operator X)
    (t : ℝ) (v : HilbertSpace X) :
    ‖duhamelLinearMap h b t v‖ ≤ (|t| * ‖b‖) * ‖v‖ := by
  have hb : ∀ s ∈ Set.uIoc 0 t, ‖Complex.I • diagonalFlow h s b v‖ ≤ ‖b‖ * ‖v‖ :=
    fun s _ => by simpa only [norm_smul, Complex.norm_I, one_mul] using
      diagonalFlow_apply_norm_le h s b v
  simpa only [duhamelLinearMap, LinearMap.coe_mk, AddHom.coe_mk, sub_zero,
    mul_assoc, mul_comm, mul_left_comm] using intervalIntegral.norm_integral_le_of_norm_le_const hb

/-- The weak oriented integral of i times the conjugated commutator. -/
def duhamelOperator {X : Type u} (h : X → ℝ) (b : Operator X) (t : ℝ) : Operator X :=
  (duhamelLinearMap h b t).mkContinuous (|t| * ‖b‖) (duhamelLinearMap_norm_le h b t)

theorem duhamelOperator_norm_le {X : Type u} (h : X → ℝ) (b : Operator X) (t : ℝ) :
    ‖duhamelOperator h b t‖ ≤ |t| * ‖b‖ :=
  (duhamelLinearMap h b t).mkContinuous_norm_le
    (mul_nonneg (abs_nonneg t) (norm_nonneg b)) (duhamelLinearMap_norm_le h b t)

theorem matrixEntry_duhamelOperator {X : Type u} (h : X → ℝ) (b : Operator X)
    (t : ℝ) (x y : X) :
    matrixEntry (duhamelOperator h b t) x y =
      ∫ s in 0..t, Complex.I * matrixEntry (diagonalFlow h s b) x y := by
  change (∫ s in 0..t, Complex.I • diagonalFlow h s b (delta y)) x = _
  simpa only [lp.evalCLM, LinearMap.mkContinuous_apply, lp.evalₗ_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, matrixEntry] using
    ((lp.evalCLM ℂ (fun _ : X => ℂ) 2 x).intervalIntegral_comp_comm
      (intervalIntegrable_diagonalFlow_apply h b (delta y) t)).symm

theorem hasDerivAt_phase_mul (ξ : ℝ) (z : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (((t * ξ : ℝ) : ℂ) * Complex.I) * z)
      (Complex.I * (Complex.exp (((s * ξ : ℝ) : ℂ) * Complex.I) * ((ξ : ℂ) * z))) s := by
  convert! ((((hasDerivAt_id s).mul_const ξ).ofReal_comp.mul_const Complex.I).cexp.mul_const z) using 1
  simp only [id_eq, one_mul, mul_assoc, mul_left_comm]

theorem integral_phase_mul (ξ : ℝ) (z : ℂ) (t : ℝ) :
    (∫ s in 0..t, Complex.I *
      (Complex.exp (((s * ξ : ℝ) : ℂ) * Complex.I) * ((ξ : ℂ) * z))) =
        Complex.exp (((t * ξ : ℝ) : ℂ) * Complex.I) * z - z := by
  have hc : Continuous (fun s : ℝ => Complex.I *
      (Complex.exp (((s * ξ : ℝ) : ℂ) * Complex.I) * ((ξ : ℂ) * z))) := by
    fun_prop
  simpa only [zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul] using!
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_phase_mul ξ z s)
      (hc.intervalIntegrable 0 t)

/-- The weak Duhamel identity, without boundedness of h or norm continuity assumptions. -/
theorem duhamelOperator_eq_sub {X : Type u} (h : X → ℝ) (a b : Operator X)
    (hab : HasDiagonalCommutator h a b) (t : ℝ) :
    duhamelOperator h b t = diagonalFlow h t a - a := by
  refine operator_ext fun x y => ?_
  simp only [matrixEntry_duhamelOperator, matrixEntry_diagonalFlow, hab x y, integral_phase_mul]
  change _ = matrixEntry (diagonalFlow h t a) x y - matrixEntry a x y
  rw [matrixEntry_diagonalFlow]

/-- Lemma Duhamel: bounded entrywise commutator implies the exact linear orbit bound. -/
theorem duhamel_norm_le {X : Type u} (h : X → ℝ) (a b : Operator X)
    (hab : HasDiagonalCommutator h a b) (t : ℝ) :
    ‖diagonalFlow h t a - a‖ ≤ |t| * ‖b‖ :=
  duhamelOperator_eq_sub h a b hab t ▸ duhamelOperator_norm_le h b t

/-- Bounded entrywise commutators give globally Lipschitz orbits. -/
theorem lipschitzWith_diagonalFlow_of_commutator {X : Type u} (h : X → ℝ)
    (a b : Operator X) (hab : HasDiagonalCommutator h a b) :
    LipschitzWith ⟨‖b‖, norm_nonneg b⟩ (fun t : ℝ => diagonalFlow h t a) := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rw [← diagonalFlow_dist h (-t), ← diagonalFlow_add, ← diagonalFlow_add,
    neg_add_cancel, diagonalFlow_zero]
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_mk, sub_eq_add_neg,
    add_comm (-t) s, mul_comm] using! duhamel_norm_le h a b hab (-t + s)

end DynamicalCStarAlgebras
