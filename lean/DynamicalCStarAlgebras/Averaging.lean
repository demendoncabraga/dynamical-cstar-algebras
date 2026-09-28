import DynamicalCStarAlgebras.StrongContinuity

namespace DynamicalCStarAlgebras

open MeasureTheory

universe u

theorem diagonalFlow_apply_norm_le {X : Type u} (h : X → ℝ) (t : ℝ)
    (a : Operator X) (v : HilbertSpace X) : ‖diagonalFlow h t a v‖ ≤ ‖a‖ * ‖v‖ := by
  simpa only [diagonalFlow_norm] using (diagonalFlow h t a).le_opNorm v

theorem integrable_diagonalFlow_smul {X : Type u} (h : X → ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) (a : Operator X) (v : HilbertSpace X) :
    Integrable (fun t => f t • diagonalFlow h t a v) :=
  hf.smul_bdd (‖a‖ * ‖v‖) (continuous_diagonalFlow_apply h a v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => diagonalFlow_apply_norm_le h t a v)

noncomputable def averagingLinearMap {X : Type u} (h : X → ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) (a : Operator X) : HilbertSpace X →ₗ[ℂ] HilbertSpace X where
  toFun v := ∫ t, f t • diagonalFlow h t a v
  map_add' v w := by
    simpa only [map_add, smul_add] using
      integral_add (integrable_diagonalFlow_smul h hf a v)
        (integrable_diagonalFlow_smul h hf a w)
  map_smul' c v := by
    simp only [map_smul, smul_comm (f _) c, integral_smul, RingHom.id_apply]

theorem averagingLinearMap_norm_le {X : Type u} (h : X → ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) (a : Operator X) (v : HilbertSpace X) :
    ‖averagingLinearMap h hf a v‖ ≤ ((∫ t, ‖f t‖) * ‖a‖) * ‖v‖ := by
  have hb : ∀ᵐ t : ℝ, ‖f t • diagonalFlow h t a v‖ ≤ ‖f t‖ * (‖a‖ * ‖v‖) :=
    Filter.Eventually.of_forall fun t => (norm_smul (f t) _).le.trans
      (mul_le_mul_of_nonneg_left (diagonalFlow_apply_norm_le h t a v) (norm_nonneg _))
  simpa only [averagingLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    integral_mul_const, mul_assoc] using
    norm_integral_le_of_norm_le (hf.norm.mul_const (‖a‖ * ‖v‖)) hb

/-- Section 3: the weak averaging operator, constructed by integrating its vector orbits. -/
noncomputable def averagingOperator {X : Type u} (h : X → ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) (a : Operator X) : Operator X :=
  (averagingLinearMap h hf a).mkContinuous ((∫ t, ‖f t‖) * ‖a‖)
    (averagingLinearMap_norm_le h hf a)

theorem averagingOperator_apply {X : Type u} (h : X → ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) (a : Operator X) (v : HilbertSpace X) :
    averagingOperator h hf a v = ∫ t, f t • diagonalFlow h t a v := rfl

/-- Equation BoundNormThetafa, with the L1 norm written as the integral of the norm. -/
theorem averagingOperator_norm_le {X : Type u} (h : X → ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) (a : Operator X) :
    ‖averagingOperator h hf a‖ ≤ (∫ t, ‖f t‖) * ‖a‖ :=
  (averagingLinearMap h hf a).mkContinuous_norm_le
    (mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (norm_nonneg _))
    (averagingLinearMap_norm_le h hf a)

/-- The weak integral identity; inner-product arguments are reversed to match Mathlib. -/
theorem inner_averagingOperator {X : Type u} (h : X → ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) (a : Operator X) (v w : HilbertSpace X) :
    inner ℂ w (averagingOperator h hf a v) =
      ∫ t, f t * inner ℂ w (diagonalFlow h t a v) := by
  simpa only [averagingOperator_apply, inner_smul_right] using
    (integral_inner (𝕜 := ℂ) (integrable_diagonalFlow_smul h hf a v) w).symm

/-- The manuscript's Fourier convention, without a 2π factor and with positive sign. -/
noncomputable def fourierPlus (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ t : ℝ, f t * Complex.exp (((t * ξ : ℝ) : ℂ) * Complex.I)

/-- Equation Theta.Schur.mult: averaging is Schur multiplication by the Fourier transform. -/
theorem matrixEntry_averagingOperator {X : Type u} (h : X → ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) (a : Operator X) (x y : X) :
    matrixEntry (averagingOperator h hf a) x y =
      fourierPlus f (h x - h y) * matrixEntry a x y := by
  rw [matrixEntry_eq_inner, inner_averagingOperator]
  simp only [← matrixEntry_eq_inner, matrixEntry_diagonalFlow, ← mul_assoc,
    integral_mul_const, fourierPlus]

theorem integrable_diagonalFlow_operator_smul {X : Type u} (h : X → ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) (a : Operator X) (ha : a ∈ continuityPoints h) :
    Integrable (fun t => f t • diagonalFlow h t a) :=
  hf.smul_bdd ‖a‖ ha.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => (diagonalFlow_norm h t a).le)

/-- At a norm-continuity point, the weak average equals the operator-valued Bochner integral. -/
theorem averagingOperator_eq_integral {X : Type u} (h : X → ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) (a : Operator X) (ha : a ∈ continuityPoints h) :
    averagingOperator h hf a = ∫ t, f t • diagonalFlow h t a := by
  apply ContinuousLinearMap.ext
  exact fun v => ((ContinuousLinearMap.apply ℂ (HilbertSpace X) v).integral_comp_comm
    (integrable_diagonalFlow_operator_smul h hf a ha))

theorem averagingOperator_sub_eq_integral {X : Type u} (h : X → ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) (a : Operator X) (ha : a ∈ continuityPoints h)
    (hmass : ∫ t, f t = 1) :
    averagingOperator h hf a - a = ∫ t, f t • (diagonalFlow h t a - a) := by
  simp only [smul_sub, integral_sub (integrable_diagonalFlow_operator_smul h hf a ha)
    (hf.smul_const a), integral_smul_const, hmass, one_smul,
    averagingOperator_eq_integral h hf a ha]

/-- The norm estimate used in Equation 1.03.Aug.26, also valid for complex kernels. -/
theorem averagingOperator_sub_norm_le {X : Type u} (h : X → ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) (a : Operator X) (ha : a ∈ continuityPoints h)
    (hmass : ∫ t, f t = 1) :
    ‖averagingOperator h hf a - a‖ ≤ ∫ t, ‖f t‖ * ‖diagonalFlow h t a - a‖ := by
  simpa only [averagingOperator_sub_eq_integral h hf a ha hmass, norm_smul] using
    norm_integral_le_integral_norm (fun t => f t • (diagonalFlow h t a - a))

theorem integral_mem_closedComplexSubmodule {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (S : Submodule ℂ E)
    (hS : IsClosed (S : Set E)) (f : ℝ → E) (hf : ∀ t, f t ∈ S) :
    (∫ t, f t) ∈ S := by
  let : IsClosed (S : Set E) := hS
  exact (S.subtypeL.integral_comp_comm' isometry_subtype_coe.antilipschitz
    (fun t => ⟨f t, hf t⟩)).symm ▸ (∫ t, (⟨f t, hf t⟩ : S)).property

/-- The invariant-subalgebra step in Theorem A; no identity element is required in A. -/
theorem averagingOperator_mem_invariant_subalgebra {X : Type u} (h : X → ℝ)
    {f : ℝ → ℂ} (hf : Integrable f) (A : NonUnitalStarSubalgebra ℂ (Operator X))
    (hA : IsClosed (A : Set (Operator X)))
    (hinv : ∀ t a, a ∈ A → diagonalFlow h t a ∈ A)
    (a : Operator X) (ha : a ∈ continuityPoints h) (haA : a ∈ A) :
    averagingOperator h hf a ∈ A := by
  rw [averagingOperator_eq_integral h hf a ha]
  exact integral_mem_closedComplexSubmodule A.toNonUnitalSubalgebra.toSubmodule hA _
    (fun t => A.smul_mem (f t) (hinv t a haA))

theorem averagingOperator_congr_ae {X : Type u} (h : X → ℝ) {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (hfg : f =ᵐ[volume] g) (a : Operator X) :
    averagingOperator h hf a = averagingOperator h hg a :=
  ContinuousLinearMap.ext fun v => integral_congr_ae
    (hfg.mono fun t ht => congrArg (fun c : ℂ => c • diagonalFlow h t a v) ht)

/-- Averaging with the kernel supplied as an L1 equivalence class. -/
noncomputable def averagingOperatorL1 {X : Type u} (h : X → ℝ)
    (f : ℝ →₁[volume] ℂ) (a : Operator X) : Operator X :=
  averagingOperator h (L1.integrable_coeFn f) a

theorem averagingOperatorL1_toL1 {X : Type u} (h : X → ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) (a : Operator X) :
    averagingOperatorL1 h (hf.toL1 f) a = averagingOperator h hf a :=
  averagingOperator_congr_ae h _ hf hf.coeFn_toL1 a

theorem averagingOperatorL1_norm_le {X : Type u} (h : X → ℝ)
    (f : ℝ →₁[volume] ℂ) (a : Operator X) : ‖averagingOperatorL1 h f a‖ ≤ ‖f‖ * ‖a‖ := by
  simpa only [averagingOperatorL1, L1.norm_eq_integral_norm] using
    averagingOperator_norm_le h (L1.integrable_coeFn f) a

end DynamicalCStarAlgebras
