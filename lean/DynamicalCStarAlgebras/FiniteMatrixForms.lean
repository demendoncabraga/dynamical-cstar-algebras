import DynamicalCStarAlgebras.ScalarExponentialBounds

noncomputable section

namespace DynamicalCStarAlgebras

universe u

/-- Finite linear combinations of the canonical l2 vectors. -/
def finiteVector {X : Type u} : (X →₀ ℂ) →ₗ[ℂ] HilbertSpace X :=
  Finsupp.linearCombination ℂ delta

theorem finiteVector_single {X : Type u} (x : X) (c : ℂ) :
    finiteVector (Finsupp.single x c) = c • delta x :=
  Finsupp.linearCombination_single ℂ c x

theorem denseRange_finiteVector {X : Type u} : DenseRange (finiteVector (X := X)) := by
  classical
  intro v
  exact isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) v)
    (Filter.Eventually.of_forall fun s => subset_closure
      ((LinearMap.range (finiteVector (X := X))).sum_mem fun x _hx =>
        ⟨Finsupp.single x (v x), (finiteVector_single x (v x)).trans (single_eq_smul_delta x (v x)).symm⟩))

/-- The sesquilinear form of an arbitrary matrix on finitely supported vectors. -/
def finiteMatrixForm {X : Type u} (m : X → X → ℂ) :
    (X →₀ ℂ) →ₗ⋆[ℂ] (X →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ (fun x =>
    (LinearMap.id.smulRight (Finsupp.linearCombination ℂ (m x))).comp
      (starLinearEquiv ℂ : ℂ ≃ₗ⋆[ℂ] ℂ).toLinearMap)

theorem finiteMatrixForm_apply {X : Type u} (m : X → X → ℂ) (v w : X →₀ ℂ) :
    finiteMatrixForm m v w = ∑ x ∈ v.support, ∑ y ∈ w.support, star (v x) * (w y * m x y) := by
  simp [finiteMatrixForm, Finsupp.lsum_apply, Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum]

/-- Finite matrix forms agree with the Hilbert-space pairing of an existing operator. -/
theorem finiteMatrixForm_matrixEntry {X : Type u} (a : Operator X) (v w : X →₀ ℂ) :
    finiteMatrixForm (matrixEntry a) v w = inner ℂ (finiteVector v) (a (finiteVector w)) := by
  simp [finiteMatrixForm_apply, finiteVector, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, matrixEntry_eq_inner, Finset.mul_sum,
    mul_comm, mul_left_comm]
  exact Finset.sum_comm

theorem norm_finiteMatrixForm_matrixEntry_le {X : Type u} (a : Operator X) (v w : X →₀ ℂ) :
    ‖finiteMatrixForm (matrixEntry a) v w‖ ≤ ‖a‖ * ‖finiteVector v‖ * ‖finiteVector w‖ := by
  simpa only [finiteMatrixForm_matrixEntry, mul_left_comm, mul_assoc] using
    (norm_inner_le_norm (finiteVector v) (a (finiteVector w))).trans
      (mul_le_mul_of_nonneg_left (a.le_opNorm (finiteVector w)) (norm_nonneg _))

/-- The finite-support scalar functions used in the entire-extension construction. -/
def finiteOrbitForm {X : Type u} (h : X → ℝ) (a : Operator X) (z : ℂ) :
    (X →₀ ℂ) →ₗ⋆[ℂ] (X →₀ ℂ) →ₗ[ℂ] ℂ :=
  finiteMatrixForm (fun x y => Complex.exp (Complex.I * z * ((h x - h y : ℝ) : ℂ)) * matrixEntry a x y)

theorem finiteOrbitForm_real {X : Type u} (h : X → ℝ) (a : Operator X) (t : ℝ) :
    finiteOrbitForm h a t = finiteMatrixForm (matrixEntry (diagonalFlow h t a)) := by
  exact congrArg finiteMatrixForm (funext fun x => funext fun y => by
    simp only [matrixEntry_diagonalFlow, Complex.ofReal_mul, mul_assoc, mul_comm])

theorem finiteOrbitForm_sum {X : Type u} (h : X → ℝ) (a : Operator X) (z : ℂ)
    (v w : X →₀ ℂ) :
    finiteOrbitForm h a z v w = ∑ p ∈ v.support ×ˢ w.support,
      (star (v p.1) * w p.2 * matrixEntry a p.1 p.2) *
        Complex.exp (Complex.I * z * ((h p.1 - h p.2 : ℝ) : ℂ)) := by
  simp [finiteOrbitForm, finiteMatrixForm_apply, Finset.sum_product, mul_assoc, mul_comm, mul_left_comm]

/-- Equation fix2:eq.complexbound for all finitely supported vectors, with the exact constant. -/
theorem finiteOrbitForm_norm_le {X : Type u} (h : X → ℝ) (a : Operator X) {M : ℝ}
    (hprop : ∀ x y, M < |h x - h y| → matrixEntry a x y = 0)
    (z : ℂ) (v w : X →₀ ℂ) :
    ‖finiteOrbitForm h a z v w‖ ≤
      (‖a‖ * ‖finiteVector v‖ * ‖finiteVector w‖) * Real.exp (M * |z.im|) := by
  rw [finiteOrbitForm_sum]
  refine norm_sum_exponentials_le _ _ _
    (fun p _ hp => le_of_not_gt fun hlt => hp (by rw [hprop p.1 p.2 hlt, mul_zero])) ?_ z
  exact fun t => by
    simpa only [← finiteOrbitForm_sum, finiteOrbitForm_real, diagonalFlow_norm] using
      norm_finiteMatrixForm_matrixEntry_le (diagonalFlow h t a) v w

/-- Extend the second variable of a finite sesquilinear form by density. -/
def extendFiniteFormRight {X : Type u}
    (B : (X →₀ ℂ) →ₗ⋆[ℂ] (X →₀ ℂ) →ₗ[ℂ] ℂ) (v : X →₀ ℂ) :
    HilbertSpace X →L[ℂ] ℂ := (B v).extendOfNorm finiteVector

theorem extendFiniteFormRight_apply {X : Type u}
    (B : (X →₀ ℂ) →ₗ⋆[ℂ] (X →₀ ℂ) →ₗ[ℂ] ℂ) {C : ℝ}
    (hB : ∀ v w, ‖B v w‖ ≤ C * ‖finiteVector v‖ * ‖finiteVector w‖) (v w : X →₀ ℂ) :
    extendFiniteFormRight B v (finiteVector w) = B v w :=
  (B v).extendOfNorm_eq denseRange_finiteVector ⟨C * ‖finiteVector v‖, hB v⟩ w

theorem norm_extendFiniteFormRight_apply_le {X : Type u}
    (B : (X →₀ ℂ) →ₗ⋆[ℂ] (X →₀ ℂ) →ₗ[ℂ] ℂ) {C : ℝ}
    (hB : ∀ v w, ‖B v w‖ ≤ C * ‖finiteVector v‖ * ‖finiteVector w‖)
    (v : X →₀ ℂ) (w : HilbertSpace X) :
    ‖extendFiniteFormRight B v w‖ ≤ C * ‖finiteVector v‖ * ‖w‖ :=
  (B v).norm_extendOfNorm_apply_le denseRange_finiteVector _ (hB v) w

theorem finiteVector_dual_ext {X : Type u} {f g : HilbertSpace X →L[ℂ] ℂ}
    (hfg : ∀ v, f (finiteVector v) = g (finiteVector v)) : f = g :=
  DFunLike.ext _ _ fun w => congrFun
    (denseRange_finiteVector.equalizer f.continuous g.continuous (funext hfg)) w

/-- The first-variable semilinearity survives extension in the second variable. -/
def extendFiniteFormRightLinear {X : Type u}
    (B : (X →₀ ℂ) →ₗ⋆[ℂ] (X →₀ ℂ) →ₗ[ℂ] ℂ) {C : ℝ}
    (hB : ∀ v w, ‖B v w‖ ≤ C * ‖finiteVector v‖ * ‖finiteVector w‖) :
    (X →₀ ℂ) →ₗ⋆[ℂ] (HilbertSpace X →L[ℂ] ℂ) where
  toFun := extendFiniteFormRight B
  map_add' v w := finiteVector_dual_ext fun u => by
    simp only [extendFiniteFormRight_apply B hB, map_add, add_apply,
      LinearMap.add_apply]
  map_smul' c v := finiteVector_dual_ext fun u => by
    simp only [extendFiniteFormRight_apply B hB, map_smulₛₗ, smul_apply,
      LinearMap.smul_apply]

theorem norm_extendFiniteFormRight_le {X : Type u}
    (B : (X →₀ ℂ) →ₗ⋆[ℂ] (X →₀ ℂ) →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ v w, ‖B v w‖ ≤ C * ‖finiteVector v‖ * ‖finiteVector w‖) (v : X →₀ ℂ) :
    ‖extendFiniteFormRight B v‖ ≤ C * ‖finiteVector v‖ :=
  (extendFiniteFormRight B v).opNorm_le_bound (mul_nonneg hC (norm_nonneg _))
    (norm_extendFiniteFormRight_apply_le B hB v)

/-- Extend a uniformly bounded finite sesquilinear form in both variables. -/
def extendFiniteForm {X : Type u}
    (B : (X →₀ ℂ) →ₗ⋆[ℂ] (X →₀ ℂ) →ₗ[ℂ] ℂ) {C : ℝ}
    (hB : ∀ v w, ‖B v w‖ ≤ C * ‖finiteVector v‖ * ‖finiteVector w‖) :
    HilbertSpace X →L⋆[ℂ] HilbertSpace X →L[ℂ] ℂ :=
  (extendFiniteFormRightLinear B hB).extendOfNorm finiteVector

theorem extendFiniteForm_apply {X : Type u}
    (B : (X →₀ ℂ) →ₗ⋆[ℂ] (X →₀ ℂ) →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ v w, ‖B v w‖ ≤ C * ‖finiteVector v‖ * ‖finiteVector w‖) (v w : X →₀ ℂ) :
    extendFiniteForm B hB (finiteVector v) (finiteVector w) = B v w := by
  have he : extendFiniteForm B hB (finiteVector v) = extendFiniteFormRight B v :=
    (extendFiniteFormRightLinear B hB).extendOfNorm_eq denseRange_finiteVector
      ⟨C, norm_extendFiniteFormRight_le B hC hB⟩ v
  exact (congrArg (fun f : HilbertSpace X →L[ℂ] ℂ => f (finiteVector w)) he).trans
    (extendFiniteFormRight_apply B hB v w)

theorem norm_extendFiniteForm_apply_le {X : Type u}
    (B : (X →₀ ℂ) →ₗ⋆[ℂ] (X →₀ ℂ) →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ v w, ‖B v w‖ ≤ C * ‖finiteVector v‖ * ‖finiteVector w‖) (v : HilbertSpace X) :
    ‖extendFiniteForm B hB v‖ ≤ C * ‖v‖ :=
  (extendFiniteFormRightLinear B hB).norm_extendOfNorm_apply_le denseRange_finiteVector C
    (norm_extendFiniteFormRight_le B hC hB) v

/-- Riesz representation of the extended form, with the adjoint fixing the inner-product convention. -/
def operatorOfFiniteForm {X : Type u}
    (B : (X →₀ ℂ) →ₗ⋆[ℂ] (X →₀ ℂ) →ₗ[ℂ] ℂ) {C : ℝ}
    (hB : ∀ v w, ‖B v w‖ ≤ C * ‖finiteVector v‖ * ‖finiteVector w‖) : Operator X :=
  star (InnerProductSpace.continuousLinearMapOfBilin (extendFiniteForm B hB))

theorem inner_operatorOfFiniteForm {X : Type u}
    (B : (X →₀ ℂ) →ₗ⋆[ℂ] (X →₀ ℂ) →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ v w, ‖B v w‖ ≤ C * ‖finiteVector v‖ * ‖finiteVector w‖) (v w : X →₀ ℂ) :
    inner ℂ (finiteVector v) (operatorOfFiniteForm B hB (finiteVector w)) = B v w :=
  ((InnerProductSpace.continuousLinearMapOfBilin (extendFiniteForm B hB)).adjoint_inner_right
    (finiteVector v) (finiteVector w)).trans
      ((InnerProductSpace.continuousLinearMapOfBilin_apply _ _ _).trans
        (extendFiniteForm_apply B hC hB v w))

theorem norm_operatorOfFiniteForm_le {X : Type u}
    (B : (X →₀ ℂ) →ₗ⋆[ℂ] (X →₀ ℂ) →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ v w, ‖B v w‖ ≤ C * ‖finiteVector v‖ * ‖finiteVector w‖) :
    ‖operatorOfFiniteForm B hB‖ ≤ C := by
  refine (norm_star (InnerProductSpace.continuousLinearMapOfBilin (extendFiniteForm B hB))).trans_le
    (ContinuousLinearMap.opNorm_le_bound _ hC fun v => ?_)
  exact ((InnerProductSpace.toDual ℂ (HilbertSpace X)).symm.norm_map
    (extendFiniteForm B hB v)).trans_le (norm_extendFiniteForm_apply_le B hC hB v)

theorem matrixEntry_operatorOfFiniteForm {X : Type u}
    (B : (X →₀ ℂ) →ₗ⋆[ℂ] (X →₀ ℂ) →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ v w, ‖B v w‖ ≤ C * ‖finiteVector v‖ * ‖finiteVector w‖) (x y : X) :
    matrixEntry (operatorOfFiniteForm B hB) x y = B (Finsupp.single x 1) (Finsupp.single y 1) := by
  simpa only [finiteVector_single, one_smul, matrixEntry_eq_inner] using
    inner_operatorOfFiniteForm B hC hB (Finsupp.single x 1) (Finsupp.single y 1)

theorem finiteMatrixForm_single_one {X : Type u} (m : X → X → ℂ) (x y : X) :
    finiteMatrixForm m (Finsupp.single x 1) (Finsupp.single y 1) = m x y := by
  simp [finiteMatrixForm, Finsupp.lsum_apply]

/-- Finite vector pairings determine the operator norm bound. -/
theorem norm_le_of_finiteMatrixForm_bound {X : Type u} (a : Operator X) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ v w, ‖finiteMatrixForm (matrixEntry a) v w‖ ≤
      C * ‖finiteVector v‖ * ‖finiteVector w‖) : ‖a‖ ≤ C := by
  have he : operatorOfFiniteForm (finiteMatrixForm (matrixEntry a)) hB = a :=
    operator_ext fun x y => (matrixEntry_operatorOfFiniteForm _ hC hB x y).trans
      (finiteMatrixForm_single_one _ x y)
  exact (congrArg norm he).symm.trans_le (norm_operatorOfFiniteForm_le _ hC hB)

end DynamicalCStarAlgebras
