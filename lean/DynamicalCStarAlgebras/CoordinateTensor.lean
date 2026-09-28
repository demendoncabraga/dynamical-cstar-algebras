import DynamicalCStarAlgebras.MatrixAlgebraCopies

noncomputable section
open Classical TensorProduct

namespace DynamicalCStarAlgebras

variable {X J : Type*}

def productSliceEmbedding (j : J) : HilbertSpace X →ₗᵢ[ℂ] HilbertSpace (X × J) :=
  coordinateEmbedding (fun x => (x, j)) (fun _ _ h => congrArg Prod.fst h)

lemma productSliceEmbedding_inner (j k : J) (v w : HilbertSpace X) :
    inner ℂ (productSliceEmbedding j v) (productSliceEmbedding k w) =
      if j = k then inner ℂ v w else 0 := by
  by_cases hjk : j = k
  · subst k
    simp only [ite_true, LinearIsometry.inner_map_map]
  · rw [if_neg hjk]
    have hzero : (productSliceEmbedding (X := X) j).toContinuousLinearMap.adjoint.comp
        (productSliceEmbedding k).toContinuousLinearMap = 0 := by
      apply operator_ext
      intro x y
      rw [matrixEntry_eq_inner]
      change inner ℂ (delta x)
        ((productSliceEmbedding j).toContinuousLinearMap.adjoint
          ((productSliceEmbedding k).toContinuousLinearMap (delta y))) = 0
      rw [ContinuousLinearMap.adjoint_inner_right]
      change inner ℂ (coordinateEmbedding (fun x : X => (x, j)) (fun _ _ h => congrArg Prod.fst h) (delta x))
        (coordinateEmbedding (fun x : X => (x, k)) (fun _ _ h => congrArg Prod.fst h) (delta y)) = 0
      erw [coordinateEmbedding_delta, coordinateEmbedding_delta]
      simp [delta, lp.inner_single_left, lp.single_apply, hjk]
    change inner ℂ ((productSliceEmbedding j).toContinuousLinearMap v)
      ((productSliceEmbedding k).toContinuousLinearMap w) = 0
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply,
      hzero, zero_apply, inner_zero_right]

variable [Fintype J]

def coordinateTensorMap : (HilbertSpace X ⊗[ℂ] HilbertSpace J) →ₗ[ℂ]
    HilbertSpace (X × J) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ
    (fun v w => ∑ j : J, w j • productSliceEmbedding j v)
    (by intro v w z; simp [smul_add, Finset.sum_add_distrib])
    (by
      intro c v w
      simp only [map_smul, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact smul_comm (w j) c _)
    (by intro v w z; simp [add_smul, Finset.sum_add_distrib])
    (by intro c v w; simp [Finset.smul_sum, smul_smul]))

lemma coordinateTensorMap_tmul (v : HilbertSpace X) (w : HilbertSpace J) :
    coordinateTensorMap (v ⊗ₜ[ℂ] w) = ∑ j, w j • productSliceEmbedding j v := rfl

lemma coordinateTensorMap_inner_tmul (v v' : HilbertSpace X) (w w' : HilbertSpace J) :
    inner ℂ (coordinateTensorMap (v ⊗ₜ[ℂ] w)) (coordinateTensorMap (v' ⊗ₜ[ℂ] w')) =
      inner ℂ (v ⊗ₜ[ℂ] w) (v' ⊗ₜ[ℂ] w') := by
  simp only [coordinateTensorMap_tmul, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, productSliceEmbedding_inner, TensorProduct.inner_tmul]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [lp.inner_eq_tsum w w', tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [RCLike.inner_apply]
  ring

lemma coordinateTensorMap_inner (v w : HilbertSpace X ⊗[ℂ] HilbertSpace J) :
    inner ℂ (coordinateTensorMap v) (coordinateTensorMap w) = inner ℂ v w := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, inner_add_left, hx, hy]
  | tmul x y =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add v w hv hw => simp only [map_add, inner_add_right, hv, hw]
    | tmul v w => exact coordinateTensorMap_inner_tmul x v y w

def coordinateTensorIsometry :
    (HilbertSpace X ⊗[ℂ] HilbertSpace J) →ₗᵢ[ℂ] HilbertSpace (X × J) :=
  coordinateTensorMap.isometryOfInner coordinateTensorMap_inner

lemma coordinateTensorMap_tmul_delta (v : HilbertSpace X) (j : J) :
    coordinateTensorMap (v ⊗ₜ[ℂ] delta j) = productSliceEmbedding j v := by
  simp [coordinateTensorMap_tmul, delta, lp.single_apply]

lemma coordinateTensorMap_surjective :
    Function.Surjective (coordinateTensorMap (X := X) (J := J)) := by
  have hs : (∑ j : J, (productSliceEmbedding (X := X) j).toContinuousLinearMap.comp
      (productSliceEmbedding j).toContinuousLinearMap.adjoint) = 1 := by
    have he (j : J) : (productSliceEmbedding (X := X) j).toContinuousLinearMap.comp
        (productSliceEmbedding j).toContinuousLinearMap.adjoint =
          coordinateProjection {p : X × J | p.2 = j} := by
      erw [productSliceEmbedding, coordinateEmbedding_mul_adjoint]
      congr 1
      ext ⟨x, k⟩
      simp [eq_comm]
    simp only [he]
    apply ContinuousLinearMap.ext
    intro v
    apply lp.ext
    funext p
    simp only [sum_apply, one_apply_eq_self]
    change (∑ j : J, coordinateProjection {p : X × J | p.2 = j} v) p = v p
    rw [lp.coeFn_sum]
    erw [Finset.sum_apply]
    simp [coordinateProjection_apply_ite]
  intro v
  refine ⟨∑ j : J, (productSliceEmbedding j).toContinuousLinearMap.adjoint v ⊗ₜ[ℂ] delta j, ?_⟩
  simpa only [map_sum, coordinateTensorMap_tmul_delta, sum_apply,
    ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    one_apply_eq_self] using congrArg (fun A : Operator (X × J) => A v) hs

/-- The Hilbert tensor product with a finite coordinate space is the coordinate
Hilbert space of the product. -/
def coordinateTensorEquiv :
    (HilbertSpace X ⊗[ℂ] HilbertSpace J) ≃ₗᵢ[ℂ] HilbertSpace (X × J) :=
  LinearIsometryEquiv.ofSurjective coordinateTensorIsometry coordinateTensorMap_surjective

lemma coordinateTensorEquiv_apply (v : HilbertSpace X ⊗[ℂ] HilbertSpace J) :
    coordinateTensorEquiv v = coordinateTensorMap v := rfl

lemma coordinateTensorEquiv_delta (x : X) (j : J) :
    coordinateTensorEquiv (delta x ⊗ₜ[ℂ] delta j) = delta (x, j) := by
  rw [coordinateTensorEquiv_apply, coordinateTensorMap_tmul_delta]
  exact coordinateEmbedding_delta _ _ _

/-- Transporting bounded operators by a Hilbert-space isometric equivalence
preserves their operator norm. -/
def operatorConjugationIsometry {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (e : H ≃ₗᵢ[ℂ] K) :
    (H →L[ℂ] H) ≃ₗᵢ[ℂ] (K →L[ℂ] K) :=
  { (e.toContinuousLinearEquiv.arrowCongr e.toContinuousLinearEquiv).toLinearEquiv with
    norm_map' := by
      intro A
      apply le_antisymm
      · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
        intro x
        change ‖e (A (e.symm x))‖ ≤ ‖A‖ * ‖x‖
        rw [e.norm_map]
        simpa using A.le_opNorm (e.symm x)
      · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
        intro x
        have h := (e.toContinuousLinearEquiv.arrowCongr e.toContinuousLinearEquiv A).le_opNorm (e x)
        change ‖e (A (e.symm (e x)))‖ ≤ _ * ‖e x‖ at h
        simpa using h }

lemma operatorConjugationIsometry_apply {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (e : H ≃ₗᵢ[ℂ] K) (A : H →L[ℂ] H) (x : K) :
    operatorConjugationIsometry e A x = e (A (e.symm x)) := rfl

lemma coordinateTensor_matrixEntry (A : Operator X) (B : Operator J) (x y : X) (j k : J) :
    matrixEntry (operatorConjugationIsometry coordinateTensorEquiv (TensorProduct.mapL A B))
      (x, j) (y, k) = matrixEntry A x y * matrixEntry B j k := by
  rw [matrixEntry_eq_inner, ← coordinateTensorEquiv_delta x j,
    ← coordinateTensorEquiv_delta y k, operatorConjugationIsometry_apply,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.inner_map_map,
    TensorProduct.mapL_tmul, TensorProduct.inner_tmul]
  rw [matrixEntry_eq_inner, matrixEntry_eq_inner]

end DynamicalCStarAlgebras
