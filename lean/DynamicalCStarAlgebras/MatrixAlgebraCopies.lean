import DynamicalCStarAlgebras.OzawaEntanglement

noncomputable section
open Classical InnerProductSpace

namespace DynamicalCStarAlgebras

/-- An injective homomorphism of Hilbert-space operator algebras contains an
isometric copy of the defining representation, obtained from a rank-one corner. -/
theorem exists_isometric_intertwiner_of_injective_starHom
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (Φ : (H →L[ℂ] H) →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hΦ : Function.Injective Φ)
    (u : H) (hu : ‖u‖ = 1) :
    ∃ e : H →ₗᵢ[ℂ] K, ∀ A x, Φ A (e x) = e (A x) := by
  let p := rankOne ℂ u u
  have hp : p * p = p := isIdempotentElem_rankOne_self hu
  have hp0 : p ≠ 0 := by
    intro h
    have hpu := congrArg (fun A : H →L[ℂ] H => A u) h
    have hu0 : u ≠ 0 := by intro h; simp [h] at hu
    apply hu0
    simpa [p, inner_self_eq_norm_sq_to_K, hu] using hpu
  have hq0 : Φ p ≠ 0 := fun h => hp0 (hΦ (by simpa using h))
  obtain ⟨w, hw⟩ : ∃ w, Φ p w ≠ 0 := by
    by_contra! h
    apply hq0
    ext w
    exact h w
  let v := (‖Φ p w‖ : ℂ)⁻¹ • Φ p w
  have hv : ‖v‖ = 1 := by
    simp [v, norm_smul, norm_inv, Complex.norm_real, norm_ne_zero_iff.mpr hw]
  have hpv : Φ p v = v := by
    have hq : Φ p * Φ p = Φ p := by rw [← map_mul, hp]
    have hqw := congrArg (fun A : K →L[ℂ] K => A w) hq
    simpa only [v, map_smul, mul_apply_eq_comp] using
      congrArg (fun z => (‖Φ p w‖ : ℂ)⁻¹ • z) hqw
  let f : H →ₗ[ℂ] K :=
    { toFun x := Φ (rankOne ℂ x u) v
      map_add' x y := by simp
      map_smul' c x := by simp }
  have hf (x y : H) : inner ℂ (f x) (f y) = inner ℂ x y := by
    change inner ℂ (Φ (rankOne ℂ x u) v) (Φ (rankOne ℂ y u) v) = _
    rw [← ContinuousLinearMap.adjoint_inner_right]
    have hprod : (Φ (rankOne ℂ x u)).adjoint * Φ (rankOne ℂ y u) =
        (inner ℂ x y) • Φ p := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, ← map_mul]
      simp only [ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne,
        ContinuousLinearMap.mul_def, rankOne_comp_rankOne, map_smul]
      rfl
    rw [← mul_apply_eq_comp, hprod, smul_apply, hpv, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hv]
    simp
  exact ⟨f.isometryOfInner hf, by
    intro A x
    change Φ A (Φ (rankOne ℂ x u) v) = Φ (rankOne ℂ (A x) u) v
    rw [← mul_apply_eq_comp, ← map_mul]
    congr 2
    exact comp_rankOne x u A⟩

/-- The lower amplification estimate also permits an arbitrary operator in
the complementary corner, exactly as in Ozawa's finite-matrix obstruction. -/
theorem matrix_embedding_amplification_norm_lower_bound
    {J H K : Type*} [Fintype J] [Nonempty J]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (b : OrthonormalBasis J ℂ H) [Fintype (signedBasisGroup b)]
    (Φ : (H →L[ℂ] H) →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hΦ : Function.Injective Φ)
    (B : signedBasisGroup b → K →L[ℂ] K)
    (hB : ∀ g, B g * Φ 1 = 0) :
    1 ≤ ‖(Fintype.card (signedBasisGroup b) : ℂ)⁻¹ •
      ∑ g : signedBasisGroup b,
        TensorProduct.mapL (Φ g.val.toLinearIsometry.toContinuousLinearMap + B g)
          g.val.toLinearIsometry.toContinuousLinearMap‖ := by
  let j : J := Classical.choice inferInstance
  obtain ⟨e, he⟩ := exists_isometric_intertwiner_of_injective_starHom Φ hΦ (b j)
    (b.norm_eq_one j)
  apply signed_unitary_amplification_norm_lower_bound b e
  intro g x
  have hzero : B g (e x) = 0 := by
    have hunit : Φ 1 (e x) = e x := by simpa using he 1 x
    rw [← hunit, ← mul_apply_eq_comp, hB]
    rfl
  simp only [add_apply, he, hzero, add_zero]
  rfl

end DynamicalCStarAlgebras
