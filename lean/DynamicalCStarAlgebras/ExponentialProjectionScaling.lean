import DynamicalCStarAlgebras.BoundedMatrixProducts

noncomputable section

open scoped ENNReal

namespace DynamicalCStarAlgebras

lemma subspace_corner_supported {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (W : Submodule ℂ H) [CompleteSpace W]
    (a : W →L[ℂ] W) :
    W.starProjection * isometryCornerHom W.subtypeₗᵢ a = isometryCornerHom W.subtypeₗᵢ a ∧
      isometryCornerHom W.subtypeₗᵢ a * W.starProjection = isometryCornerHom W.subtypeₗᵢ a := by
  have hleft (b : W →L[ℂ] W) :
      W.starProjection * isometryCornerHom W.subtypeₗᵢ b = isometryCornerHom W.subtypeₗᵢ b := by
    ext x
    apply W.starProjection_eq_self_iff.mpr
    exact (b (W.subtypeₗᵢ.toContinuousLinearMap.adjoint x)).property
  refine ⟨hleft a, ?_⟩
  have h := congrArg star (hleft (star a))
  simpa only [map_star, star_mul, star_star, (isSelfAdjoint_starProjection W).star_eq] using h

lemma componentOperator_smul {X Y : Type*} (ι : Y → X) (hι : Function.Injective ι)
    (c : ℂ) (a : Operator X) :
    componentOperator ι hι (c • a) = c • componentOperator ι hι a := by
  ext v
  simp [componentOperator]

/-- Scaling removes the contraction restriction from the good-subspace proof
of exponential decay. -/
theorem CoarseGraphUnion.good_projection_block_hasExponentialDecay
    {X : Type*} [PseudoMetricSpace X] (D : CoarseGraphUnion X)
    (a : Operator X)
    (hblock : ∀ x y, D.component x ≠ D.component y → matrixEntry a x y = 0)
    {γ C : ℝ} (hγ : 0 < γ) (hC : 1 ≤ C)
    (hExp : ∀ n, letI := @Fintype.ofFinite {x : X // D.component x = n} (D.finite n)
      HasVertexExpansion (D.graph n) γ)
    (hdata : ∀ n,
      let b := componentOperator (fun x : {x : X // D.component x = n} => (x : X))
        Subtype.val_injective a
      ∃ (m : ℕ) (p : Operator {x : X // D.component x = n}),
        IsSelfAdjoint p ∧ (Nat.card {x : X // D.component x = n} : ℝ) ^ (1 / 4 : ℝ) ≤ m ∧
        p * b = b ∧ b * p = b ∧
        ∀ (S : Finset {x : X // D.component x = n}) (δ : ℝ),
          1 / (m : ℝ) ≤ δ → δ ≤ 1 / 2 →
          (S.card : ℝ) ≤ δ * Nat.card {x : X // D.component x = n} →
          ‖coordinateProjection (S : Set {x : X // D.component x = n}) * p‖ ≤
            C * Real.sqrt (δ * Real.log (1 / δ))) :
    HasExponentialDecay a := by
  let M : ℝ := ‖a‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let c : ℂ := (M⁻¹ : ℝ)
  have hc : ‖c‖ = M⁻¹ := by
    exact Complex.norm_real _ |>.trans (abs_of_pos (inv_pos.mpr hM))
  have hnorm : ‖c • a‖ ≤ 1 := by
    rw [norm_smul, hc]
    apply (inv_mul_le_iff₀ hM).mpr
    dsimp [M]
    linarith
  have hblock' : ∀ x y, D.component x ≠ D.component y → matrixEntry (c • a) x y = 0 := by
    intro x y hxy
    rw [matrixEntry_smul, hblock x y hxy, mul_zero]
  obtain ⟨κ, hκ, hmod, hdecay⟩ := D.good_projection_block_exponential_bound
    (c • a) hnorm hblock' hγ hC hExp (by
      intro n
      obtain ⟨m, p, hp, hm, hleft, hright, hgood⟩ := hdata n
      refine ⟨m, p, hp, hm, ?_, ?_, hgood⟩
      · simp only [componentOperator_smul, mul_smul_comm, hleft]
      · simp only [componentOperator_smul, smul_mul_assoc, hright])
  have hrecover : (M : ℂ) • (c • a) = a := by
    rw [smul_smul]
    have he : (M : ℂ) * c = 1 := by
      dsimp [c]
      norm_cast
      exact mul_inv_cancel₀ hM.ne'
    rw [he, one_smul]
  exact hrecover ▸ hdecay.smul (M : ℂ)

end DynamicalCStarAlgebras
