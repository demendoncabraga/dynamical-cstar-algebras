import DynamicalCStarAlgebras.CoordinateTensor

noncomputable section
open Classical TensorProduct

namespace DynamicalCStarAlgebras

lemma tensor_average_sub_norm_le {G H K : Type*} [Fintype G] [Nonempty G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (A C : G → K →L[ℂ] K) (U : G → H →L[ℂ] H) {ε : ℝ} (hε : 0 ≤ ε)
    (hAC : ∀ g, ‖A g - C g‖ ≤ ε) (hU : ∀ g, ‖U g‖ ≤ 1) :
    ‖(Fintype.card G : ℂ)⁻¹ • (∑ g, TensorProduct.mapL (A g) (U g)) -
      (Fintype.card G : ℂ)⁻¹ • (∑ g, TensorProduct.mapL (C g) (U g))‖ ≤ ε := by
  let : NormedAddCommGroup (K ⊗[ℂ] H →L[ℂ] K ⊗[ℂ] H) := inferInstance
  let : NormedSpace ℂ (K ⊗[ℂ] H →L[ℂ] K ⊗[ℂ] H) := inferInstance

  have hmap (g : G) : TensorProduct.mapL (A g) (U g) - TensorProduct.mapL (C g) (U g) =
      TensorProduct.mapL (A g - C g) (U g) := by
    apply ContinuousLinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [TensorProduct.sub_tmul]
    | add x y hx hy => simp_all only [map_add, sub_apply]
  have he := smul_sub (Fintype.card G : ℂ)⁻¹
    (∑ g, TensorProduct.mapL (A g) (U g)) (∑ g, TensorProduct.mapL (C g) (U g))
  rw [← he, ← Finset.sum_sub_distrib]
  simp_rw [hmap]
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  have hc : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ε := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
      apply (norm_sum_le Finset.univ (fun g : G => TensorProduct.mapL (A g - C g) (U g))).trans
      apply Finset.sum_le_sum
      intro g _
      exact (TensorProduct.norm_mapL_le _ _).trans
        (by simpa using mul_le_mul (hAC g) (hU g) (norm_nonneg _) hε)
    _ = ε := by simp [hc.ne']

/-- Ozawa's finite-matrix obstruction with a qualitative dimension threshold.
The N^2 matching partition changes the threshold, while retaining the uniform
one-half distance needed for the bounded-product nonembedding theorem. -/
theorem controlled_finite_matrix_obstruction {X : Type*} (C : CoarseStructure X)
    (hC : C.UniformlyLocallyFinite) (E : Set (X × X)) (hE : E ∈ C.controlled) :
    ∃ N : ℕ, ∀ {J : Type*} [Fintype J] [Nonempty J],
      6 * (N : ℝ) ^ 2 < Real.sqrt (Fintype.card J) →
      ∀ (Φ : Operator J →⋆ₙₐ[ℂ] Operator X), Function.Injective Φ →
      ∃ a : Operator J, ‖a‖ ≤ 1 ∧ ∀ B : Operator X, ‖B‖ ≤ 1 → B * Φ 1 = 0 →
        ∀ c : Operator X, (∀ x y, (x, y) ∉ E → matrixEntry c x y = 0) →
          (1 / 2 : ℝ) ≤ ‖Φ a + B - c‖ := by
  obtain ⟨N, hN⟩ := controlled_unitary_amplification_norm_bound C hC E hE
  refine ⟨N, ?_⟩
  intro J _ _ hdim Φ hΦ
  let b := deltaBasis J
  let G := signedBasisGroup b
  let : Fintype G := Fintype.ofFinite G
  let ρ := signedBasisRepresentation b
  let : ρ.IsIrreducible := signedBasisRepresentation_irreducible b
  let U (g : G) : Operator J := g.val.toLinearIsometry.toContinuousLinearMap
  have hU (g : G) : ‖U g‖ ≤ 1 := LinearIsometry.norm_toContinuousLinearMap_le _
  by_contra! hnot
  have hbad (g : G) : ∃ B c : Operator X, ‖B‖ ≤ 1 ∧ B * Φ 1 = 0 ∧
      (∀ x y, (x, y) ∉ E → matrixEntry c x y = 0) ∧ ‖Φ (U g) + B - c‖ < 1 / 2 := by
    obtain ⟨B, hB, hBp, c, hc, herr⟩ := hnot (U g) (hU g)
    exact ⟨B, c, hB, hBp, hc, herr⟩
  choose B c hB hBp hc herr using hbad
  have hcnorm (g : G) : ‖c g‖ ≤ 3 := by
    have hpnorm : ‖Φ (U g)‖ ≤ 1 := by
      rw [NonUnitalStarAlgHom.norm_map Φ hΦ]
      exact hU g
    have ht := norm_add_le (c g - (Φ (U g) + B g)) (Φ (U g) + B g)
    rw [sub_add_cancel, norm_sub_rev] at ht
    have ht' := norm_add_le (Φ (U g)) (B g)
    linarith [hB g, herr g]
  let S := (Fintype.card G : ℂ)⁻¹ •
    ∑ g : G, TensorProduct.mapL (Φ (U g) + B g) (U g)
  let T := (Fintype.card G : ℂ)⁻¹ • ∑ g : G, TensorProduct.mapL (c g) (U g)
  have hS : 1 ≤ ‖S‖ := matrix_embedding_amplification_norm_lower_bound b Φ hΦ B hBp
  have hST : ‖S - T‖ ≤ (1 / 2 : ℝ) :=
    tensor_average_sub_norm_le (fun g => Φ (U g) + B g) c U (by norm_num)
      (fun g => (herr g).le) hU
  have hTlower : (1 / 2 : ℝ) ≤ ‖T‖ := by
    have ht := norm_add_le (S - T) T
    rw [sub_add_cancel] at ht
    linarith
  let Te := operatorConjugationIsometry (coordinateTensorEquiv (X := X) (J := J))
  have hentries (x y : X) (j k : J) : matrixEntry (Te T) (x, j) (y, k) =
      matrixEntry ((Fintype.card G : ℂ)⁻¹ •
        (∑ g : G, matrixEntry (c g) x y • (ρ g).toContinuousLinearMap)) j k := by
    change matrixEntry (Te ((Fintype.card G : ℂ)⁻¹ •
      ∑ g : G, TensorProduct.mapL (c g) (U g))) (x, j) (y, k) = _
    simp only [← matrixEntryCLM_apply, map_smul, map_sum, smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro g _
    change matrixEntry (operatorConjugationIsometry coordinateTensorEquiv
      (TensorProduct.mapL (c g) (U g))) (x, j) (y, k) = _
    rw [coordinateTensor_matrixEntry]
    rfl
  have hTupper := hN ρ (signedBasisRepresentation_norm b) c 3 (by norm_num) hcnorm hc
    (Te T) hentries
  rw [Te.norm_map] at hTupper
  have hsqrt : 0 < Real.sqrt (Fintype.card J : ℝ) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast Fintype.card_pos
  have hsmall : (N : ℝ) ^ 2 * 3 / Real.sqrt (Fintype.card J) < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ hsqrt).mpr
    linarith
  exact (not_lt_of_ge hTlower) (hTupper.trans_lt hsmall)

end DynamicalCStarAlgebras
