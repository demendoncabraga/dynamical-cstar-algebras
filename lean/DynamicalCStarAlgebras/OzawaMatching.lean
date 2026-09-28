import DynamicalCStarAlgebras.IrreducibleAverages

noncomputable section

open Classical

namespace DynamicalCStarAlgebras

lemma irreducible_unitary_average_norm_le_bound {G H : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (ρ : Representation ℂ G H) [ρ.IsIrreducible]
    (hu : ∀ g x, ‖ρ g x‖ = ‖x‖) (α : G → ℂ) {M : ℝ}
    (hM : 0 ≤ M) (hα : ∀ g, ‖α g‖ ≤ M) :
    ‖(Fintype.card G : ℂ)⁻¹ • (∑ g : G, α g • (ρ g).toContinuousLinearMap)‖ ≤
      M / Real.sqrt (Module.finrank ℂ H) := by
  by_cases hM0 : M = 0
  · have hzero (g : G) : α g = 0 := norm_le_zero_iff.mp (hM0 ▸ hα g)
    simp only [hzero, zero_smul, Finset.sum_const_zero, smul_zero, norm_zero, hM0, zero_div, le_refl]
  have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
  let β (g : G) : ℂ := (M : ℂ)⁻¹ * α g
  have hβ (g : G) : ‖β g‖ ≤ 1 := by
    dsimp [β]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM]
    apply (inv_mul_le_iff₀ hMpos).mpr
    simpa only [mul_one] using hα g
  have hb := irreducible_unitary_average_norm_le ρ hu β hβ
  have he : (M : ℂ) • ((Fintype.card G : ℂ)⁻¹ •
      (∑ g : G, β g • (ρ g).toContinuousLinearMap)) =
      (Fintype.card G : ℂ)⁻¹ • (∑ g : G, α g • (ρ g).toContinuousLinearMap) := by
    rw [smul_comm (M : ℂ), Finset.smul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro g _
    rw [smul_smul]
    congr 1
    dsimp [β]
    exact mul_inv_cancel_left₀ (by exact_mod_cast hM0 : (M : ℂ) ≠ 0) _
  rw [← he, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM]
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hb hM

lemma coordinateEmbedding_adjoint_delta_outside {X Y : Type*} (ι : Y → X)
    (hι : Function.Injective ι) {x : X} (hx : x ∉ Set.range ι) :
    (coordinateEmbedding ι hι).toContinuousLinearMap.adjoint (delta x) = 0 := by
  apply lp.ext
  funext y
  have hy : ι y ≠ x := fun h => hx ⟨y, h⟩
  have he := ContinuousLinearMap.adjoint_inner_right
    (coordinateEmbedding ι hι).toContinuousLinearMap (delta y) (delta x)
  simp only [LinearIsometry.coe_toContinuousLinearMap, coordinateEmbedding_delta] at he
  simpa [delta, lp.inner_single_left, lp.single_apply, hy, Ne.symm hy]
    using he

/-- A matrix of operator-valued coefficients supported on a partial matching
has the common norm bound of those coefficients. This is the complete-isometry
step in Ozawa's proof of Lemma 1, Section 2. -/
theorem exists_matching_block_operator {X S J : Type*}
    (row col : S → X) (hrow : Function.Injective row) (hcol : Function.Injective col)
    (a : S → Operator J) {M : ℝ} (hM : 0 ≤ M) (ha : ∀ s, ‖a s‖ ≤ M) :
    ∃ T : Operator (X × J), ‖T‖ ≤ M ∧
      (∀ s t j k, matrixEntry T (row s, j) (col t, k) =
        if s = t then matrixEntry (a s) j k else 0) ∧
      ∀ x y j k, (x ∉ Set.range row ∨ y ∉ Set.range col) → matrixEntry T (x, j) (y, k) = 0 := by
  classical
  let embed (s : S) : J → S × J := fun j => (s, j)
  have hinj (s : S) : Function.Injective (embed s) := fun _ _ h => congrArg Prod.snd h
  let b (s : S) := liftComponentOperator (embed s) (hinj s) (a s)
  obtain ⟨B, hB, hBe⟩ := exists_fiber_operator Prod.fst b hM
    (fun s => (compression_norm_le (b s) _ _).trans
      ((norm_liftComponentOperator_le _ _ _).trans (ha s)))
  have hBentries (s t : S) (j k : J) : matrixEntry B (s, j) (t, k) =
      if s = t then matrixEntry (a s) j k else 0 := by
    rw [hBe]
    change (if s = t then matrixEntry (b s) (s, j) (t, k) else 0) = _
    split_ifs with h
    · subst t
      exact matrixEntry_liftComponentOperator_image (embed s) (hinj s) (a s) j k
    · rfl
  let ir : S × J → X × J := fun v => (row v.1, v.2)
  let ic : S × J → X × J := fun v => (col v.1, v.2)
  have hir : Function.Injective ir := fun _ _ h => Prod.ext (hrow (congrArg Prod.fst h))
    (congrArg (fun v : X × J => v.2) h)
  have hic : Function.Injective ic := fun _ _ h => Prod.ext (hcol (congrArg Prod.fst h))
    (congrArg (fun v : X × J => v.2) h)
  let er := coordinateEmbedding ir hir
  let ec := coordinateEmbedding ic hic
  let T : Operator (X × J) := er.toContinuousLinearMap.comp
    (B.comp ec.toContinuousLinearMap.adjoint)
  refine ⟨T, ?_, ?_, ?_⟩
  · apply le_trans _ hB
    dsimp [T]
    grw [ContinuousLinearMap.opNorm_comp_le, ContinuousLinearMap.opNorm_comp_le,
      LinearIsometryEquiv.norm_map, LinearIsometry.norm_toContinuousLinearMap_le,
      LinearIsometry.norm_toContinuousLinearMap_le]
    simp
  · intro s t j k
    change matrixEntry T (ir (s, j)) (ic (t, k)) = _
    rw [matrixEntry_eq_inner, ← coordinateEmbedding_delta ir hir,
      ← coordinateEmbedding_delta ic hic]
    simp only [T, er, ec, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      coordinateEmbedding_adjoint_apply, LinearIsometry.inner_map_map]
    simpa only [matrixEntry_eq_inner] using hBentries s t j k
  · intro x y j k hxy
    rw [matrixEntry_eq_inner]
    change inner ℂ (delta (x, j)) (er (B (ec.toContinuousLinearMap.adjoint (delta (y, k))))) = 0
    rcases hxy with hx | hy
    · have hx' : (x, j) ∉ Set.range ir := by
        rintro ⟨v, hv⟩
        exact hx ⟨v.1, congrArg Prod.fst hv⟩
      change inner ℂ (delta (x, j))
        (er.toContinuousLinearMap (B (ec.toContinuousLinearMap.adjoint (delta (y, k))))) = 0
      rw [← ContinuousLinearMap.adjoint_inner_left]
      rw [coordinateEmbedding_adjoint_delta_outside ir hir hx', inner_zero_left]
    · have hy' : (y, k) ∉ Set.range ic := by
        rintro ⟨v, hv⟩
        exact hy ⟨v.1, congrArg Prod.fst hv⟩
      rw [coordinateEmbedding_adjoint_delta_outside ic hic hy', map_zero, map_zero, inner_zero_right]


end DynamicalCStarAlgebras
