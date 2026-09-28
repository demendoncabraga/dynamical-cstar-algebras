import DynamicalCStarAlgebras.OzawaMatching
import DynamicalCStarAlgebras.PartialTranslationPartition

noncomputable section
open Classical

namespace DynamicalCStarAlgebras

lemma exists_partial_bijection_block_operator {X J : Type*} (E : Set (X × X))
    (hE : IsPartialBijection E) (a : E → Operator J) {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ p, ‖a p‖ ≤ M) :
    ∃ T : Operator (X × J), ‖T‖ ≤ M ∧ ∀ x y j k,
      matrixEntry T (x, j) (y, k) =
        if h : (x, y) ∈ E then matrixEntry (a ⟨(x, y), h⟩) j k else 0 := by
  obtain ⟨T, hT, he, ho⟩ := exists_matching_block_operator
    (fun p : E => p.val.1) (fun p : E => p.val.2) hE.1 hE.2 a hM ha
  refine ⟨T, hT, fun x y j k => ?_⟩
  by_cases hxy : (x, y) ∈ E
  · rw [dif_pos hxy]
    simpa only [ite_true] using he ⟨(x, y), hxy⟩ ⟨(x, y), hxy⟩ j k
  · rw [dif_neg hxy]
    by_cases hx : x ∈ Set.range (fun p : E => p.val.1)
    · obtain ⟨s, rfl⟩ := hx
      by_cases hy : y ∈ Set.range (fun p : E => p.val.2)
      · obtain ⟨t, rfl⟩ := hy
        have hst : s ≠ t := by
          intro h
          subst t
          exact hxy s.property
        simpa only [if_neg hst] using he s t j k
      · exact ho _ _ _ _ (Or.inr hy)
    · exact ho _ _ _ _ (Or.inl hx)

/-- A controlled relation has a dimension-independent bound for matrices of
operator blocks. The proof uses N^2 partial matchings, without an optimal
edge-coloring bound. -/
theorem controlled_block_matrix_norm_bound {X : Type*} (C : CoarseStructure X)
    (hC : C.UniformlyLocallyFinite) (E : Set (X × X)) (hE : E ∈ C.controlled) :
    ∃ N : ℕ, ∀ {J : Type*} (q : X → X → Operator J) (M : ℝ), 0 ≤ M →
      (∀ x y, ‖q x y‖ ≤ M) → (∀ x y, (x, y) ∉ E → q x y = 0) →
      ∀ T : Operator (X × J),
        (∀ x y j k, matrixEntry T (x, j) (y, k) = matrixEntry (q x y) j k) →
        ‖T‖ ≤ (N : ℝ) ^ 2 * M := by
  obtain ⟨N, F, hcover, hdis, hF⟩ := controlled_relation_partial_bijection_partition C hC E hE
  refine ⟨N, fun {J} q M hM hq hzero T hT => ?_⟩
  have hex (i : Fin N × Fin N) := exists_partial_bijection_block_operator (F i) (hF i).1
    (fun p => q p.val.1 p.val.2) hM (fun p => hq p.val.1 p.val.2)
  choose B hB hBe using hex
  have hsum : T = ∑ i, B i := by
    apply operator_ext
    rintro ⟨x, j⟩ ⟨y, k⟩
    rw [hT]
    simp only [← matrixEntryCLM_apply, map_sum]
    simp only [matrixEntryCLM_apply, hBe]
    by_cases hxy : (x, y) ∈ E
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover ▸ hxy)
      rw [Finset.sum_eq_single i]
      · rw [dif_pos hi]
      · intro l _ hli
        have hn : (x, y) ∉ F l := fun hl => Set.disjoint_left.mp (hdis hli) hl hi
        rw [dif_neg hn]
      · intro hn
        exact (hn (Finset.mem_univ i)).elim
    · have hn (i : Fin N × Fin N) : (x, y) ∉ F i := by
        intro hi
        apply hxy
        rw [← hcover]
        exact Set.mem_iUnion.mpr ⟨i, hi⟩
      simp only [dif_neg (hn _), hzero x y hxy, Finset.sum_const_zero]
      rfl
  rw [hsum]
  apply (norm_sum_le _ _).trans
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hB i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_mul, pow_two] using h

/-- The full finite-propagation amplification upper bound used in Ozawa's
nonembedding argument. The number N depends only on the controlled relation;
the bound tends to zero with the matrix size. Our N^2 partition bound replaces
the sharper 2 N_X(R) appearing in the published proof. -/
theorem controlled_unitary_amplification_norm_bound {X : Type*} (C : CoarseStructure X)
    (hC : C.UniformlyLocallyFinite) (E : Set (X × X)) (hE : E ∈ C.controlled) :
    ∃ N : ℕ, ∀ {J : Type*} [Fintype J] {G : Type*} [Group G] [Fintype G]
      (ρ : Representation ℂ G (HilbertSpace J)) [ρ.IsIrreducible],
      (∀ g x, ‖ρ g x‖ = ‖x‖) → ∀ (c : G → Operator X) (M : ℝ), 0 ≤ M →
      (∀ g, ‖c g‖ ≤ M) →
      (∀ g x y, (x, y) ∉ E → matrixEntry (c g) x y = 0) →
      ∀ T : Operator (X × J),
        (∀ x y j k, matrixEntry T (x, j) (y, k) = matrixEntry
          ((Fintype.card G : ℂ)⁻¹ •
            (∑ g : G, matrixEntry (c g) x y • (ρ g).toContinuousLinearMap)) j k) →
        ‖T‖ ≤ (N : ℝ) ^ 2 * M / Real.sqrt (Fintype.card J) := by
  obtain ⟨N, hN⟩ := controlled_block_matrix_norm_bound C hC E hE
  refine ⟨N, ?_⟩
  intro J _ G _ _ ρ _ hu c M hM hc hsupp T hT
  let q (x y : X) : Operator J := (Fintype.card G : ℂ)⁻¹ •
    (∑ g : G, matrixEntry (c g) x y • (ρ g).toContinuousLinearMap)
  have hq (x y : X) : ‖q x y‖ ≤ M / Real.sqrt (Fintype.card J) := by
    simpa only [finrank_hilbertSpace] using
      irreducible_unitary_average_norm_le_bound ρ hu (fun g => matrixEntry (c g) x y) hM
        (fun g => (norm_matrixEntry_le (c g) x y).trans (hc g))
  have hzero (x y : X) (hxy : (x, y) ∉ E) : q x y = 0 := by
    simp only [q, hsupp _ x y hxy, zero_smul, Finset.sum_const_zero, smul_zero]
  have hh := hN q (M / Real.sqrt (Fintype.card J)) (div_nonneg hM (Real.sqrt_nonneg _))
    hq hzero T hT
  simpa only [mul_div_assoc] using hh

end DynamicalCStarAlgebras
