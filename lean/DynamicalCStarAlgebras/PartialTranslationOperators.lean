import DynamicalCStarAlgebras.PartialTranslationPartition
import DynamicalCStarAlgebras.OzawaMatching

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- The partial translation operator of a partial-bijection relation. -/
def partialTranslationOperator {X : Type*} (E : Set (X × X)) (hE : IsPartialBijection E) :
    Operator X :=
  (coordinateEmbedding (fun p : E => p.val.1) hE.1).toContinuousLinearMap.comp
    (coordinateEmbedding (fun p : E => p.val.2) hE.2).toContinuousLinearMap.adjoint

lemma partialTranslationOperator_norm_le {X : Type*} (E : Set (X × X))
    (hE : IsPartialBijection E) : ‖partialTranslationOperator E hE‖ ≤ 1 := by
  unfold partialTranslationOperator
  grw [ContinuousLinearMap.opNorm_comp_le, LinearIsometryEquiv.norm_map,
    LinearIsometry.norm_toContinuousLinearMap_le, LinearIsometry.norm_toContinuousLinearMap_le]
  norm_num

/-- The matrix of a partial translation is the characteristic function of its graph. -/
lemma matrixEntry_partialTranslationOperator {X : Type*} (E : Set (X × X))
    (hE : IsPartialBijection E) (x y : X) :
    matrixEntry (partialTranslationOperator E hE) x y = if (x, y) ∈ E then 1 else 0 := by
  by_cases hy : y ∈ Set.range (fun p : E => p.val.2)
  · obtain ⟨p, rfl⟩ := hy
    have hh : (coordinateEmbedding (fun p : E => p.val.2) hE.2).toContinuousLinearMap.adjoint
        (delta p.val.2) = delta p := by
      rw [← coordinateEmbedding_delta (fun p : E => p.val.2) hE.2 p]
      exact coordinateEmbedding_adjoint_apply _ _ _
    simp only [matrixEntry, partialTranslationOperator, ContinuousLinearMap.comp_apply, hh,
      LinearIsometry.coe_toContinuousLinearMap, coordinateEmbedding_delta]
    by_cases hx : x = p.val.1
    · subst x
      rw [if_pos p.property]
      exact lp.single_apply_self (E := fun _ : X => ℂ) 2 p.val.1 (1 : ℂ)
    · have hp : (x, p.val.2) ∉ E := by
        intro hm
        exact hx (congrArg (fun q : E => q.val.1) (hE.2 (show (⟨(x, p.val.2), hm⟩ : E).val.2 = p.val.2 from rfl)))
      rw [if_neg hp]
      exact lp.single_apply_ne (E := fun _ : X => ℂ) 2 p.val.1 1 hx
  · have hp : (x, y) ∉ E := fun hm => hy ⟨⟨(x, y), hm⟩, rfl⟩
    simp only [matrixEntry, partialTranslationOperator, ContinuousLinearMap.comp_apply,
      coordinateEmbedding_adjoint_delta_outside _ _ hy, map_zero, if_neg hp]
    rfl

/-- The initial projection is the coordinate projection onto the source, so
this operator is a partial isometry. -/
lemma partialTranslationOperator_star_mul {X : Type*} (E : Set (X × X))
    (hE : IsPartialBijection E) :
    star (partialTranslationOperator E hE) * partialTranslationOperator E hE =
      coordinateProjection (Set.range (fun p : E => p.val.2)) := by
  have hs : star (partialTranslationOperator E hE) =
      (coordinateEmbedding (fun p : E => p.val.2) hE.2).toContinuousLinearMap.comp
        (coordinateEmbedding (fun p : E => p.val.1) hE.1).toContinuousLinearMap.adjoint := by
    change (partialTranslationOperator E hE).adjoint = _
    simp only [partialTranslationOperator, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  rw [hs]
  apply ContinuousLinearMap.ext
  intro v
  change (coordinateEmbedding (fun p : E => p.val.2) hE.2)
    ((coordinateEmbedding (fun p : E => p.val.1) hE.1).toContinuousLinearMap.adjoint
      ((coordinateEmbedding (fun p : E => p.val.1) hE.1)
        ((coordinateEmbedding (fun p : E => p.val.2) hE.2).toContinuousLinearMap.adjoint v))) = _
  rw [coordinateEmbedding_adjoint_apply]
  exact congrArg (fun T : Operator X => T v)
    (coordinateEmbedding_mul_adjoint (fun p : E => p.val.2) hE.2)

lemma partialTranslationOperator_hasControlledPropagation {X : Type*}
    (C : CoarseStructure X) (E : Set (X × X)) (hE : IsPartialBijection E)
    (hc : E ∈ C.controlled) : HasControlledPropagation C (partialTranslationOperator E hE) := by
  apply C.subset _ hc
  intro p hp
  by_contra hn
  exact hp (by rw [matrixEntry_partialTranslationOperator, if_neg hn])

/-- Any matrix restricted to a partial translation is a bounded diagonal
multiplier times the translation operator. -/
theorem exists_partial_translation_coefficient {X : Type*} (E : Set (X × X))
    (hE : IsPartialBijection E) (a : Operator X) :
    ∃ f : BoundedDiagonal X, ‖f‖ ≤ ‖a‖ ∧
      ∀ x y, matrixEntry (diagonalMultiplier f * partialTranslationOperator E hE) x y =
        if (x, y) ∈ E then matrixEntry a x y else 0 := by
  let g (x : X) : ℂ := if h : ∃ y, (x, y) ∈ E then matrixEntry a x h.choose else 0
  have hg (x : X) : ‖g x‖ ≤ ‖a‖ := by
    dsimp [g]
    split_ifs
    · exact norm_matrixEntry_le _ _ _
    · exact (norm_zero : ‖(0 : ℂ)‖ = 0).trans_le (norm_nonneg a)
  let f : BoundedDiagonal X := ⟨g, memℓp_infty ⟨‖a‖, by rintro _ ⟨x, rfl⟩; exact hg x⟩⟩
  refine ⟨f, lp.norm_le_of_forall_le (norm_nonneg a) hg, ?_⟩
  intro x y
  change g x * matrixEntry (partialTranslationOperator E hE) x y = _
  rw [matrixEntry_partialTranslationOperator]
  by_cases hp : (x, y) ∈ E
  · rw [if_pos hp, mul_one]
    have hx : ∃ y, (x, y) ∈ E := ⟨y, hp⟩
    have he : hx.choose = y := congrArg (fun p : E => p.val.2)
      (hE.1 (show (⟨(x, hx.choose), hx.choose_spec⟩ : E).val.1 =
        (⟨(x, y), hp⟩ : E).val.1 from rfl))
    simp only [g, dif_pos hx, he, if_pos hp]
  · simp only [if_neg hp, mul_zero]

/-- The finite partial-translation decomposition used in the source remark.
It holds for every uniformly locally finite coarse structure. -/
theorem controlled_operator_partial_translation_decomposition {X : Type*}
    (C : CoarseStructure X) (hC : C.UniformlyLocallyFinite) (a : Operator X)
    (ha : HasControlledPropagation C a) :
    ∃ (N : ℕ) (E : Fin N × Fin N → Set (X × X)) (hE : ∀ i, IsPartialBijection (E i))
      (f : Fin N × Fin N → BoundedDiagonal X),
      (∀ i, E i ∈ C.controlled) ∧
      (∀ i, IsStarProjection (star (partialTranslationOperator (E i) (hE i)) *
        partialTranslationOperator (E i) (hE i))) ∧ (∀ i, ‖f i‖ ≤ ‖a‖) ∧
      (∀ i, ‖diagonalMultiplier (f i) * partialTranslationOperator (E i) (hE i)‖ ≤ ‖a‖) ∧
      (∀ i, HasControlledPropagation C (partialTranslationOperator (E i) (hE i))) ∧
      (∀ i, ∀ h : X → ℝ, IsCoarseReal C h →
        IsEntireExponentialType h (diagonalMultiplier (f i) * partialTranslationOperator (E i) (hE i))) ∧
      a = ∑ i, diagonalMultiplier (f i) * partialTranslationOperator (E i) (hE i) := by
  obtain ⟨N, E, hcover, hdis, hE⟩ := controlled_relation_partial_bijection_partition
    C hC (operatorSupport a) ha
  choose f hf hcoeff using fun i => exists_partial_translation_coefficient (E i) (hE i).1 a
  refine ⟨N, E, fun i => (hE i).1, f, fun i => (hE i).2, ?_, hf, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [partialTranslationOperator_star_mul]
    exact ⟨(coordinateSubspace _).toSubmodule.isIdempotentElem_starProjection,
      isSelfAdjoint_starProjection _⟩
  · intro i
    exact (norm_mul_le _ _).trans ((mul_le_mul (diagonalMultiplier_norm_le (f i))
      (partialTranslationOperator_norm_le _ _) (norm_nonneg _) (norm_nonneg _)).trans
        (by simpa only [mul_one] using hf i))
  · intro i
    exact partialTranslationOperator_hasControlledPropagation C (E i) (hE i).1 (hE i).2
  · intro i h hh
    exact ((diagonalMultiplier_hasControlledPropagation C (f i)).mul
      (partialTranslationOperator_hasControlledPropagation C (E i) (hE i).1 (hE i).2)).isEntireExponentialType hh
  · apply operator_ext
    intro x y
    change matrixEntry a x y = (matrixEntryCLM x y) (∑ i, _)
    simp only [map_sum, matrixEntryCLM_apply, hcoeff]
    by_cases hp : (x, y) ∈ operatorSupport a
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover.symm ▸ hp)
      rw [Finset.sum_eq_single i]
      · rw [if_pos hi]
      · intro j _ hji
        rw [if_neg (fun hj => (Set.disjoint_left.mp (hdis hji) hj hi))]
      · intro hn
        exact (hn (Finset.mem_univ i)).elim
    · have hz : matrixEntry a x y = 0 := by simpa only [operatorSupport, Set.mem_ofPred_eq, not_not] using hp
      simp only [hz, ite_self, Finset.sum_const_zero]

end DynamicalCStarAlgebras
