import DynamicalCStarAlgebras.PartialTranslationOperators
import DynamicalCStarAlgebras.RoeContinuity

noncomputable section
open Classical Filter
namespace DynamicalCStarAlgebras

/-- A continuous partial-translation orbit forces a uniform height bound on its graph. -/
lemma boundedVariation_of_partialTranslation_continuous {X : Type*}
    (h : X → ℝ) (E : Set (X × X)) (hE : IsPartialBijection E)
    (ha : partialTranslationOperator E hE ∈ continuityPoints h) : BoundedVariation h E := by
  let a := partialTranslationOperator E hE
  have ht := (tendsto_fejerAverage h a ha).eventually (Metric.ball_mem_nhds a zero_lt_one)
  obtain ⟨s, hs, hb⟩ := ((eventually_gt_atTop (0 : ℝ)).and ht).exists
  refine ⟨s, ?_⟩
  intro p hp
  by_contra! hgap
  have hz := matrixEntry_fejerAverage_eq_zero h hs a p.1 p.2 (by
    simpa only [Real.dist_eq] using hgap)
  have he : matrixEntry a p.1 p.2 = 1 := by
    simp [a, matrixEntry_partialTranslationOperator, hp]
  have hn := norm_matrixEntry_le (fejerAverage h s a - a) p.1 p.2
  change ‖matrixEntry (fejerAverage h s a) p.1 p.2 - matrixEntry a p.1 p.2‖ ≤ _ at hn
  have hh : (1 : ℝ) ≤ ‖fejerAverage h s a - a‖ := by
    simpa only [hz, he, zero_sub, norm_neg, norm_one] using hn
  exact (not_le_of_gt (show ‖fejerAverage h s a - a‖ < 1 by
    simpa only [Metric.mem_ball, dist_eq_norm] using hb)) hh

/-- The finite partial-translation partition detects whether a height is coarse. -/
theorem isCoarseReal_iff_partialTranslations_continuous {X : Type*}
    (C : CoarseStructure X) (hC : C.UniformlyLocallyFinite) (h : X → ℝ) :
    IsCoarseReal C h ↔ ∀ (E : Set (X × X)) (hE : IsPartialBijection E),
      E ∈ C.controlled → partialTranslationOperator E hE ∈ continuityPoints h := by
  constructor
  · intro hh E hE hc
    apply finitePropagation_mem_continuityPoints h
    exact ((partialTranslationOperator_hasControlledPropagation C E hE hc).isEntireExponentialType
      hh).hasFinitePropagation
  · intro hh E hc
    obtain ⟨N, F, hFE, _, hF⟩ := controlled_relation_partial_bijection_partition C hC E hc
    have hB (i : Fin N × Fin N) : BoundedVariation h (F i) :=
      boundedVariation_of_partialTranslation_continuous h (F i) (hF i).1
        (hh (F i) (hF i).1 (hF i).2)
    choose R hR using hB
    refine ⟨∑ i, max (R i) 0, ?_⟩
    intro p hp
    rw [← hFE] at hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    exact (hR i p hi).trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun j _ => le_max_right (R j) 0) (Finset.mem_univ i)))

/-- The diagonal action restricts to a norm-continuous action on the uniform Roe
algebra exactly for coarse heights, on any uniformly locally finite coarse space. -/
theorem isCoarseReal_iff_uniformRoe_continuous {X : Type*}
    (C : CoarseStructure X) (hC : C.UniformlyLocallyFinite) (h : X → ℝ) :
    IsCoarseReal C h ↔ uniformRoe C ⊆ continuityPoints h := by
  constructor
  · intro hh a ha
    apply uniformRoe_restrictReal_subset_continuityPoints C h
    exact uniformRoe_mono (C := C) (D := C.restrictReal h) (fun E hE => ⟨hE, hh E hE⟩) ha
  · intro hh
    apply (isCoarseReal_iff_partialTranslations_continuous C hC h).mpr
    intro E hE hc
    exact hh (subset_closure (partialTranslationOperator_hasControlledPropagation C E hE hc))

end DynamicalCStarAlgebras
