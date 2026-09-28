import DynamicalCStarAlgebras.TheoremA

namespace DynamicalCStarAlgebras

open MeasureTheory Filter

universe u

theorem averagingOperator_sub_operator {X : Type u} (h : X → ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) (a b : Operator X) :
    averagingOperator h hf (a - b) = averagingOperator h hf a - averagingOperator h hf b := by
  apply ContinuousLinearMap.ext
  exact fun v => by
    simpa only [averagingOperator_apply, diagonalFlow_sub, sub_apply, smul_sub] using
      integral_sub (integrable_diagonalFlow_smul h hf a v) (integrable_diagonalFlow_smul h hf b v)

theorem continuous_averagingOperator {X : Type u} (h : X → ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) : Continuous (fun a : Operator X => averagingOperator h hf a) := by
  apply LipschitzWith.continuous (K := ⟨∫ t, ‖f t‖, integral_nonneg fun _ => norm_nonneg _⟩)
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  simpa only [dist_eq_norm, ← averagingOperator_sub_operator] using!
    averagingOperator_norm_le h hf (a - b)

theorem operatorSupport_averagingOperator_subset {X : Type u} (h : X → ℝ)
    {f : ℝ → ℂ} (hf : Integrable f) (a : Operator X) :
    operatorSupport (averagingOperator h hf a) ⊆ operatorSupport a := by
  intro p hp
  exact fun he => hp (by rw [matrixEntry_averagingOperator, he, mul_zero])

theorem fejerAverage_hasControlledPropagation_restrictReal {X : Type u}
    (C : CoarseStructure X) (h : X → ℝ) {s : ℝ} (hs : 0 < s)
    (a : Operator X) (ha : HasControlledPropagation C a) :
    HasControlledPropagation (C.restrictReal h) (fejerAverage h s a) := by
  refine ⟨C.subset (operatorSupport_averagingOperator_subset h _ a) ha, s, ?_⟩
  exact fun p hp => le_of_not_gt fun hgt => hp
    (matrixEntry_fejerAverage_eq_zero h hs a p.1 p.2 ((Real.dist_eq _ _) ▸ hgt))

theorem fejerAverage_mem_uniformRoe_restrictReal {X : Type u} (C : CoarseStructure X)
    (h : X → ℝ) {s : ℝ} (hs : 0 < s) (a : Operator X) (ha : a ∈ uniformRoe C) :
    fejerAverage h s a ∈ uniformRoe (C.restrictReal h) := by
  have hc : IsClosed ((fun b : Operator X => fejerAverage h s b) ⁻¹'
      uniformRoe (C.restrictReal h)) :=
    isClosed_closure.preimage (continuous_averagingOperator h _)
  exact closure_minimal (t := (fun b : Operator X => fejerAverage h s b) ⁻¹'
    uniformRoe (C.restrictReal h)) (fun b hb => subset_closure
    (fejerAverage_hasControlledPropagation_restrictReal C h hs b hb)) hc ha

theorem uniformRoe_restrictReal_subset_continuityPoints {X : Type u}
    (C : CoarseStructure X) (h : X → ℝ) :
    uniformRoe (C.restrictReal h) ⊆ continuityPoints h := by
  rw [continuityPoints_eq_uniformRoe_pullback]
  exact uniformRoe_mono (fun _ hE => hE.2)

/-- Theorem uRa.h.Points.Cont.Substructure, for arbitrary coarse spaces. -/
theorem uniformRoe_inter_continuityPoints {X : Type u} (C : CoarseStructure X) (h : X → ℝ) :
    uniformRoe C ∩ continuityPoints h = uniformRoe (C.restrictReal h) := by
  apply Set.Subset.antisymm
  · exact fun a ha => isClosed_closure.mem_of_tendsto (tendsto_fejerAverage h a ha.2)
      ((eventually_gt_atTop 0).mono fun _s hs => fejerAverage_mem_uniformRoe_restrictReal C h hs a ha.1)
  · exact fun _ ha => ⟨uniformRoe_restrictReal_subset C h ha,
      uniformRoe_restrictReal_subset_continuityPoints C h ha⟩

end DynamicalCStarAlgebras
