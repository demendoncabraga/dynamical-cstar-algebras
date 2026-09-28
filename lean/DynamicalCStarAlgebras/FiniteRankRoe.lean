import DynamicalCStarAlgebras.FiniteCompressions

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

theorem matrixEntry_rankOne {X : Type*} (v w : HilbertSpace X) (x y : X) :
    matrixEntry (InnerProductSpace.rankOne ℂ v w) x y = v x * star (w y) := by
  simp [matrixEntry, InnerProductSpace.rankOne_apply, delta, lp.inner_single_right,
    lp.coeFn_smul, mul_comm]

/-- Rank-one operators made from finite vectors have finite propagation. -/
theorem finitePropagation_rankOne_finiteVector {X : Type*} [PseudoMetricSpace X]
    (v w : X →₀ ℂ) : HasFinitePropagation
      (InnerProductSpace.rankOne ℂ (finiteVector v) (finiteVector w)) := by
  obtain ⟨R, hR⟩ := ((v.support.product w.support).finite_toSet.image
    (fun p : X × X => dist p.1 p.2)).bddAbove
  refine ⟨max R 0 + 1, by positivity, fun x y hxy => ?_⟩
  rw [matrixEntry_rankOne, finiteVector_apply, finiteVector_apply]
  by_cases hx : x ∈ v.support
  · by_cases hy : y ∈ w.support
    · have hb := hR (Set.mem_image_of_mem _ (show (x, y) ∈ (v.support.product w.support : Set (X × X)) from Finset.mem_product.mpr ⟨hx, hy⟩))
      exact False.elim ((not_le_of_gt hxy) (hb.trans (by linarith [le_max_left R 0])))
    · simp only [Finsupp.notMem_support_iff.mp hy, star_zero, mul_zero]
  · simp only [Finsupp.notMem_support_iff.mp hx, zero_mul]

/-- Every rank-one operator belongs to the uniform Roe algebra of a metric space. -/
theorem rankOne_mem_uniformRoe {X : Type*} [PseudoMetricSpace X] (v w : HilbertSpace X) :
    InnerProductSpace.rankOne ℂ v w ∈ uniformRoe (CoarseStructure.ofPseudoMetric X) := by
  refine denseRange_finiteVector.induction_on w
    (isClosed_closure.preimage (InnerProductSpace.rankOne ℂ v).continuous) fun w => ?_
  refine denseRange_finiteVector.induction_on v ?_ fun v => ?_
  · simpa only [ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne] using!
      (show IsClosed (uniformRoe (CoarseStructure.ofPseudoMetric X)) from isClosed_closure).preimage
        (InnerProductSpace.rankOne ℂ (finiteVector w) : HilbertSpace X →L⋆[ℂ] Operator X).continuous.star
  · rw [uniformRoe_metric_eq]
    exact subset_closure (finitePropagation_rankOne_finiteVector v w)

/-- A finite collection of columns is a sum of rank-one operators. -/
theorem mul_coordinateProjection_finset {X : Type*} (a : Operator X) (F : Finset X) :
    a * coordinateProjection (F : Set X) =
      ∑ x ∈ F, InnerProductSpace.rankOne ℂ (a (delta x)) (delta x) := by
  refine operator_ext fun x y => ?_
  change _ = (matrixEntryCLM x y) (∑ z ∈ F, _)
  simp only [map_sum, matrixEntryCLM_apply, matrixEntry_rankOne]
  by_cases hy : y ∈ F
  · change a (coordinateProjection (F : Set X) (delta y)) x = _
    rw [coordinateProjection_delta_of_mem hy]
    simp [delta, lp.single_apply, Pi.single_apply, hy]
  · change a (coordinateProjection (F : Set X) (delta y)) x = _
    rw [coordinateProjection_delta_of_not_mem hy]
    simp [delta, lp.single_apply, Pi.single_apply, hy]

theorem mul_finite_coordinateProjection_mem_uniformRoe {X : Type*} [PseudoMetricSpace X]
    (a : Operator X) {F : Set X} (hF : F.Finite) :
    a * coordinateProjection F ∈ uniformRoe (CoarseStructure.ofPseudoMetric X) := by
  rw [← hF.coe_toFinset, mul_coordinateProjection_finset]
  exact (uniformRoeStarSubalgebra (CoarseStructure.ofPseudoMetric X)).sum_mem
    (fun x _ => rankOne_mem_uniformRoe _ _)

theorem finite_coordinateProjection_mul_mem_uniformRoe {X : Type*} [PseudoMetricSpace X]
    (a : Operator X) {F : Set X} (hF : F.Finite) :
    coordinateProjection F * a ∈ uniformRoe (CoarseStructure.ofPseudoMetric X) := by
  simpa only [star_mul, star_star, coordinateProjection_star] using!
    (uniformRoeStarSubalgebra (CoarseStructure.ofPseudoMetric X)).star_mem'
      (mul_finite_coordinateProjection_mem_uniformRoe (star a) hF)

/-- Deleting a finite set of rows and columns changes an operator by a Roe operator. -/
theorem remove_finite_buffer_error_mem_uniformRoe {X : Type*} [PseudoMetricSpace X]
    (a : Operator X) {F : Set X} (hF : F.Finite) :
    a - coordinateProjection Fᶜ * a * coordinateProjection Fᶜ ∈
      uniformRoe (CoarseStructure.ofPseudoMetric X) := by
  have hcomp : coordinateProjection Fᶜ = 1 - coordinateProjection F := by
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm, coordinateProjection_add_compl]
  have he : a - coordinateProjection Fᶜ * a * coordinateProjection Fᶜ =
      coordinateProjection F * a + (coordinateProjection Fᶜ * a) * coordinateProjection F := by
    rw [hcomp]
    noncomm_ring
  rw [he]
  exact (uniformRoeStarSubalgebra (CoarseStructure.ofPseudoMetric X)).add_mem
    (finite_coordinateProjection_mul_mem_uniformRoe a hF)
    (mul_finite_coordinateProjection_mem_uniformRoe _ hF)

end DynamicalCStarAlgebras
