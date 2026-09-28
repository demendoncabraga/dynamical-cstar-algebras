import DynamicalCStarAlgebras.BlockNorms

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

lemma coordinateEmbedding_adjoint_apply_coord {X Y : Type*} (ι : Y → X)
    (hι : Function.Injective ι) (v : HilbertSpace X) (y : Y) :
    (coordinateEmbedding ι hι).toContinuousLinearMap.adjoint v y = v (ι y) := by
  have h := ContinuousLinearMap.adjoint_inner_right
    (coordinateEmbedding ι hι).toContinuousLinearMap (delta y) v
  rw [show (coordinateEmbedding ι hι).toContinuousLinearMap (delta y) = delta (ι y)
    from coordinateEmbedding_delta ι hι y] at h
  simpa [delta, lp.inner_single_left] using h


lemma coordinateEmbedding_mul_adjoint {X Y : Type*} (ι : Y → X)
    (hι : Function.Injective ι) :
    (coordinateEmbedding ι hι).toContinuousLinearMap.comp
      (coordinateEmbedding ι hι).toContinuousLinearMap.adjoint =
        coordinateProjection (Set.range ι) := by
  apply operator_ext
  intro x y
  by_cases hy : y ∈ Set.range ι
  · obtain ⟨z, rfl⟩ := hy
    have hz : (coordinateEmbedding ι hι).toContinuousLinearMap.adjoint (delta (ι z)) = delta z := by
      rw [← coordinateEmbedding_delta ι hι z]
      exact coordinateEmbedding_adjoint_apply ι hι _
    simp only [matrixEntry, ContinuousLinearMap.comp_apply, hz,
      LinearIsometry.coe_toContinuousLinearMap, coordinateEmbedding_delta,
      coordinateProjection_delta_of_mem (Set.mem_range_self z)]
  · have hz : (coordinateEmbedding ι hι).toContinuousLinearMap.adjoint (delta y) = 0 := by
      apply lp.ext
      funext z
      rw [coordinateEmbedding_adjoint_apply_coord]
      exact lp.single_apply_ne (E := fun _ : X => ℂ) 2 y 1
        (fun he => hy ⟨z, he⟩)
    simp only [matrixEntry, ContinuousLinearMap.comp_apply, hz, map_zero,
      coordinateProjection_delta_of_not_mem hy]

lemma lift_componentOperator_eq_compression {X Y : Type*} (ι : Y → X)
    (hι : Function.Injective ι) (a : Operator X) :
    liftComponentOperator ι hι (componentOperator ι hι a) =
      coordinateProjection (Set.range ι) * a * coordinateProjection (Set.range ι) := by
  have h := coordinateEmbedding_mul_adjoint ι hι
  apply ContinuousLinearMap.ext
  intro v
  simp only [liftComponentOperator, componentOperator, ContinuousLinearMap.comp_apply,
    mul_apply_eq_comp]
  have hv (w : HilbertSpace X) := congrArg (fun q : Operator X => q w) h
  exact (hv (a ((coordinateEmbedding ι hι).toContinuousLinearMap
    ((coordinateEmbedding ι hι).toContinuousLinearMap.adjoint v)))).trans
      (congrArg (fun w => coordinateProjection (Set.range ι) (a w)) (hv v))

end DynamicalCStarAlgebras
