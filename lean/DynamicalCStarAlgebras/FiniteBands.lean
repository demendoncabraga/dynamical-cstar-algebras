import DynamicalCStarAlgebras.CoordinatePartitions

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

theorem matrixEntry_compression {X : Type*} (A B : Set X) (a : Operator X) (x y : X) :
    matrixEntry (coordinateProjection A * a * coordinateProjection B) x y =
      if x ∈ A ∧ y ∈ B then matrixEntry a x y else 0 := by
  change coordinateProjection A (a (coordinateProjection B (delta y))) x = _
  by_cases hy : y ∈ B
  · simp only [coordinateProjection_delta_of_mem hy, coordinateProjection_apply_ite,
      hy, and_true, matrixEntry]
  · simp only [coordinateProjection_delta_of_not_mem hy, map_zero, lp.coeFn_zero,
      Pi.zero_apply, hy, and_false, if_false]

/-- One diagonal band of the finite block matrix associated to an integer-valued partition. -/
def integerBand {X : Type*} (φ : X → ℤ) (s : Finset ℤ) (a : Operator X) (k : ℤ) : Operator X :=
  ∑ j ∈ s, coordinateProjection {x | φ x = j + k} * a * coordinateProjection {x | φ x = j}

/-- Every block in a fixed band has disjoint input and output supports. -/
theorem norm_integerBand_le {X : Type*} (φ : X → ℤ) (s : Finset ℤ) (a : Operator X)
    (k : ℤ) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ j ∈ s, ‖coordinateProjection {x | φ x = j + k} * a *
      coordinateProjection {x | φ x = j}‖ ≤ C) : ‖integerBand φ s a k‖ ≤ C := by
  refine norm_sum_disjoint_compressions_le s _ _ (fun _ => a) ?_ ?_ hC ha
  · exact fun i _ j _ hij => Set.disjoint_left.mpr fun x hxi hxj =>
      hij (add_right_cancel (hxi.symm.trans hxj))
  · exact fun i _ j _ hij => Set.disjoint_left.mpr fun x hxi hxj => hij (hxi.symm.trans hxj)

theorem matrixEntry_integerBand {X : Type*} (φ : X → ℤ) (s : Finset ℤ)
    (a : Operator X) (k : ℤ) (x y : X) (hy : φ y ∈ s) :
    matrixEntry (integerBand φ s a k) x y =
      if φ x - φ y = k then matrixEntry a x y else 0 := by
  change (matrixEntryCLM x y) (∑ j ∈ s, _) = _
  simp only [map_sum, matrixEntryCLM_apply, matrixEntry_compression, Set.mem_ofPred_eq,
    and_comm, ite_and, Finset.sum_ite_eq, hy, if_true, sub_eq_iff_eq_add, add_comm]

/-- The commutator of a finite-valued real diagonal is the weighted sum of its bands. -/
theorem diagonalCommutator_eq_sum_integerBand {X : Type*} (f : BoundedDiagonal X)
    (φ : X → ℤ) (s t : Finset ℤ) (a : Operator X) (δ : ℝ)
    (hf : ∀ x, f x = (δ : ℂ) * (φ x : ℂ)) (hs : ∀ x, φ x ∈ s)
    (ht : ∀ x y, φ x - φ y ∈ t) :
    diagonalCommutator f a = ∑ k ∈ t, ((δ : ℂ) * (k : ℂ)) • integerBand φ s a k := by
  refine operator_ext fun x y => ?_
  change _ = (matrixEntryCLM x y) (∑ k ∈ t, _)
  simp only [map_sum, map_smul, matrixEntryCLM_apply, matrixEntry_integerBand φ s a _ _ _ (hs y),
    smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, ht x y, if_true,
    matrixEntry_diagonalCommutator, hf, Int.cast_sub, mul_sub]

end DynamicalCStarAlgebras
