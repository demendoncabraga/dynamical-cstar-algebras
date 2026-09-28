import DynamicalCStarAlgebras.CoarseContinuity

namespace DynamicalCStarAlgebras

universe u

theorem coordinateProjection_comm_diagonalUnitary {X : Type u} (h : X → ℝ)
    (t : ℝ) (A : Set X) :
    coordinateProjection A * diagonalUnitary h t =
      diagonalUnitary h t * coordinateProjection A := by
  refine operator_ext fun x y => ?_
  change coordinateProjection A (diagonalUnitary h t (delta y)) x =
    diagonalUnitary h t (coordinateProjection A (delta y)) x
  by_cases hx : x ∈ A
  · simp only [coordinateProjection_apply_of_mem A _ hx, diagonalUnitary_apply]
  · simp only [coordinateProjection_apply_of_not_mem A _ hx, diagonalUnitary_apply, mul_zero]

theorem diagonalFlow_coordinateProjection {X : Type u} (h : X → ℝ) (t : ℝ) (A : Set X) :
    diagonalFlow h t (coordinateProjection A) = coordinateProjection A := by
  rw [diagonalFlow, ← coordinateProjection_comm_diagonalUnitary, mul_assoc,
    ← diagonalUnitary_add, add_neg_cancel, diagonalUnitary_zero, mul_one]

theorem diagonalFlow_compression {X : Type u} (h : X → ℝ) (t : ℝ)
    (a : Operator X) (A B : Set X) :
    diagonalFlow h t (coordinateProjection A * a * coordinateProjection B) =
      coordinateProjection A * diagonalFlow h t a * coordinateProjection B := by
  rw [← diagonalFlowEquiv_apply, map_mul, map_mul]
  simp only [diagonalFlowEquiv_apply, diagonalFlow_coordinateProjection]

theorem compression_diagonalFlow_norm {X : Type u} (h : X → ℝ) (t : ℝ)
    (a : Operator X) (A B : Set X) :
    ‖coordinateProjection A * diagonalFlow h t a * coordinateProjection B‖ =
      ‖coordinateProjection A * a * coordinateProjection B‖ := by
  rw [← diagonalFlow_compression, diagonalFlow_norm]

theorem IsQuasiLocalAt.diagonalFlow {X : Type u} {a : Operator X} {ε : ℝ}
    {E : Set (X × X)} (ha : IsQuasiLocalAt a ε E) (h : X → ℝ) (t : ℝ) :
    IsQuasiLocalAt (diagonalFlow h t a) ε E :=
  fun A B hAB => (compression_diagonalFlow_norm h t a A B).trans_le (ha A B hAB)

theorem diagonalFlow_mem_quasiLocal {X : Type u} (C : CoarseStructure X)
    (h : X → ℝ) (t : ℝ) (a : Operator X) (ha : a ∈ quasiLocal C) :
    diagonalFlow h t a ∈ quasiLocal C :=
  fun ε hε => (ha ε hε).imp fun _E hE => ⟨hE.1, hE.2.diagonalFlow h t⟩

end DynamicalCStarAlgebras
