import DynamicalCStarAlgebras.DiagonalMultipliers
import DynamicalCStarAlgebras.QuasiLocalModulus

noncomputable section

namespace DynamicalCStarAlgebras

universe u

/-- Commutation with a bounded complex diagonal multiplier. -/
def diagonalCommutator {X : Type u} (f : BoundedDiagonal X) (a : Operator X) : Operator X :=
  diagonalMultiplier f * a - a * diagonalMultiplier f

theorem diagonalCommutator_norm_le {X : Type u} (f : BoundedDiagonal X) (a : Operator X) :
    ‖diagonalCommutator f a‖ ≤ (2 * ‖f‖) * ‖a‖ := by
  refine (norm_sub_le _ _).trans ((add_le_add (norm_mul_le _ _) (norm_mul_le _ _)).trans ?_)
  simp only [diagonalMultiplier_norm]
  exact le_of_eq (by ring)

theorem coordinateProjection_comm_diagonalMultiplier {X : Type u}
    (f : BoundedDiagonal X) (A : Set X) :
    coordinateProjection A * diagonalMultiplier f =
      diagonalMultiplier f * coordinateProjection A := by
  refine ContinuousLinearMap.ext fun v => lp.ext (funext fun x => ?_)
  change coordinateProjection A (diagonalMultiplier f v) x =
    diagonalMultiplier f (coordinateProjection A v) x
  by_cases hx : x ∈ A
  · simp only [coordinateProjection_apply_of_mem A _ hx, diagonalMultiplier_apply]
  · simp only [coordinateProjection_apply_of_not_mem A _ hx, diagonalMultiplier_apply, mul_zero]

theorem compression_diagonalCommutator {X : Type u} (f : BoundedDiagonal X)
    (a : Operator X) (A B : Set X) :
    coordinateProjection A * diagonalCommutator f a * coordinateProjection B =
      diagonalCommutator f (coordinateProjection A * a * coordinateProjection B) := by
  simp only [diagonalCommutator, mul_sub, sub_mul, ← mul_assoc,
    coordinateProjection_comm_diagonalMultiplier]
  rw [mul_assoc (coordinateProjection A * a), ← coordinateProjection_comm_diagonalMultiplier f B,
    ← mul_assoc]

theorem quasiLocalModulus_diagonalCommutator_le {X : Type u} [PseudoMetricSpace X]
    (f : BoundedDiagonal X) (a : Operator X) (r : ℝ) :
    quasiLocalModulus (diagonalCommutator f a) r ≤ (2 * ‖f‖) * quasiLocalModulus a r := by
  refine (quasiLocalModulus_le_iff _ _ _).mpr fun A B hAB => ?_
  rw [compression_diagonalCommutator]
  exact (diagonalCommutator_norm_le f _).trans (mul_le_mul_of_nonneg_left
    ((quasiLocalModulus_le_iff a r _).mp le_rfl A B hAB)
    (mul_nonneg (by norm_num) (norm_nonneg f)))

theorem matrixEntry_diagonalCommutator {X : Type u} (f : BoundedDiagonal X)
    (a : Operator X) (x y : X) :
    matrixEntry (diagonalCommutator f a) x y = (f x - f y) * matrixEntry a x y := by
  simp only [matrixEntry, diagonalCommutator, sub_apply, mul_apply_eq_comp,
    lp.coeFn_sub, Pi.sub_apply, diagonalMultiplier_apply, diagonalMultiplier_delta,
    map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  exact (sub_mul _ _ _).symm

/-- For bounded diagonals the iterated commutator agrees with the manuscript's entrywise ad. -/
theorem matrixEntry_iterate_diagonalCommutator {X : Type u} (f : BoundedDiagonal X)
    (a : Operator X) (k : ℕ) (x y : X) :
    matrixEntry ((diagonalCommutator f)^[k] a) x y =
      (f x - f y) ^ k * matrixEntry a x y := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', matrixEntry_diagonalCommutator, ih, pow_succ', mul_assoc]

/-- Both bounds in Eq.AdbBounds, for every bounded complex diagonal and every radius. -/
theorem iterate_diagonalCommutator_bounds {X : Type u} [PseudoMetricSpace X]
    (f : BoundedDiagonal X) (a : Operator X) {L : ℝ} (hf : ‖f‖ ≤ L) (k : ℕ) (r : ℝ) :
    ‖(diagonalCommutator f)^[k] a‖ ≤ (2 * L) ^ k * ‖a‖ ∧
      quasiLocalModulus ((diagonalCommutator f)^[k] a) r ≤
        (2 * L) ^ k * quasiLocalModulus a r := by
  have hL : 0 ≤ L := (norm_nonneg f).trans hf
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ_apply', pow_succ']
    constructor
    · simpa only [mul_assoc] using (diagonalCommutator_norm_le f _).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left hf (by norm_num)) ih.1
          (norm_nonneg _) (mul_nonneg (by norm_num) hL))
    · simpa only [mul_assoc] using (quasiLocalModulus_diagonalCommutator_le f _ r).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left hf (by norm_num)) ih.2
          (quasiLocalModulus_nonneg _ r) (mul_nonneg (by norm_num) hL))

end DynamicalCStarAlgebras
