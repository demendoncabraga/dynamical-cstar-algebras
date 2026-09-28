import DynamicalCStarAlgebras.CosineSmoothing

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- A locally finite real square partition of unity. -/
structure FiniteSquarePartition (X I : Type*) where
  row : X → I →₀ ℝ
  sum_sq : ∀ x, ∑ i ∈ (row x).support, row x i ^ 2 = 1

namespace FiniteSquarePartition
variable {X I : Type*} (P : FiniteSquarePartition X I)

lemma summable_sq (x : X) : Summable (fun i => P.row x i ^ 2) :=
  summable_of_ne_finset_zero (s := (P.row x).support) (by
    intro i hi
    simp only [Finsupp.notMem_support_iff.mp hi, zero_pow (by decide : 2 ≠ 0)])

lemma tsum_sq (x : X) : ∑' i, P.row x i ^ 2 = 1 := by
  rw [tsum_eq_sum (s := (P.row x).support)]
  · exact P.sum_sq x
  · intro i hi
    simp only [Finsupp.notMem_support_iff.mp hi, zero_pow (by decide : 2 ≠ 0)]

lemma sum_sq_le (x : X) (s : Finset I) : ∑ i ∈ s, P.row x i ^ 2 ≤ 1 := by
  simpa only [P.tsum_sq] using (P.summable_sq x).sum_le_tsum s (fun _ _ => sq_nonneg _)

lemma abs_row_le_one (x : X) (i : I) : |P.row x i| ≤ 1 := by
  have hs := P.sum_sq_le x {i}
  simp only [Finset.sum_singleton] at hs
  nlinarith [sq_abs (P.row x i)]

/-- One real partition coefficient as a bounded diagonal. -/
def diagonal (i : I) : BoundedDiagonal X :=
  boundedRealDiagonal (fun x => P.row x i) 1 (fun x => P.abs_row_le_one x i)


lemma sum_diagonal_sq_le (s : Finset I) (x : X) :
    ∑ i ∈ s, ‖P.diagonal i x‖ ^ 2 ≤ 1 := by
  simpa only [diagonal, boundedRealDiagonal_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs] using P.sum_sq_le x s

/-- The matrix of the partition Schur multiplier. -/
def smoothingMatrix (a : Operator X) (x y : X) : ℂ :=
  ∑' i, (P.row x i : ℂ) * matrixEntry a x y * (P.row y i : ℂ)

lemma smoothingMatrix_eq_sum (a : Operator X) (x y : X) (s : Finset I)
    (hs : (P.row x).support ⊆ s) :
    P.smoothingMatrix a x y = ∑ i ∈ s, (P.row x i : ℂ) * matrixEntry a x y * (P.row y i : ℂ) := by
  apply tsum_eq_sum
  intro i hi
  have hx : i ∉ (P.row x).support := fun h => hi (hs h)
  simp only [Finsupp.notMem_support_iff.mp hx, Complex.ofReal_zero, zero_mul]

lemma smoothingMatrix_form_bound (a : Operator X) (v w : X →₀ ℂ) :
    ‖finiteMatrixForm (P.smoothingMatrix a) v w‖ ≤ ‖a‖ * ‖finiteVector v‖ * ‖finiteVector w‖ := by
  let s := v.support.biUnion fun x => (P.row x).support
  let b : Operator X := ∑ i ∈ s, star (diagonalMultiplier (P.diagonal i)) * a *
    diagonalMultiplier (P.diagonal i)
  have he : finiteMatrixForm (P.smoothingMatrix a) v w = finiteMatrixForm (matrixEntry b) v w := by
    simp only [finiteMatrixForm_apply]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y _hy => ?_
    have hs : (P.row x).support ⊆ s := fun i hi => Finset.mem_biUnion.mpr ⟨x, hx, hi⟩
    rw [P.smoothingMatrix_eq_sum a x y s hs]
    congr 2
    change _ = (matrixEntryCLM x y) (∑ i ∈ s, _)
    simp only [map_sum, matrixEntryCLM_apply, matrixEntry_star_diagonal_sandwich,
      diagonal, boundedRealDiagonal_apply, Complex.star_def, Complex.conj_ofReal]
  have hb : ‖b‖ ≤ ‖a‖ := norm_sum_diagonal_sandwich_le s _ (P.sum_diagonal_sq_le s) a
  rw [he]
  exact (norm_finiteMatrixForm_matrixEntry_le b v w).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) (norm_nonneg _))

/-- The bounded operator obtained by summing the diagonal sandwiches of a partition. -/
def smoothing (a : Operator X) : Operator X :=
  operatorOfFiniteForm (finiteMatrixForm (P.smoothingMatrix a)) (P.smoothingMatrix_form_bound a)

lemma smoothing_norm_le (a : Operator X) : ‖P.smoothing a‖ ≤ ‖a‖ :=
  norm_operatorOfFiniteForm_le _ (norm_nonneg _) (P.smoothingMatrix_form_bound a)

lemma matrixEntry_smoothing (a : Operator X) (x y : X) :
    matrixEntry (P.smoothing a) x y = P.smoothingMatrix a x y :=
  (matrixEntry_operatorOfFiniteForm _ (norm_nonneg _) (P.smoothingMatrix_form_bound a) x y).trans
    (finiteMatrixForm_single_one _ x y)

/-- A uniformly bounded support diameter gives the actual finite-propagation approximant. -/
lemma smoothing_propagation [PseudoMetricSpace X] {S : ℝ}
    (hS : ∀ x y i, P.row x i ≠ 0 → P.row y i ≠ 0 → dist x y ≤ S)
    (a : Operator X) (x y : X) (hxy : S < dist x y) :
    matrixEntry (P.smoothing a) x y = 0 := by
  rw [P.matrixEntry_smoothing]
  unfold smoothingMatrix
  suffices hz : ∀ i, (P.row x i : ℂ) * matrixEntry a x y * (P.row y i : ℂ) = 0 by
    simp only [hz, tsum_zero]
  intro i
  by_cases hx : P.row x i = 0
  · simp [hx]
  · have hy : P.row y i = 0 := by
      by_contra hy
      exact (not_le_of_gt hxy) (hS x y i hx hy)
    simp [hy]

end FiniteSquarePartition
end DynamicalCStarAlgebras
