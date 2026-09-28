import DynamicalCStarAlgebras.PropertyASigns
import DynamicalCStarAlgebras.CosineSmoothingEstimate
import DynamicalCStarAlgebras.FiniteOperatorAverages

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical
open scoped BigOperators
namespace DynamicalCStarAlgebras

lemma expect_boolSign_mul {I : Type*} [Fintype I] (i j : I) :
    (𝔼 σ : I → Bool, boolSign (σ i) * boolSign (σ j)) = if i = j then 1 else 0 := by
  rw [Fintype.expect_eq_sum_div_card, sum_boolSign_mul]
  split_ifs
  · exact div_self (by exact_mod_cast Fintype.card_ne_zero)
  · rw [zero_div]

namespace FiniteSquarePartition
variable {X I : Type*} (P : FiniteSquarePartition X I)

lemma expect_signed_mul (s : Finset I) (x y : X) :
    (𝔼 σ : s → Bool, P.signed s σ x * P.signed s σ y) =
      ∑ i ∈ s, P.row x i * P.row y i := by
  unfold signed
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  simp_rw [Finset.expect_sum_comm]
  have he (i j : s) : (𝔼 σ : s → Bool,
      boolSign (σ i) * P.row x i * (boolSign (σ j) * P.row y j)) =
      (if i = j then 1 else 0) * (P.row x i * P.row y j) := by
    have hp (σ : s → Bool) : boolSign (σ i) * P.row x i * (boolSign (σ j) * P.row y j) =
        (boolSign (σ i) * boolSign (σ j)) * (P.row x i * P.row y j) := by ring
    simp_rw [hp]
    rw [← Finset.expect_mul]
    congr 1
    convert expect_boolSign_mul i j using 1
    · congr 3
      exact Subsingleton.elim _ _
    · by_cases hij : i = j <;> simp [hij]
  simp_rw [he]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.sum_coe_sort s (fun i => P.row x i * P.row y i)

/-- A bounded real diagonal for a finite sign combination. -/
def signedDiagonal (s : Finset I) (σ : s → Bool) : BoundedDiagonal X :=
  boundedRealDiagonal (P.signed s σ) s.card (P.signed_abs_le_card s σ)


/-- The identity minus smoothing is the finite sign average of diagonal commutators
on any finite collection of rows containing the relevant partition supports. -/
lemma finiteMatrixForm_smoothing_error (a : Operator X) (v w : X →₀ ℂ) (s : Finset I)
    (hs : ∀ x ∈ v.support, (P.row x).support ⊆ s) :
    finiteMatrixForm (matrixEntry (a - P.smoothing a)) v w =
      finiteMatrixForm (matrixEntry (operatorAverage (fun σ : s → Bool =>
        star (diagonalMultiplier (P.signedDiagonal s σ)) *
          diagonalCommutator (P.signedDiagonal s σ) a))) v w := by
  simp only [finiteMatrixForm_apply]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y _ => ?_
  congr 2
  have hsq : (𝔼 σ : s → Bool, P.signed s σ x ^ 2) = 1 := by
    rw [P.expect_signed_sq]
    rw [← P.tsum_sq x, tsum_eq_sum (s := s)]
    intro i hi
    have hz : P.row x i = 0 := Finsupp.notMem_support_iff.mp (fun hp => hi (hs x hx hp))
    simp [hz]
  rw [matrixEntry_operatorAverage]
  change (matrixEntryCLM x y) (_ - _) = _
  rw [map_sub]
  simp only [matrixEntryCLM_apply, matrixEntry_star_diagonal_mul, matrixEntry_diagonalCommutator,
    signedDiagonal, boundedRealDiagonal_apply, Complex.star_def, Complex.conj_ofReal]
  have he (σ : s → Bool) : (P.signed s σ x : ℂ) *
      ((P.signed s σ x : ℂ) - P.signed s σ y) * matrixEntry a x y =
      ((P.signed s σ x ^ 2 : ℝ) : ℂ) * matrixEntry a x y -
      ((P.signed s σ x * P.signed s σ y : ℝ) : ℂ) * matrixEntry a x y := by push_cast; ring
  simp_rw [← mul_assoc (P.signed s _ x : ℂ), he]
  rw [Finset.expect_sub_distrib, ← Finset.expect_mul, ← Finset.expect_mul,
    ← Complex.ofReal_expect, ← Complex.ofReal_expect, hsq, Complex.ofReal_one, one_mul,
    P.expect_signed_mul, P.matrixEntry_smoothing, P.smoothingMatrix_eq_sum a x y s (hs x hx)]
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

end FiniteSquarePartition
end DynamicalCStarAlgebras
