import DynamicalCStarAlgebras.PropertyASignOperators
import DynamicalCStarAlgebras.PropertyACommutator

noncomputable section
open Classical
open scoped BigOperators
namespace DynamicalCStarAlgebras
namespace FiniteProbabilityKernel
variable {X : Type*} (μ ν : FiniteProbabilityKernel X)

lemma norm_average_signed_commutator_le {t : ℝ} (ht : 0 < t)
    (a : Operator X) (ha : ‖a‖ ≤ 1) {E : Set (X × X)} (haE : IsQuasiLocalAt a (t ^ 4) E)
    (hμ : ∀ p ∈ E, μ.variation p.1 p.2 ≤ t ^ 2)
    (hν : ∀ x z, μ.row x z ≠ 0 → ν.variation x z ≤ t ^ 2) (s : Finset X) :
    ‖operatorAverage (fun σ : s → Bool =>
      star (diagonalMultiplier (ν.squarePartition.signedDiagonal s σ)) *
        diagonalCommutator (ν.squarePartition.signedDiagonal s σ) a)‖ ≤ 18 * t := by
  let F := ν.squarePartition.signedDiagonal s
  let H := μ.smoothedSignDiagonal ν ht s
  let D : (s → Bool) → BoundedDiagonal X := fun σ => F σ - H σ
  have hF (x : X) : (𝔼 σ : s → Bool, ‖F σ x‖ ^ 2) ≤ (1 : ℝ) ^ 2 := by
    simpa only [F, FiniteSquarePartition.signedDiagonal, boundedRealDiagonal_apply, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, one_pow] using ν.squarePartition.expect_signed_sq_le s x
  have hD (x : X) : (𝔼 σ : s → Bool, ‖D σ x‖ ^ 2) ≤ (3 * t) ^ 2 := by
    simpa only [D, F, H, lp.coeFn_sub, Pi.sub_apply, FiniteSquarePartition.signedDiagonal, boundedRealDiagonal_apply,
      smoothedSignDiagonal, boundedRealDiagonal_apply, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      sq_abs] using μ.expect_signed_sub_smoothed_sq ν ht s x (hν x)
  have hmain := norm_expect_diagonal_mul_le F (fun σ => diagonalCommutator (H σ) a)
    zero_le_one (show 0 ≤ 12 * t by positivity) hF
    (fun σ => μ.smoothedSign_commutator_le ν ht s σ a ha haE hμ)
  have hright := norm_expect_diagonal_sandwich_le F D a zero_le_one
    (show 0 ≤ 3 * t by positivity) hF hD
  have hleft : ‖operatorAverage (fun σ : s → Bool =>
      star (diagonalMultiplier (F σ)) * diagonalMultiplier (D σ)) * a‖ ≤ 3 * t := by
    have hb := norm_expect_diagonal_sandwich_le F D (1 : Operator X) zero_le_one
      (show 0 ≤ 3 * t by positivity) hF hD
    simp only [mul_one, one_mul] at hb
    have hnorm : ‖(1 : Operator X)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    exact (norm_mul_le _ _).trans ((mul_le_mul hb ha (norm_nonneg _)
      (by positivity)).trans (by nlinarith))
  have hd (σ : s → Bool) : diagonalMultiplier (D σ) =
      diagonalMultiplier (F σ) - diagonalMultiplier (H σ) :=
    map_sub diagonalMultiplierHom (F σ) (H σ)
  have he : (fun σ : s → Bool => star (diagonalMultiplier (F σ)) * diagonalCommutator (F σ) a) =
      (fun σ => star (diagonalMultiplier (F σ)) * diagonalCommutator (H σ) a +
        (star (diagonalMultiplier (F σ)) * diagonalMultiplier (D σ)) * a -
        star (diagonalMultiplier (F σ)) * a * diagonalMultiplier (D σ)) := by
    funext σ
    rw [hd]
    unfold diagonalCommutator
    noncomm_ring
  change ‖operatorAverage (fun σ : s → Bool =>
    star (diagonalMultiplier (F σ)) * diagonalCommutator (F σ) a)‖ ≤ _
  rw [he, operatorAverage_sub, operatorAverage_add, operatorAverage_mul_right]
  have hnorm := norm_sub_le
    (operatorAverage (fun σ : s → Bool => star (diagonalMultiplier (F σ)) * diagonalCommutator (H σ) a) +
      operatorAverage (fun σ : s → Bool => star (diagonalMultiplier (F σ)) * diagonalMultiplier (D σ)) * a)
    (operatorAverage (fun σ : s → Bool => star (diagonalMultiplier (F σ)) * a * diagonalMultiplier (D σ)))
  exact (hnorm.trans (add_le_add (norm_add_le _ _) le_rfl)).trans (by
    simp only [one_mul] at hmain hright
    nlinarith [mul_le_mul_of_nonneg_right ha (show 0 ≤ 3 * t by positivity)])

/-- Ozawa's quantitative finite-propagation approximation, with error exactly 18t. -/
theorem smoothing_error_le {t : ℝ} (ht : 0 < t)
    (a : Operator X) (ha : ‖a‖ ≤ 1) {E : Set (X × X)} (haE : IsQuasiLocalAt a (t ^ 4) E)
    (hμ : ∀ p ∈ E, μ.variation p.1 p.2 ≤ t ^ 2)
    (hν : ∀ x z, μ.row x z ≠ 0 → ν.variation x z ≤ t ^ 2) :
    ‖a - ν.squarePartition.smoothing a‖ ≤ 18 * t := by
  apply norm_le_of_finiteMatrixForm_bound _ (by positivity)
  intro v w
  let s := v.support.biUnion fun x => (ν.squarePartition.row x).support
  rw [ν.squarePartition.finiteMatrixForm_smoothing_error a v w s
    (fun x hx i hi => Finset.mem_biUnion.mpr ⟨x, hx, hi⟩)]
  exact (norm_finiteMatrixForm_matrixEntry_le _ v w).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (μ.norm_average_signed_commutator_le ν ht a ha haE hμ hν s) (norm_nonneg _)) (norm_nonneg _))

end FiniteProbabilityKernel
end DynamicalCStarAlgebras
