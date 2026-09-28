import DynamicalCStarAlgebras.SeparatedBlockHeights

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

/-- A finite matrix form of a compression only sees the coordinates in its two supports. -/
theorem finiteMatrixForm_compression_restrict {X : Type*} (a : Operator X)
    (A B : Set X) (v w : X →₀ ℂ) :
    finiteMatrixForm (matrixEntry (coordinateProjection A * a * coordinateProjection B)) v w =
      finiteMatrixForm (matrixEntry (coordinateProjection (A ∩ (v.support : Set X)) * a *
        coordinateProjection (B ∩ (w.support : Set X)))) v w := by
  simp only [finiteMatrixForm_apply]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  simp only [matrixEntry_compression, Set.mem_inter_iff, Finset.mem_coe, hx, hy, and_true]

/-- Uniform bounds on all finite subcompressions bound the original compression. -/
theorem compression_norm_le_of_finite_subsets {X : Type*} (a : Operator X)
    (A B : Set X) {C : ℝ} (hC : 0 ≤ C)
    (hfin : ∀ S T : Set X, S.Finite → T.Finite → S ⊆ A → T ⊆ B →
      ‖coordinateProjection S * a * coordinateProjection T‖ ≤ C) :
    ‖coordinateProjection A * a * coordinateProjection B‖ ≤ C := by
  refine norm_le_of_finiteMatrixForm_bound _ hC fun v w => ?_
  rw [finiteMatrixForm_compression_restrict]
  exact (norm_finiteMatrixForm_matrixEntry_le _ v w).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (hfin _ _ (v.support.finite_toSet.inter_of_right A)
        (w.support.finite_toSet.inter_of_right B) Set.inter_subset_left Set.inter_subset_left)
      (norm_nonneg _)) (norm_nonneg _))

/-- Every strict compression lower bound is witnessed by finite subsets. -/
theorem exists_finite_subcompression {X : Type*} (a : Operator X) (A B : Set X)
    {C : ℝ} (hC : 0 ≤ C)
    (ha : C < ‖coordinateProjection A * a * coordinateProjection B‖) :
    ∃ S T : Set X, S.Finite ∧ T.Finite ∧ S ⊆ A ∧ T ⊆ B ∧
      C < ‖coordinateProjection S * a * coordinateProjection T‖ := by
  by_contra hn
  push Not at hn
  exact (not_le_of_gt ha) (compression_norm_le_of_finite_subsets a A B hC hn)

/-- Non-quasi-locality has a uniform positive lower bound witnessed by finite separated sets. -/
theorem nonQuasiLocal_finite_witnesses {X : Type*} [PseudoMetricSpace X] (a : Operator X)
    (ha : ¬ IsQuasiLocal (CoarseStructure.ofPseudoMetric X) a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : ℝ, ∃ A B : Set X, A.Finite ∧ B.Finite ∧
      (∀ x ∈ A, ∀ y ∈ B, R ≤ dist x y) ∧
      ε < ‖coordinateProjection A * a * coordinateProjection B‖ := by
  rw [isQuasiLocal_iff_metric] at ha
  simp only [IsMetricQuasiLocal, not_forall, not_exists, not_and, not_le] at ha
  obtain ⟨ε, hε, hw⟩ := ha
  refine ⟨ε, hε, fun R => ?_⟩
  obtain ⟨A, B, hAB, hab⟩ := hw (max R 0 + 1) (by positivity)
  obtain ⟨S, T, hS, hT, hSA, hTB, hst⟩ := exists_finite_subcompression a A B hε.le hab
  exact ⟨S, T, hS, hT, fun x hx y hy =>
    (le_max_left R 0).trans ((le_add_of_nonneg_right zero_le_one).trans
      (hAB x (hSA hx) y (hTB hy))), hst⟩

end DynamicalCStarAlgebras
