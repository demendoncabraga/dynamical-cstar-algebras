import DynamicalCStarAlgebras.FiniteRankRoe

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

theorem compression_remove_buffer {X : Type*} (a : Operator X) (A B F : Set X) :
    coordinateProjection A * (coordinateProjection Fᶜ * a * coordinateProjection Fᶜ) *
      coordinateProjection B = coordinateProjection (A \ F) * a * coordinateProjection (B \ F) := by
  refine operator_ext fun x y => ?_
  simp only [matrixEntry_compression, Set.mem_sdiff, Set.mem_compl_iff]
  split_ifs <;> simp_all

/-- The finite-buffer claim in the proof of non-quasi-local detection. -/
theorem nonQuasiLocal_finite_buffer_witnesses {X : Type*} [PseudoMetricSpace X]
    (a : Operator X) (ha : ¬ IsQuasiLocal (CoarseStructure.ofPseudoMetric X) a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : ℝ, ∀ F : Set X, F.Finite →
      ∃ A B : Set X, A.Finite ∧ B.Finite ∧ A ⊆ Fᶜ ∧ B ⊆ Fᶜ ∧
        (∀ x ∈ A, ∀ y ∈ B, R ≤ dist x y) ∧
        ε < ‖coordinateProjection A * a * coordinateProjection B‖ := by
  obtain ⟨ε, hε, hw⟩ := nonQuasiLocal_finite_witnesses a ha
  refine ⟨ε / 2, half_pos hε, fun R F hF => ?_⟩
  let b := coordinateProjection Fᶜ * a * coordinateProjection Fᶜ
  have hc : IsMetricQuasiLocal (a - b) := (isQuasiLocal_iff_metric _).mp
    (uniformRoe_subset_quasiLocal _ (remove_finite_buffer_error_mem_uniformRoe a hF))
  obtain ⟨S, hS, hcS⟩ := hc (ε / 2) (half_pos hε)
  obtain ⟨A, B, hA, hB, hAB, hab⟩ := hw (max R S)
  have hsmall := hcS A B fun x hx y hy => (le_max_right R S).trans (hAB x hx y hy)
  have htriangle := norm_add_le (coordinateProjection A * (a - b) * coordinateProjection B)
    (coordinateProjection A * b * coordinateProjection B)
  rw [← add_mul, ← mul_add, sub_add_cancel] at htriangle
  refine ⟨A \ F, B \ F, hA.sdiff, hB.sdiff, fun _ hx => hx.2, fun _ hy => hy.2,
    fun x hx y hy => (le_max_left R S).trans (hAB x hx.1 y hy.1), ?_⟩
  rw [← compression_remove_buffer]
  change ε / 2 < ‖coordinateProjection A * b * coordinateProjection B‖
  linarith

end DynamicalCStarAlgebras
