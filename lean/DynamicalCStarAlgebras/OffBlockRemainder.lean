import DynamicalCStarAlgebras.BlockCutAveraging

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

/-- Across different fibers, deleting the diagonal blocks changes no matrix coefficients. -/
theorem compression_offBlock_eq {X I : Type*} (π : X → I) (a b : Operator X)
    (hb : ∀ x y, matrixEntry b x y = if π x = π y then matrixEntry a x y else 0)
    (A B : Set X) (hAB : ∀ x ∈ A, ∀ y ∈ B, π x ≠ π y) :
    coordinateProjection A * (a - b) * coordinateProjection B =
      coordinateProjection A * a * coordinateProjection B := by
  apply operator_ext
  intro x y
  simp only [matrixEntry_compression]
  by_cases hmem : x ∈ A ∧ y ∈ B
  · simp only [if_pos hmem, ← matrixEntryCLM_apply, map_sub]
    simp only [matrixEntryCLM_apply, hb, if_neg (hAB x hmem.1 y hmem.2), sub_zero]
  · simp only [if_neg hmem]

/-- Separation of the remaining fibers makes the entire off-block tail small in norm. -/
theorem offBlock_tail_norm_le {X I : Type*} [PseudoMetricSpace X]
    (π : X → I) (a b : Operator X)
    (hb : ∀ x y, matrixEntry b x y = if π x = π y then matrixEntry a x y else 0)
    (F : Set X) (r : ℝ)
    (hsep : ∀ x ∉ F, ∀ y ∉ F, π x ≠ π y → r ≤ dist x y) :
    ‖coordinateProjection Fᶜ * (a - b) * coordinateProjection Fᶜ‖ ≤
      4 * quasiLocalModulus a r := by
  refine norm_le_four_mul_of_cuts π _ ?_ (quasiLocalModulus_nonneg a r) ?_
  · intro x y he
    rw [matrixEntry_compression]
    simp only [← matrixEntryCLM_apply, map_sub]
    simp only [matrixEntryCLM_apply, hb, if_pos he, sub_self, ite_self]
  · intro t
    rw [← mul_assoc, ← mul_assoc, coordinateProjection_mul_inter, mul_assoc,
      mul_assoc, coordinateProjection_mul_inter, ← mul_assoc]
    have hdiff : ∀ x ∈ {x | π x ∈ t} ∩ Fᶜ, ∀ y ∈ Fᶜ ∩ {x | π x ∉ t}, π x ≠ π y := by
      intro x hx y hy he
      exact hy.2 (he ▸ hx.1)
    rw [compression_offBlock_eq π a b hb _ _ hdiff]
    exact (quasiLocalModulus_le_iff a r _).mp le_rfl _ _
      (fun x hx y hy => hsep x hx.2 y hy.1 (hdiff x hx y hy))

/-- The off-block part is Roe when distinct fibers become separated outside finite sets. -/
theorem offBlock_mem_uniformRoe {X I : Type*} [PseudoMetricSpace X]
    (π : X → I) (a b : Operator X)
    (ha : IsQuasiLocal (CoarseStructure.ofPseudoMetric X) a)
    (hb : ∀ x y, matrixEntry b x y = if π x = π y then matrixEntry a x y else 0)
    (hsep : ∀ r : ℝ, ∃ F : Set X, F.Finite ∧
      ∀ x ∉ F, ∀ y ∉ F, π x ≠ π y → r ≤ dist x y) :
    a - b ∈ uniformRoe (CoarseStructure.ofPseudoMetric X) := by
  suffices a - b ∈ closure (uniformRoe (CoarseStructure.ofPseudoMetric X)) by
    simpa only [uniformRoe, closure_closure] using this
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨r, _, hr⟩ := (isMetricQuasiLocal_iff_modulus a).mp
    ((isQuasiLocal_iff_metric a).mp ha) (ε / 8) (by positivity)
  obtain ⟨F, hF, hdist⟩ := hsep r
  refine ⟨a - b - coordinateProjection Fᶜ * (a - b) * coordinateProjection Fᶜ,
    remove_finite_buffer_error_mem_uniformRoe (a - b) hF, ?_⟩
  rw [dist_eq_norm, sub_sub_cancel]
  exact (offBlock_tail_norm_le π a b hb F r hdist).trans_lt (by linarith)

end DynamicalCStarAlgebras
