import DynamicalCStarAlgebras.ExpanderMatrixExistence
import DynamicalCStarAlgebras.ExpanderProjectionExistence
import DynamicalCStarAlgebras.BoundedProductNonembedding

noncomputable section
namespace DynamicalCStarAlgebras

/-- The leftmost strict link: the constructed bounded matrix product cannot
lie in the uniform Roe algebra. -/
theorem ExpanderGraphUnion.uniformRoe_ssubset_exponentialQuasiLocal
    {X : Type*} [PseudoMetricSpace X] (D : ExpanderGraphUnion X) :
    uniformRoe (CoarseStructure.ofPseudoMetric X) ⊂ (exponentialQuasiLocal : Set (Operator X)) := by
  refine ⟨uniformRoe_subset_exponentialQuasiLocal, ?_⟩
  intro hreverse
  obtain ⟨Φ, hΦ, _, hg⟩ := D.exists_matrixProduct_embedding
  exact boundedMatrixProduct_not_range_subset_uniformRoe D.uniformlyLocallyFinite Φ hΦ
    (fun a => hreverse (hg a).2)

/-- Theorem D for literal expander data, including empty initial components,
with all strict inclusions and the bounded complex matrix-product embedding. -/
theorem theoremD {X : Type*} [PseudoMetricSpace X] (D : ExpanderGraphUnionData X)
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    uniformRoe (CoarseStructure.ofPseudoMetric X) ⊂ (exponentialQuasiLocal : Set (Operator X)) ∧
    (exponentialQuasiLocal : Set (Operator X)) ⊂ polynomialQuasiLocal β ∧
    (polynomialQuasiLocal β : Set (Operator X)) ⊂ polynomialQuasiLocal α ∧
    polynomialQuasiLocal α ⊂ quasiLocal (CoarseStructure.ofPseudoMetric X) ∧
    ∃ Φ : BoundedMatrixProduct →⋆ₙₐ[ℂ] Operator X,
      Function.Injective Φ ∧ Isometry Φ ∧ ∀ a, Φ a ∈ exponentialQuasiLocal := by
  obtain ⟨h₁, h₂, h₃⟩ := D.toExpanderGraphUnion.strict_decay_inclusions hα hαβ
  obtain ⟨Φ, hΦ, hi, hg⟩ := D.exists_matrixProduct_embedding
  exact ⟨D.toExpanderGraphUnion.uniformRoe_ssubset_exponentialQuasiLocal,
    h₁, h₂, h₃, Φ, hΦ, hi, fun a => (hg a).2⟩

/-- Theorem C: the strip algebra is strictly between Roe and quasi-local. -/
theorem theoremC {X : Type*} [PseudoMetricSpace X] (D : ExpanderGraphUnionData X) :
    uniformRoe (CoarseStructure.ofPseudoMetric X) ⊂
      stripAnalyticPoints (CoarseStructure.ofPseudoMetric X) ∧
    stripAnalyticPoints (CoarseStructure.ofPseudoMetric X) ⊂
      quasiLocal (CoarseStructure.ofPseudoMetric X) := by
  have he : stripAnalyticPoints (CoarseStructure.ofPseudoMetric X) =
      (exponentialQuasiLocal : Set (Operator X)) :=
    Set.Subset.antisymm (stripAnalyticPoints_subset_exponentialQuasiLocal
      D.toExpanderGraphUnion.uniformlyLocallyFinite)
      (exponentialQuasiLocal_subset_stripAnalyticPoints D.toExpanderGraphUnion.toCoarseGraphUnion)
  rw [he]
  obtain ⟨h₁, _, h₃⟩ := D.toExpanderGraphUnion.strict_decay_inclusions
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
  refine ⟨D.toExpanderGraphUnion.uniformRoe_ssubset_exponentialQuasiLocal, ?_⟩
  exact h₁.trans (lt_of_le_of_lt (polynomialQuasiLocal_antitone (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (1 : ℝ) ≤ 2)) h₃)

end DynamicalCStarAlgebras
