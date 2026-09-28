import DynamicalCStarAlgebras.GoodSubspaces
import DynamicalCStarAlgebras.ExpanderMatrixEmbedding
import DynamicalCStarAlgebras.NonemptyExpanderUnion

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- Unconditional bounded matrix-product embedding on an expander graph union. -/
theorem ExpanderGraphUnion.exists_matrixProduct_embedding {X : Type*} [PseudoMetricSpace X]
    (D : ExpanderGraphUnion X) :
    ∃ Φ : BoundedMatrixProduct →⋆ₙₐ[ℂ] Operator X,
      Function.Injective Φ ∧ Isometry Φ ∧
      ∀ a, HasExponentialDecay (Φ a) ∧ Φ a ∈ exponentialQuasiLocal := by
  let : ∀ n, Fintype {x : X // D.component x = n} :=
    fun n => @Fintype.ofFinite _ (D.finite n)
  have hg (n : ℕ) := exists_quarter_power_subspace (X := {x : X // D.component x = n})
  choose W hdim hgood using hg
  apply D.toCoarseGraphUnion.exists_matrixProduct_embedding_of_good_subspaces
    D.expansion_pos (by norm_num : (1 : ℝ) ≤ 96) D.expansion D.card_tendsto W
  · intro n
    simpa only [Nat.card_eq_fintype_card] using hdim n
  · intro n S δ hδ hhalf hcard
    apply hgood n S δ hδ hhalf
    simpa only [Nat.card_eq_fintype_card] using hcard

/-- Thm.Exp.decay.Still.Contains for the literal raw expander data, including
possibly empty initial graph components. -/
theorem ExpanderGraphUnionData.exists_matrixProduct_embedding {X : Type*} [PseudoMetricSpace X]
    (D : ExpanderGraphUnionData X) :
    ∃ Φ : BoundedMatrixProduct →⋆ₙₐ[ℂ] Operator X,
      Function.Injective Φ ∧ Isometry Φ ∧
      ∀ a, HasExponentialDecay (Φ a) ∧ Φ a ∈ exponentialQuasiLocal :=
  D.toExpanderGraphUnion.exists_matrixProduct_embedding

/-- The product inclusion in the strip algebra stated in Remark L1177. -/
theorem ExpanderGraphUnionData.exists_matrixProduct_embedding_strip
    {X : Type*} [PseudoMetricSpace X] (D : ExpanderGraphUnionData X) :
    ∃ Φ : BoundedMatrixProduct →⋆ₙₐ[ℂ] Operator X,
      Function.Injective Φ ∧ Isometry Φ ∧
      ∀ a, Φ a ∈ stripAnalyticPoints (CoarseStructure.ofPseudoMetric X) := by
  obtain ⟨Φ, hΦ, hi, hg⟩ := D.exists_matrixProduct_embedding
  exact ⟨Φ, hΦ, hi, fun a => (hg a).1.mem_stripAnalyticPoints
    D.toExpanderGraphUnion.toCoarseGraphUnion⟩

end DynamicalCStarAlgebras
