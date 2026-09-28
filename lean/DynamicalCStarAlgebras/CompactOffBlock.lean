import DynamicalCStarAlgebras.StripCharacterization
import Mathlib.Analysis.Normed.Operator.Compact.Basic

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

/-- Rank-one Hilbert-space operators are compact. -/
theorem isCompactOperator_rankOne {X : Type*} (v w : HilbertSpace X) :
    IsCompactOperator (InnerProductSpace.rankOne ℂ v w) := by
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℂ v)).comp_clm (innerSL ℂ w)

/-- A projection onto finitely many coordinates is compact. -/
theorem isCompactOperator_finite_coordinateProjection {X : Type*} {F : Set X}
    (hF : F.Finite) : IsCompactOperator (coordinateProjection F) := by
  classical
  rw [← hF.coe_toFinset]
  have he := mul_coordinateProjection_finset (1 : Operator X) hF.toFinset
  simp only [one_mul, one_apply_eq_self] at he
  rw [he]
  exact (compactOperator (RingHom.id ℂ) (HilbertSpace X) (HilbertSpace X)).sum_mem
    (fun x _ => isCompactOperator_rankOne _ _)

/-- Deleting finitely many rows and columns changes an operator by a compact operator. -/
theorem remove_finite_buffer_error_isCompactOperator {X : Type*} (a : Operator X)
    {F : Set X} (hF : F.Finite) :
    IsCompactOperator (a - coordinateProjection Fᶜ * a * coordinateProjection Fᶜ) := by
  have hcomp : coordinateProjection Fᶜ = 1 - coordinateProjection F := by
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm, coordinateProjection_add_compl]
  have he : a - coordinateProjection Fᶜ * a * coordinateProjection Fᶜ =
      coordinateProjection F * a + (coordinateProjection Fᶜ * a) * coordinateProjection F := by
    rw [hcomp]
    noncomm_ring
  rw [he]
  exact ((isCompactOperator_finite_coordinateProjection hF).comp_clm a).add
    ((isCompactOperator_finite_coordinateProjection hF).clm_comp (coordinateProjection Fᶜ * a))

/-- The manuscript's off-block compactness assertion for quasi-local operators. -/
theorem offBlock_isCompactOperator {X I : Type*} [PseudoMetricSpace X]
    (π : X → I) (a b : Operator X)
    (ha : IsQuasiLocal (CoarseStructure.ofPseudoMetric X) a)
    (hb : ∀ x y, matrixEntry b x y = if π x = π y then matrixEntry a x y else 0)
    (hsep : ∀ r : ℝ, ∃ F : Set X, F.Finite ∧
      ∀ x ∉ F, ∀ y ∉ F, π x ≠ π y → r ≤ dist x y) :
    IsCompactOperator (a - b) := by
  have hclosed : IsClosed {d : Operator X | IsCompactOperator d} :=
    isClosed_setOfPred_isCompactOperator
  suffices a - b ∈ closure {d : Operator X | IsCompactOperator d} by
    rwa [hclosed.closure_eq] at this
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨r, _, hr⟩ := (isMetricQuasiLocal_iff_modulus a).mp
    ((isQuasiLocal_iff_metric a).mp ha) (ε / 8) (by positivity)
  obtain ⟨F, hF, hdist⟩ := hsep r
  refine ⟨a - b - coordinateProjection Fᶜ * (a - b) * coordinateProjection Fᶜ,
    remove_finite_buffer_error_isCompactOperator (a - b) hF, ?_⟩
  rw [dist_eq_norm, sub_sub_cancel]
  exact (offBlock_tail_norm_le π a b hb F r hdist).trans_lt (by linarith)

/-- Every quasi-local operator on a coarse graph union has a compact off-block remainder. -/
theorem CoarseGraphUnion.exists_compact_offBlock {X : Type*} [PseudoMetricSpace X]
    (D : CoarseGraphUnion X) (a : Operator X)
    (ha : IsQuasiLocal (CoarseStructure.ofPseudoMetric X) a) :
    ∃ b : Operator X,
      (∀ x y, matrixEntry b x y =
        if D.component x = D.component y then matrixEntry a x y else 0) ∧
      IsCompactOperator (a - b) := by
  obtain ⟨b, _, hb, _⟩ := exists_blockDiagonal_modulus_le D.component a
  refine ⟨b, ?_, offBlock_isCompactOperator D.component a b ha hb D.finite_separation⟩
  intro x y
  rw [hb]
  split_ifs <;> rfl

end DynamicalCStarAlgebras
