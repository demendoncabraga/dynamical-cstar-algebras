import DynamicalCStarAlgebras.GraphUnionLocalFiniteness

noncomputable section
open Classical Filter
namespace DynamicalCStarAlgebras

/-- The manuscript's coarse disjoint union of expander graphs, with nonempty
components as in `CoarseGraphUnion`. The degree and expansion constants are uniform. -/
structure ExpanderGraphUnion (X : Type*) [PseudoMetricSpace X] extends CoarseGraphUnion X where
  degreeBound : ℕ
  degree_le : ∀ n, letI := @Fintype.ofFinite {x : X // component x = n} (finite n)
    ∀ x, ((graph n).neighborFinset x).card ≤ degreeBound
  expansionConstant : ℝ
  expansion_pos : 0 < expansionConstant
  expansion : ∀ n, letI := @Fintype.ofFinite {x : X // component x = n} (finite n)
    HasVertexExpansion (graph n) expansionConstant
  card_tendsto : Tendsto (fun n => (Nat.card {x : X // component x = n} : ℝ)) atTop atTop

/-- Uniform local finiteness is a consequence of the expander-union data. -/
theorem ExpanderGraphUnion.uniformlyLocallyFinite
    {X : Type*} [PseudoMetricSpace X] (D : ExpanderGraphUnion X) :
    UniformlyLocallyFinite X :=
  D.toCoarseGraphUnion.uniformlyLocallyFinite D.degreeBound D.degree_le

/-- Theorem C's strict-inclusion argument on an expander union, with the finite
projection existence problem exposed as exactly the data of Assumption.1. -/
theorem ExpanderGraphUnion.strict_decay_inclusions_of_projection_data
    {X : Type*} [PseudoMetricSpace X] (D : ExpanderGraphUnion X)
    (p : Operator X) (hp : IsSelfAdjoint p)
    (hblock : ∀ x y, D.component x ≠ D.component y → matrixEntry p x y = 0)
    {α β C : ℝ} (hα : 0 < α) (hαβ : α < β) (hC : 0 < C)
    (n₀ : ℕ)
    (hzero : ∀ n < n₀, componentOperator
      (fun x : {x : X // D.component x = n} => (x : X)) Subtype.val_injective p = 0)
    (hdata : ∀ n, n₀ ≤ n →
      let q := componentOperator (fun x : {x : X // D.component x = n} => (x : X))
        Subtype.val_injective p
      IsStarProjection q ∧ Module.finrank ℂ (LinearMap.range q.toLinearMap) =
        ⌊(Nat.card {x : X // D.component x = n} : ℝ) /
          Real.log (Nat.card {x : X // D.component x = n}) ^ (2 * α)⌋₊ ∧
      ∀ A : Finset {x : X // D.component x = n}, A.Nonempty →
        ‖coordinateProjection (A : Set {x : X // D.component x = n}) * q‖ ≤ C * Real.sqrt
          (1 / Real.log (Nat.card {x : X // D.component x = n}) ^ (2 * α) +
            (A.card : ℝ) / Nat.card {x : X // D.component x = n} *
              Real.log (Real.exp 1 * Nat.card {x : X // D.component x = n} / A.card))) :
    (exponentialQuasiLocal : Set (Operator X)) ⊂ polynomialQuasiLocal α ∧
      (polynomialQuasiLocal β : Set (Operator X)) ⊂ polynomialQuasiLocal α ∧
      polynomialQuasiLocal β ⊂ quasiLocal (CoarseStructure.ofPseudoMetric X) :=
  D.toCoarseGraphUnion.strict_decay_inclusions_of_projection_data D.uniformlyLocallyFinite
    D.card_tendsto p hp hblock D.expansion_pos hα hαβ hC D.expansion n₀ hzero hdata

end DynamicalCStarAlgebras
