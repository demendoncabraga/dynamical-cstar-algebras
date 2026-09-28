import DynamicalCStarAlgebras.ExpanderProjectionMembership

noncomputable section
open Classical Filter
namespace DynamicalCStarAlgebras

/-- The strict-inclusion argument in Theorem C, from the projections specified in
Assumption.1. Their existence remains a separate finite-dimensional assertion. -/
theorem CoarseGraphUnion.strict_decay_inclusions_of_projection_data
    {X : Type*} [PseudoMetricSpace X] (D : CoarseGraphUnion X)
    (hX : UniformlyLocallyFinite X)
    (hN : Tendsto (fun n => (Nat.card {x : X // D.component x = n} : ℝ)) atTop atTop)
    (p : Operator X) (hp : IsSelfAdjoint p)
    (hblock : ∀ x y, D.component x ≠ D.component y → matrixEntry p x y = 0)
    {γ α β C : ℝ} (hγ : 0 < γ) (hα : 0 < α) (hαβ : α < β) (hC : 0 < C)
    (hExp : ∀ n, letI := @Fintype.ofFinite {x : X // D.component x = n} (D.finite n)
      HasVertexExpansion (D.graph n) γ)
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
      polynomialQuasiLocal β ⊂ quasiLocal (CoarseStructure.ofPseudoMetric X) := by
  have hmem := D.projection_mem_polynomialQuasiLocal p hp hblock hγ hα hC hExp n₀ hzero
    (fun n hn => (hdata n hn).2.2)
  have hnot := D.projection_not_mem_polynomialQuasiLocal hX hN p hp hα hαβ
    (Filter.eventually_ge_atTop n₀ |>.mono fun n hn => hdata n hn)
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨exponentialQuasiLocal_subset_polynomialQuasiLocal hα.le,
      fun h => hnot (exponentialQuasiLocal_subset_polynomialQuasiLocal (hα.trans hαβ).le (h hmem))⟩
  · exact ⟨polynomialQuasiLocal_antitone hα.le hαβ.le, fun h => hnot (h hmem)⟩
  · exact ⟨polynomialQuasiLocal_subset_quasiLocal (hα.trans hαβ),
      fun h => hnot (h (polynomialQuasiLocal_subset_quasiLocal hα hmem))⟩

end DynamicalCStarAlgebras
