import DynamicalCStarAlgebras.PropertyAKernels
import DynamicalCStarAlgebras.SeparatedBlockSelection

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

lemma FiniteProbabilityKernel.tsum_row {X : Type*} (μ : FiniteProbabilityKernel X) (x : X) :
    ∑' z, μ.row x z = 1 := by
  rw [tsum_eq_sum (s := (μ.row x).support) (fun _ hz => Finsupp.notMem_support_iff.mp hz)]
  exact μ.sum_one x

lemma FiniteProbabilityKernel.variation_eq_tsum {X : Type*} (μ : FiniteProbabilityKernel X)
    (x y : X) : μ.variation x y = ∑' z, |μ.row x z - μ.row y z| := by
  symm
  apply tsum_eq_sum (s := (μ.row x - μ.row y).support)
  intro z hz
  have he := Finsupp.notMem_support_iff.mp hz
  change μ.row x z - μ.row y z = 0 at he
  rw [he, abs_zero]

/-- On a ULF space the finite-coordinate definition is exactly the usual
probability-measure definition: nonnegative l1 rows of mass one, uniformly bounded
supports, and arbitrarily small l1 variation on bounded-distance pairs. -/
theorem hasPropertyA_iff_probabilityRows {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) : HasPropertyA X ↔
    ∀ δ > 0, ∀ R > 0, ∃ S > 0, ∃ μ : X → X → ℝ,
      (∀ x z, 0 ≤ μ x z) ∧ (∀ x, ∑' z, μ x z = 1) ∧
      (∀ x z, μ x z ≠ 0 → dist x z ≤ S) ∧
      (∀ x y, dist x y ≤ R → ∑' z, |μ x z - μ y z| < δ) := by
  constructor
  · intro h δ hδ R hR
    obtain ⟨S, hS, μ, hsupport, hvar⟩ := h δ hδ R hR
    exact ⟨S, hS, fun x z => μ.row x z, μ.nonneg, μ.tsum_row, hsupport,
      fun x y hxy => (μ.variation_eq_tsum x y) ▸ hvar x y hxy⟩
  · intro h δ hδ R hR
    obtain ⟨S, hS, μ, hμ0, hμ1, hsupport, hvar⟩ := h δ hδ R hR
    have hf (x : X) : (Function.support (μ x)).Finite :=
      (hX.finite_closedBall x S).subset fun z hz => by
        rw [Metric.mem_closedBall, dist_comm]
        exact hsupport x z hz
    let ν : FiniteProbabilityKernel X :=
      { row := fun x => Finsupp.ofSupportFinite (μ x) (hf x)
        nonneg := hμ0
        sum_one := fun x => by
          rw [← hμ1 x]
          symm
          apply tsum_eq_sum
          intro z hz
          exact Finsupp.notMem_support_iff.mp hz }
    refine ⟨S, hS, ν, hsupport, ?_⟩
    intro x y hxy
    rw [ν.variation_eq_tsum]
    exact hvar x y hxy

end DynamicalCStarAlgebras
