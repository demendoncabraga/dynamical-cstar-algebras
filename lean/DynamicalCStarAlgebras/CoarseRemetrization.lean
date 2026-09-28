import DynamicalCStarAlgebras.CoarseEquivalence

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- Add a weighted discrete metric between components, preserving their internal metrics. -/
@[instance_reducible] def partitionWeightedMetric {X : Type*} [MetricSpace X]
    (π : X → ℕ) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) : MetricSpace X where
  dist x y := dist x y + if π x = π y then 0 else w (π x) + w (π y)
  dist_self x := by simp
  dist_comm x y := by simp only [dist_comm, eq_comm (a := π x), add_comm (w (π x))]
  dist_triangle x y z := by
    have hd := dist_triangle x y z
    by_cases hxy : π x = π y <;> by_cases hyz : π y = π z <;> by_cases hxz : π x = π z <;>
      simp_all <;> linarith [hw (π x), hw (π y), hw (π z)]
  eq_of_dist_eq_zero {x y} h := by
    apply dist_eq_zero.mp
    have hnon : 0 ≤ if π x = π y then 0 else w (π x) + w (π y) := by
      split_ifs
      · exact le_rfl
      · exact add_nonneg (hw _) (hw _)
    linarith [dist_nonneg (x := x) (y := y)]

/-- Cumulative weights dominate any prescribed growth rate at the sum of two indices. -/
lemma cumulative_weight_bound (ρ : ℕ → ℝ) (n m : ℕ) :
    ρ (n + m) ≤ (∑ j ∈ Finset.range (2 * n + 1), |ρ j|) +
      ∑ j ∈ Finset.range (2 * m + 1), |ρ j| := by
  have hn : 0 ≤ ∑ j ∈ Finset.range (2 * n + 1), |ρ j| := Finset.sum_nonneg (by intros; positivity)
  have hm : 0 ≤ ∑ j ∈ Finset.range (2 * m + 1), |ρ j| := Finset.sum_nonneg (by intros; positivity)
  rcases le_total n m with h | h
  · have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (2 * m + 1)) => abs_nonneg (ρ j))
      (Finset.mem_range.mpr (show n + m < 2 * m + 1 by omega))
    exact (le_abs_self _).trans (hs.trans (le_add_of_nonneg_left hn))
  · have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (2 * n + 1)) => abs_nonneg (ρ j))
      (Finset.mem_range.mpr (show n + m < 2 * n + 1 by omega))
    exact (le_abs_self _).trans (hs.trans (le_add_of_nonneg_right hm))

/-- `Remark.C.d.u.`: cross-component distances can dominate any prescribed
function of the component indices, without changing internal metrics or coarse type. -/
theorem CoarseDisjointUnion.exists_metric_with_prescribed_separation
    {X : Type*} [m₀ : MetricSpace X] (D : CoarseDisjointUnion X) (ρ : ℕ → ℝ) :
    let π := D.component
    ∃ m : MetricSpace X, ∃ F : @CoarseDisjointUnion X m.toPseudoMetricSpace,
      F.component = π ∧
      (∀ x y, π x = π y → @dist X m.toDist x y = @dist X m₀.toDist x y) ∧
      (∀ x y, π x ≠ π y → ρ (π x + π y) ≤ @dist X m.toDist x y) ∧
      AreBijectivelyCoarselyEquivalent (@CoarseStructure.ofPseudoMetric X m₀.toPseudoMetricSpace)
        (@CoarseStructure.ofPseudoMetric X m.toPseudoMetricSpace) := by
  let π := D.component
  have hfinite := D.finite
  have hseparated := D.separated
  let d := @dist X m₀.toDist
  have hdnon : ∀ x y, 0 ≤ d x y := fun _ _ => dist_nonneg
  let w (n : ℕ) : ℝ := ∑ j ∈ Finset.range (2 * n + 1), |ρ j|
  have hw : ∀ n, 0 ≤ w n := fun n => Finset.sum_nonneg (fun j _ => abs_nonneg (ρ j))
  let m : MetricSpace X := partitionWeightedMetric π w hw
  have hdist (x y : X) : @dist X m.toDist x y =
      d x y + if π x = π y then 0 else w (π x) + w (π y) := rfl
  have hle (x y : X) : d x y ≤ @dist X m.toDist x y := by
    rw [hdist]
    apply le_add_of_nonneg_right
    split_ifs
    · exact le_rfl
    · exact add_nonneg (hw _) (hw _)
  let F : @CoarseDisjointUnion X m.toPseudoMetricSpace := {
    component := π
    finite := hfinite
    separated := fun r => (hseparated r).imp fun N hN x y hxy hsum =>
      (hN x y hxy hsum).trans (hle x y) }
  have hinternal (x y : X) (hxy : π x = π y) :
      @dist X m.toDist x y = d x y := by
    simp only [hdist, hxy, if_true, add_zero]
  refine ⟨m, F, rfl, hinternal, ?_, ?_⟩
  · intro x y hxy
    rw [hdist, if_neg hxy]
    exact (cumulative_weight_bound ρ (π x) (π y)).trans
      (le_add_of_nonneg_left (hdnon x y))
  · exact (@CoarseDisjointUnion.bijectivelyCoarselyEquivalent X X
      m₀.toPseudoMetricSpace m.toPseudoMetricSpace D F (Equiv.refl X)
      (fun _ => rfl) hinternal).1

end DynamicalCStarAlgebras
