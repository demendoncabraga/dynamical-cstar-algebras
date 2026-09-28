import DynamicalCStarAlgebras.FiniteBufferWitnesses

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

/-- Uniform local finiteness as in the introduction: each positive radius has a
uniform finite bound on ball cardinalities. Closed balls give the same condition. -/
def UniformlyLocallyFinite (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ R : ℝ, 0 < R → ∃ N : ℕ, ∀ x : X,
    (Metric.closedBall x R).Finite ∧ (Metric.closedBall x R).ncard ≤ N

theorem UniformlyLocallyFinite.finite_closedBall {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) (x : X) (R : ℝ) : (Metric.closedBall x R).Finite := by
  obtain ⟨N, hN⟩ := hX (max R 0 + 1) (by positivity)
  exact (hN x).1.subset (Metric.closedBall_subset_closedBall
    ((le_max_left R 0).trans (le_add_of_nonneg_right zero_le_one)))

/-- A recursive selection principle keeping all previously imposed pair constraints. -/
theorem exists_sequence_previous_constraints {Y : Type*} (P : ℕ → Y → Prop)
    (Q : ℕ → ℕ → Y → Y → Prop)
    (hstep : ∀ n, ∀ f : Fin n → Y, ∃ y, P n y ∧ ∀ i : Fin n, Q i n (f i) y) :
    ∃ g : ℕ → Y, (∀ n, P n (g n)) ∧ ∀ i n, i < n → Q i n (g i) (g n) := by
  let g : ℕ → Y := Nat.strongRec fun n f => (hstep n (fun i => f i i.isLt)).choose
  have he (n : ℕ) : g n = (hstep n (fun i : Fin n => g i)).choose := by
    exact Nat.strongRec_eq _ n
  refine ⟨g, fun n => ?_, fun i n hin => ?_⟩
  · rw [he n]
    exact (hstep n (fun i : Fin n => g i)).choose_spec.1
  · rw [he n]
    exact (hstep n (fun i : Fin n => g i)).choose_spec.2 ⟨i, hin⟩

/-- Successive exclusion of finite neighborhoods produces the separated finite blocks
in the non-quasi-local detection proof. -/
theorem nonQuasiLocal_separated_blocks {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) (a : Operator X)
    (ha : ¬ IsQuasiLocal (CoarseStructure.ofPseudoMetric X) a) :
    ∃ (ε : ℝ) (A B : ℕ → Set X), 0 < ε ∧
      (∀ n, (A n).Finite ∧ (B n).Finite) ∧
      (∀ n, ε ≤ ‖coordinateProjection (A n) * a * coordinateProjection (B n)‖) ∧
      (∀ n, ∀ x ∈ A n, ∀ y ∈ B n, (n : ℝ) + 1 ≤ dist x y) ∧
      ∀ n m, n ≠ m → ∀ x ∈ A n ∪ B n, ∀ y ∈ A m ∪ B m,
        (n : ℝ) + m + 2 ≤ dist x y := by
  obtain ⟨ε, hε, hw⟩ := nonQuasiLocal_finite_buffer_witnesses a ha
  let Y := {p : Set X × Set X // p.1.Finite ∧ p.2.Finite}
  let P : ℕ → Y → Prop := fun n p =>
    (∀ x ∈ p.val.1, ∀ y ∈ p.val.2, (n : ℝ) + 1 ≤ dist x y) ∧
      ε ≤ ‖coordinateProjection p.val.1 * a * coordinateProjection p.val.2‖
  let Q : ℕ → ℕ → Y → Y → Prop := fun i n p q =>
    ∀ x ∈ p.val.1 ∪ p.val.2, ∀ y ∈ q.val.1 ∪ q.val.2,
      (i : ℝ) + n + 2 ≤ dist x y
  have hstep : ∀ n, ∀ f : Fin n → Y, ∃ p, P n p ∧ ∀ i : Fin n, Q i n (f i) p := by
    intro n f
    let F : Set X := ⋃ i : Fin n, ⋃ x ∈ (f i).val.1 ∪ (f i).val.2,
      Metric.closedBall x ((i : ℕ) + (n : ℝ) + 2)
    have hF : F.Finite := Set.finite_iUnion fun i =>
      ((f i).property.1.union (f i).property.2).biUnion fun x _ => hX.finite_closedBall x _
    obtain ⟨A, B, hA, hB, hAF, hBF, hAB, hab⟩ := hw ((n : ℝ) + 1) F hF
    refine ⟨⟨(A, B), hA, hB⟩, ⟨hAB, hab.le⟩, ?_⟩
    intro i x hx y hy
    have hyF : y ∉ F := hy.elim (fun hy => hAF hy) (fun hy => hBF hy)
    apply le_of_not_gt
    intro hdist
    exact hyF (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion₂.mpr
      ⟨x, hx, by simpa only [Metric.mem_closedBall, dist_comm] using hdist.le⟩⟩)
  obtain ⟨g, hg, hpair⟩ := exists_sequence_previous_constraints P Q hstep
  refine ⟨ε, fun n => (g n).val.1, fun n => (g n).val.2, hε,
    fun n => (g n).property, fun n => (hg n).2, fun n => (hg n).1, ?_⟩
  intro n m hnm x hx y hy
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact hpair n m hlt x hx y hy
  · simpa only [add_comm (m : ℝ) (n : ℝ), dist_comm] using hpair m n hgt y hy x hx

end DynamicalCStarAlgebras
