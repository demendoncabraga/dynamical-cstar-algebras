import DynamicalCStarAlgebras.ShellApproximation

noncomputable section

namespace DynamicalCStarAlgebras

/-- Definition Defi.Exp.Growth: uniform exponential cardinal bounds on closed integer balls. -/
def AtMostExponentialGrowth (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∃ L : ℝ, 1 < L ∧ ∀ (m : ℕ), 0 < m → ∀ x : X,
    (Metric.closedBall x m).Finite ∧ ((Metric.closedBall x m).ncard : ℝ) ≤ L ^ m

/-- The shell bound obtained by multiplying a cardinal bound and a coefficient bound. -/
theorem finite_shell_sum_bound {X : Type*} (s : Finset X) (d f : X → ℝ)
    {m : ℕ} {C c V : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hcard : (s.card : ℝ) ≤ V)
    (hs : ∀ x ∈ s, (m : ℝ) ≤ d x)
    (hf : ∀ x ∈ s, 0 ≤ f x ∧ Real.exp (c * d x) * f x ≤ C) :
    ∑ x ∈ s, f x ≤ V * (C * Real.exp (-c * m)) := by
  have hpoint : ∀ x ∈ s, f x ≤ C * Real.exp (-c * m) := by
    intro x hx
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.exp_pos _)).mpr ((mul_comm _ _).trans_le
      ((mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (hs x hx) hc)) (hf x hx).1).trans (hf x hx).2))
  exact (Finset.sum_le_sum hpoint).trans ((by simp only [Finset.sum_const, nsmul_eq_mul] :
    (∑ _x ∈ s, C * Real.exp (-c * m)) = s.card * (C * Real.exp (-c * m))).trans_le
      (mul_le_mul_of_nonneg_right hcard (mul_nonneg hC (Real.exp_pos _).le)))

/-- Exponential growth times a faster exponential decay is summable. -/
theorem summable_volume_decay {L C : ℝ} (hL : 0 < L) :
    Summable (fun m : ℕ => L ^ (m + 1) * (C * Real.exp (-(Real.log L + 1) * m))) := by
  have he : ∀ m : ℕ, L ^ (m + 1) * (C * Real.exp (-(Real.log L + 1) * m)) =
      (L * C) * Real.exp (-1) ^ m := by
    intro m
    rw [pow_succ, ← Real.exp_nat_mul, ← Real.exp_log hL]
    simp only [← Real.exp_nat_mul, Real.log_exp]
    have hp : Real.exp ((m : ℝ) * Real.log L) * Real.exp (-(Real.log L + 1) * m) =
        Real.exp ((m : ℝ) * -1) :=
      (Real.exp_add _ _).symm.trans (congrArg Real.exp (by ring))
    linear_combination (Real.exp (Real.log L) * C) * hp
  exact ((summable_geometric_of_lt_one (Real.exp_pos (-1)).le
    (Real.exp_lt_one_iff.mpr (by norm_num))).mul_left (L * C)).congr fun m => (he m).symm

/-- The reverse containment in the exponential-growth assertion of Theorem B. -/
theorem entire_mem_uniformRoe_of_exponentialGrowth {X : Type*} [PseudoMetricSpace X]
    (hX : AtMostExponentialGrowth X) (a : Operator X)
    (ha : ∀ h : X → ℝ, LipschitzWith 1 h → ∃ F, IsEntireExtension h a F) :
    a ∈ uniformRoe (CoarseStructure.ofPseudoMetric X) := by
  obtain ⟨L, hL, hballs⟩ := hX
  have hball : ∀ (m : ℕ), 0 < m → ∀ (x : X) (s : Finset X),
      (∀ y ∈ s, dist x y ≤ m) → (s.card : ℝ) ≤ L ^ m := by
    intro m hm x s hs
    exact (Nat.cast_le.mpr (show s.card ≤ (Metric.closedBall x m).ncard from by
      simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard
        (show (s : Set X) ⊆ Metric.closedBall x m from fun y hy =>
          (dist_comm y x).trans_le (hs y hy)) (hballs m hm x).1)).trans (hballs m hm x).2
  obtain ⟨C, hC, hdecay⟩ := entire_coefficient_all_rates a ha
    (show 0 < Real.log L + 1 by linarith [Real.log_pos hL])
  refine uniformRoe_of_summable_shell_bounds a
    (summable_volume_decay (C := C) (zero_lt_one.trans hL)) ?_ ?_
  · exact fun x m s hs => finite_shell_sum_bound s (dist x) (fun y => ‖matrixEntry a x y‖)
      (by linarith [Real.log_pos hL]) hC
      (hball (m + 1) (Nat.succ_pos m) x s
        (fun y hy => by simpa only [Nat.cast_add, Nat.cast_one] using (hs y hy).2.le))
      (fun y hy => (hs y hy).1) (fun y _ => ⟨norm_nonneg _, hdecay x y⟩)
  · exact fun y m s hs => finite_shell_sum_bound s (fun x => dist x y)
      (fun x => ‖matrixEntry a x y‖) (by linarith [Real.log_pos hL]) hC
      (hball (m + 1) (Nat.succ_pos m) y s
        (fun x hx => by simpa only [Nat.cast_add, Nat.cast_one, dist_comm] using (hs x hx).2.le))
      (fun x hx => (hs x hx).1) (fun x _ => ⟨norm_nonneg _, hdecay x y⟩)

/-- Definition Def.AP.entire.algebra: closure of entire points common to all coarse real maps. -/
def entireAnalyticPoints {X : Type*} (C : CoarseStructure X) : Set (Operator X) :=
  closure {a | ∀ h : X → ℝ, IsCoarseReal C h → ∃ F, IsEntireExtension h a F}

/-- Exponential-type analyticity implies entire analyticity before and after taking closure. -/
theorem exponentialAnalyticPoints_subset_entireAnalyticPoints {X : Type*}
    (C : CoarseStructure X) : exponentialAnalyticPoints C ⊆ entireAnalyticPoints C :=
  closure_mono fun _ ha h hh => (ha h hh).elim fun F hF => ⟨F, hF.1⟩

/-- Theorem thm:roeentire.Exp.Growth, the final equality in Theorem B. -/
theorem uniformRoe_eq_entireAnalyticPoints_of_exponentialGrowth
    {X : Type*} [PseudoMetricSpace X] (hX : AtMostExponentialGrowth X) :
    uniformRoe (CoarseStructure.ofPseudoMetric X) =
      entireAnalyticPoints (CoarseStructure.ofPseudoMetric X) :=
  Set.Subset.antisymm
    ((uniformRoe_subset_exponentialAnalyticPoints _).trans
      (exponentialAnalyticPoints_subset_entireAnalyticPoints _))
    (closure_minimal (fun a ha => entire_mem_uniformRoe_of_exponentialGrowth hX a
      (fun h hh => ha h (lipschitz_isCoarseReal hh))) isClosed_closure)

end DynamicalCStarAlgebras
