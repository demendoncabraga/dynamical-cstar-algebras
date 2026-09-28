import DynamicalCStarAlgebras.LipschitzDetection

noncomputable section

namespace DynamicalCStarAlgebras

open Filter

/-- Infinite propagation supplies nonzero coefficients at diverging distances. -/
theorem infinitePropagation_pairs {X : Type*} [PseudoMetricSpace X] {a : Operator X}
    (ha : ¬HasFinitePropagation a) :
    ∃ x y : ℕ → X, Tendsto (fun n => dist (x n) (y n)) atTop atTop ∧
      ∀ n, matrixEntry a (x n) (y n) ≠ 0 := by
  have hp : ∀ n : ℕ, ∃ x y : X, (n : ℝ) + 1 < dist x y ∧ matrixEntry a x y ≠ 0 := by
    intro n
    simpa only [not_forall, exists_prop] using
      (show ¬∀ x y, (n : ℝ) + 1 < dist x y → matrixEntry a x y = 0 from
        fun h => ha ⟨(n : ℝ) + 1, by positivity, h⟩)
  choose x y hd he using hp
  exact ⟨x, y, tendsto_atTop_mono (fun n => by linarith [hd n])
    (tendsto_natCast_atTop_atTop (R := ℝ)), he⟩

/-- Corollary cor:detect, including arbitrary pseudometric spaces. -/
theorem infinitePropagation_lipschitz_detect {X : Type*} [PseudoMetricSpace X]
    {a : Operator X} (ha : ¬HasFinitePropagation a) :
    ∃ h : X → ℝ, LipschitzWith 1 h ∧
      ¬@HasFinitePropagation X (realPullbackPseudoMetric h) a := by
  obtain ⟨x, y, hd, he⟩ := infinitePropagation_pairs ha
  obtain ⟨n, hn, h, hh, hb⟩ := lipschitz_detect x y hd
  refine ⟨h, hh, fun ⟨R, _, hR⟩ => ?_⟩
  obtain ⟨i, hi⟩ := ((hd.comp hn.tendsto_atTop).eventually_gt_atTop (9 * R)).exists
  change 9 * R < dist (x (n i)) (y (n i)) at hi
  exact he (n i) (hR _ _ (by
    simpa only [realPullbackPseudoMetric_dist] using
      (show R < |h (x (n i)) - h (y (n i))| by linarith [hb i])))

/-- Lipschitz real maps are coarse for the metric coarse structure. -/
theorem lipschitz_isCoarseReal {X : Type*} [PseudoMetricSpace X] {h : X → ℝ}
    {K : NNReal} (hh : LipschitzWith K h) :
    IsCoarseReal (CoarseStructure.ofPseudoMetric X) h :=
  fun _ ⟨R, hR⟩ => ⟨K * R, fun p hp => (hh.dist_le_mul p.1 p.2).trans
    (mul_le_mul_of_nonneg_left (hR p hp) K.coe_nonneg)⟩

/-- The finite-propagation characterization in Theorem thm:roeentire. -/
theorem finitePropagation_iff_coarse_entireExponential {X : Type*} [PseudoMetricSpace X]
    (a : Operator X) : HasFinitePropagation a ↔
      ∀ h : X → ℝ, IsCoarseReal (CoarseStructure.ofPseudoMetric X) h →
        IsEntireExponentialType h a :=
  ⟨fun ha _ hh => ((controlled_iff_finitePropagation a).mpr ha).isEntireExponentialType hh,
    fun ha => Classical.byContradiction fun hn =>
      (infinitePropagation_lipschitz_detect hn).elim fun h ⟨hh, hbad⟩ =>
        hbad (ha h (lipschitz_isCoarseReal hh)).hasFinitePropagation⟩

/-- Theorem thm:roeentire and the second equality in Theorem B. -/
theorem uniformRoe_eq_exponentialAnalyticPoints {X : Type*} [PseudoMetricSpace X] :
    uniformRoe (CoarseStructure.ofPseudoMetric X) =
      exponentialAnalyticPoints (CoarseStructure.ofPseudoMetric X) := by
  simp only [uniformRoe_metric_eq, exponentialAnalyticPoints,
    finitePropagation_iff_coarse_entireExponential]

end DynamicalCStarAlgebras
