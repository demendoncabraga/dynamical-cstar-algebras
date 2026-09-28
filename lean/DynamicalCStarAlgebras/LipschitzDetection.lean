import DynamicalCStarAlgebras.RoeAnalyticInclusion

noncomputable section

namespace DynamicalCStarAlgebras

open Filter

/-- Select an increasing sequence satisfying every earlier eventual constraint. -/
theorem subsequence_pair_constraints {P : ℕ → ℕ → Prop}
    (hP : ∀ i, ∀ᶠ j in atTop, P i j) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ i j, i < j → P (n i) (n j) := by
  have hnext : ∀ i, ∃ j, i < j ∧ ∀ k ≤ i, P k j := by
    intro i
    exact ((eventually_gt_atTop i).and
      ((eventually_all_finset (Finset.range (i + 1))).mpr
        (fun k _ => hP k))).exists.imp fun j hj =>
          ⟨hj.1, fun k hk => hj.2 k (Finset.mem_range.mpr (by omega))⟩
  choose f hf hpf using hnext
  have hn : StrictMono (fun n => f^[n] 0) :=
    strictMono_nat_of_lt_succ fun n =>
      (Function.iterate_succ_apply' f n 0).symm ▸ hf (f^[n] 0)
  exact ⟨_, hn, fun i j hij =>
    (show j = (j - 1) + 1 by omega) ▸
      ((Function.iterate_succ_apply' f (j - 1) 0).symm ▸
        hpf (f^[j - 1] 0) (f^[i] 0) (hn.monotone (by omega)))⟩

/-- Distance to the second endpoints detects uniformly separated pairs. -/
theorem separated_pairs_detect {X : Type*} [PseudoMetricSpace X] (x y : ℕ → X)
    (r : ℕ → ℝ) (hsep : ∀ i j, r i ≤ dist (x i) (y j)) :
    ∃ h : X → ℝ, LipschitzWith 1 h ∧ ∀ i, r i ≤ |h (x i) - h (y i)| := by
  refine ⟨fun z => Metric.infDist z (Set.range y), Metric.lipschitz_infDist_pt _, ?_⟩
  exact fun i => by
    simpa only [Metric.infDist_zero_of_mem (Set.mem_range_self i), sub_zero,
      abs_of_nonneg Metric.infDist_nonneg] using
      (Metric.le_infDist (Set.range_nonempty y)).mpr
        (fun _ ⟨j, hj⟩ => hj ▸ hsep i j)

/-- Orient a pair with its first endpoint at least half its length from a basepoint. -/
theorem orient_pair {X : Type*} [PseudoMetricSpace X] (z x y : X) :
    ∃ p q, ((p = x ∧ q = y) ∨ (p = y ∧ q = x)) ∧ dist x y / 2 ≤ dist z p := by
  by_cases h : dist x y / 2 ≤ dist z x
  · exact ⟨x, y, Or.inl ⟨rfl, rfl⟩, h⟩
  · exact ⟨y, x, Or.inr ⟨rfl, rfl⟩, by linarith [dist_triangle_left x y z]⟩

/-- Escaping to infinity is independent of the basepoint. -/
theorem tendsto_dist_atTop_basepoint {X : Type*} [PseudoMetricSpace X] {x : ℕ → X}
    {z : X} (hx : Tendsto (fun n => dist z (x n)) atTop atTop) (w : X) :
    Tendsto (fun n => dist w (x n)) atTop atTop :=
  tendsto_atTop.mpr fun R => (hx.eventually_ge_atTop (R + dist z w)).mono
    fun n hn => by linarith [dist_triangle z w (x n)]

/-- Detect pairs whose two endpoints escape every bounded set. -/
theorem escaping_pairs_detect {X : Type*} [PseudoMetricSpace X] (x y : ℕ → X) (z : X)
    (hx : Tendsto (fun n => dist z (x n)) atTop atTop)
    (hy : Tendsto (fun n => dist z (y n)) atTop atTop)
    (hd : Tendsto (fun n => dist (x n) (y n)) atTop atTop) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ ∃ h : X → ℝ, LipschitzWith 1 h ∧
      ∀ i, dist (x (n i)) (y (n i)) / 9 ≤ |h (x (n i)) - h (y (n i))| := by
  choose p q hpq hp using fun n => orient_pair z (x n) (y n)
  have hq : ∀ w R, ∀ᶠ j in atTop, R ≤ dist w (q j) := fun w R =>
    ((tendsto_dist_atTop_basepoint hx w).eventually_ge_atTop R |>.and
      ((tendsto_dist_atTop_basepoint hy w).eventually_ge_atTop R)).mono
        fun j hj => (hpq j).elim (fun he => he.2 ▸ hj.2) (fun he => he.2 ▸ hj.1)
  obtain ⟨n, hn, hrel⟩ := subsequence_pair_constraints (P := fun i j =>
    dist (x i) (y i) / 3 ≤ dist (p i) (q j) ∧
      6 * dist z (q i) ≤ dist (x j) (y j))
    (fun i => (hq (p i) (dist (x i) (y i) / 3)).and
      (hd.eventually_ge_atTop (6 * dist z (q i))))
  have hsep : ∀ i j, dist (x (n i)) (y (n i)) / 3 ≤ dist (p (n i)) (q (n j)) := by
    intro i j
    rcases lt_trichotomy i j with hij | hij | hij
    · exact (hrel i j hij).1
    · rcases hpq (n i) with he | he <;>
        simpa only [← hij, he.1, he.2, dist_comm] using
          (show dist (x (n i)) (y (n i)) / 3 ≤ dist (x (n i)) (y (n i)) by
            linarith [dist_nonneg (x := x (n i)) (y := y (n i))])
    · linarith [hp (n i), (hrel j i hij).2, dist_triangle_right z (p (n i)) (q (n j))]
  obtain ⟨h, hh, hbound⟩ := separated_pairs_detect (p ∘ n) (q ∘ n)
    (fun i => dist (x (n i)) (y (n i)) / 3) hsep
  refine ⟨n, hn, h, hh, fun i => ?_⟩
  have heq : |h ((p ∘ n) i) - h ((q ∘ n) i)| = |h (x (n i)) - h (y (n i))| :=
    (hpq (n i)).elim (fun he => by simp only [Function.comp_apply, he.1, he.2])
      (fun he => by simp only [Function.comp_apply, he.1, he.2, abs_sub_comm])
  linarith [hbound i, dist_nonneg (x := x (n i)) (y := y (n i))]

/-- A bounded endpoint subsequence is detected by distance from a fixed point. -/
theorem bounded_endpoint_detect {X : Type*} [PseudoMetricSpace X] (x y : ℕ → X)
    (z : X) {R : ℝ} (hx : ∃ᶠ k in atTop, dist z (x k) ≤ R)
    (hd : Tendsto (fun k => dist (x k) (y k)) atTop atTop) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ ∃ h : X → ℝ, LipschitzWith 1 h ∧
      ∀ i, dist (x (n i)) (y (n i)) / 9 ≤ |h (x (n i)) - h (y (n i))| := by
  obtain ⟨n, hn, hb⟩ := extraction_of_frequently_atTop
    (hx.and_eventually (hd.eventually_ge_atTop (3 * R)))
  exact ⟨n, hn, dist z, LipschitzWith.dist_right z, fun i => by
    linarith [dist_triangle_left (x (n i)) (y (n i)) z, (hb i).1, (hb i).2,
      neg_le_abs (dist z (x (n i)) - dist z (y (n i))),
      dist_nonneg (x := x (n i)) (y := y (n i))]⟩

/-- Lemma lem:detect, proved for arbitrary pseudometric spaces. -/
theorem lipschitz_detect {X : Type*} [PseudoMetricSpace X] (x y : ℕ → X)
    (hd : Tendsto (fun k => dist (x k) (y k)) atTop atTop) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ ∃ h : X → ℝ, LipschitzWith 1 h ∧
      ∀ i, dist (x (n i)) (y (n i)) / 9 ≤ |h (x (n i)) - h (y (n i))| := by
  by_cases hx : ∃ R : ℝ, ∃ᶠ k in atTop, dist (x 0) (x k) ≤ R
  · exact hx.elim fun _ hR => bounded_endpoint_detect x y (x 0) hR hd
  · by_cases hy : ∃ R : ℝ, ∃ᶠ k in atTop, dist (x 0) (y k) ≤ R
    · simpa only [dist_comm, abs_sub_comm] using
        hy.elim (fun _ hR => bounded_endpoint_detect y x (x 0) hR
          (by simpa only [dist_comm] using hd))
    · exact escaping_pairs_detect x y (x 0)
        (tendsto_atTop.mpr fun R => (not_frequently.mp (not_exists.mp hx R)).mono
          fun _ hk => (lt_of_not_ge hk).le)
        (tendsto_atTop.mpr fun R => (not_frequently.mp (not_exists.mp hy R)).mono
          fun _ hk => (lt_of_not_ge hk).le) hd

end DynamicalCStarAlgebras
