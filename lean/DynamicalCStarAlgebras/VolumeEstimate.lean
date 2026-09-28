import DynamicalCStarAlgebras.ExponentialGrowth
import DynamicalCStarAlgebras.SeparatedBlockSelection

noncomputable section

namespace DynamicalCStarAlgebras

/-- The manuscript's volume function `N_X(m)`, with value zero on the empty space. -/
def volumeFunction (X : Type*) [PseudoMetricSpace X] (m : ℕ) : ℕ :=
  sSup (Set.range fun x : X => (Metric.closedBall x m).ncard)

/-- The manuscript's matrix-coefficient tail `η_a(m)`; the empty supremum is zero. -/
def coefficientTail {X : Type*} [PseudoMetricSpace X] (a : Operator X) (m : ℕ) : ℝ :=
  sSup {t | ∃ x y : X, (m : ℝ) ≤ dist x y ∧ t = ‖matrixEntry a x y‖}

lemma volumeFunction_bddAbove {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) (m : ℕ) :
    BddAbove (Set.range fun x : X => (Metric.closedBall x m).ncard) := by
  obtain ⟨N, hN⟩ := hX ((m : ℝ) + 1) (by positivity)
  refine ⟨N, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (Set.ncard_le_ncard (Metric.closedBall_subset_closedBall (by linarith))
    (hN x).1).trans (hN x).2

lemma closedBall_ncard_le_volumeFunction {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) (x : X) (m : ℕ) :
    (Metric.closedBall x m).ncard ≤ volumeFunction X m :=
  le_csSup (volumeFunction_bddAbove hX m) (Set.mem_range_self x)

lemma volumeFunction_le_of_ball_bound {X : Type*} [PseudoMetricSpace X]
    (m : ℕ) {V : ℝ} (hV : 0 ≤ V)
    (hball : ∀ x : X, ((Metric.closedBall x m).ncard : ℝ) ≤ V) :
    (volumeFunction X m : ℝ) ≤ V := by
  refine (show (volumeFunction X m : ℝ) ≤ ⌊V⌋₊ from ?_).trans (Nat.floor_le hV)
  exact_mod_cast (show volumeFunction X m ≤ ⌊V⌋₊ from
    csSup_le' fun _ ⟨x, hx⟩ => hx ▸ (Nat.le_floor_iff hV).mpr (hball x))

/-- The implemented growth predicate agrees with the manuscript's bound on `N_X`. -/
theorem atMostExponentialGrowth_iff_volume_bound {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) :
    AtMostExponentialGrowth X ↔
      ∃ L : ℝ, 1 < L ∧ ∀ m : ℕ, 0 < m → (volumeFunction X m : ℝ) ≤ L ^ m := by
  constructor
  · rintro ⟨L, hL, hb⟩
    exact ⟨L, hL, fun m hm => volumeFunction_le_of_ball_bound m
      (pow_nonneg (by linarith) _) (fun x => (hb m hm x).2)⟩
  · rintro ⟨L, hL, hb⟩
    exact ⟨L, hL, fun m hm x => ⟨hX.finite_closedBall x m,
      (Nat.cast_le.mpr (closedBall_ncard_le_volumeFunction hX x m)).trans (hb m hm)⟩⟩

lemma coefficientTail_nonneg {X : Type*} [PseudoMetricSpace X] (a : Operator X) (m : ℕ) :
    0 ≤ coefficientTail a m :=
  Real.sSup_nonneg fun _ ⟨_, _, _, ht⟩ => ht ▸ norm_nonneg _

lemma norm_matrixEntry_le_coefficientTail {X : Type*} [PseudoMetricSpace X]
    (a : Operator X) {m : ℕ} {x y : X} (hxy : (m : ℝ) ≤ dist x y) :
    ‖matrixEntry a x y‖ ≤ coefficientTail a m := by
  unfold coefficientTail
  refine le_csSup ?_ ⟨x, y, hxy, rfl⟩
  refine ⟨‖a‖, ?_⟩
  rintro _ ⟨x, y, _, rfl⟩
  exact norm_matrixEntry_le a x y

lemma finset_card_le_volumeFunction {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) (x : X) (m : ℕ) (s : Finset X)
    (hs : ∀ y ∈ s, dist x y ≤ m) : s.card ≤ volumeFunction X m := by
  refine (show s.card ≤ (Metric.closedBall x m).ncard from ?_).trans
    (closedBall_ncard_le_volumeFunction hX x m)
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun y hy => (dist_comm y x).trans_le (hs y hy))
    (hX.finite_closedBall x m)

lemma matrixEntry_row_shell_sum_le_volume {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) (a : Operator X) (x : X) (m : ℕ) (s : Finset X)
    (hs : ∀ y ∈ s, (m : ℝ) ≤ dist x y ∧ dist x y < m + 1) :
    ∑ y ∈ s, ‖matrixEntry a x y‖ ≤ volumeFunction X (m + 1) * coefficientTail a m := by
  have hcard : (s.card : ℝ) ≤ volumeFunction X (m + 1) := by
    exact_mod_cast finset_card_le_volumeFunction hX x (m + 1) s
      (fun y hy => by simpa only [Nat.cast_add, Nat.cast_one] using (hs y hy).2.le)
  have hp := Finset.sum_le_sum (fun y hy => norm_matrixEntry_le_coefficientTail a (hs y hy).1)
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    hp.trans (by simpa only [Finset.sum_const, nsmul_eq_mul] using
      mul_le_mul_of_nonneg_right hcard (coefficientTail_nonneg a m))

lemma matrixEntry_col_shell_sum_le_volume {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) (a : Operator X) (y : X) (m : ℕ) (s : Finset X)
    (hs : ∀ x ∈ s, (m : ℝ) ≤ dist x y ∧ dist x y < m + 1) :
    ∑ x ∈ s, ‖matrixEntry a x y‖ ≤ volumeFunction X (m + 1) * coefficientTail a m := by
  have hcard : (s.card : ℝ) ≤ volumeFunction X (m + 1) := by
    exact_mod_cast finset_card_le_volumeFunction hX y (m + 1) s
      (fun x hx => by simpa only [Nat.cast_add, Nat.cast_one, dist_comm] using (hs x hx).2.le)
  have hp := Finset.sum_le_sum (fun x hx => norm_matrixEntry_le_coefficientTail a (hs x hx).1)
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    hp.trans (by simpa only [Finset.sum_const, nsmul_eq_mul] using
      mul_le_mul_of_nonneg_right hcard (coefficientTail_nonneg a m))

/-- A summable shell majorant gives the exact tail bound after shell `k`. -/
lemma finite_tail_shell_tsum_bound {X : Type*} (s : Finset X) (d f : X → ℝ)
    (b : ℕ → ℝ) (hd : ∀ x, 0 ≤ d x) (hb : ∀ m, 0 ≤ b m) (hsum : Summable b)
    (hshell : ∀ (m : ℕ) (t : Finset X),
      (∀ x ∈ t, (m : ℝ) ≤ d x ∧ d x < m + 1) → ∑ x ∈ t, f x ≤ b m)
    (k : ℕ) :
    ∑ x ∈ s, (if (k : ℝ) + 1 < d x then f x else 0) ≤
      ∑' m : Set.Ioi k, b m := by
  classical
  rw [← Finset.sum_filter]
  refine (finite_sum_shell_bound _ d f b (fun x _ => hd x) hshell).trans ?_
  rw [tsum_subtype]
  calc
    _ = ∑ m ∈ (s.filter (fun x => (k : ℝ) + 1 < d x)).image (fun x => ⌊d x⌋₊),
        (Set.Ioi k).indicator b m := by
      apply Finset.sum_congr rfl
      intro m hm
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
      have hkm : k < ⌊d x⌋₊ := by
        have hh := (Finset.mem_filter.mp hx).2
        exact_mod_cast (show (k : ℝ) < ⌊d x⌋₊ by linarith [Nat.lt_floor_add_one (d x)])
      rw [Set.indicator_of_mem (show ⌊d x⌋₊ ∈ Set.Ioi k from hkm)]
    _ ≤ _ := Summable.sum_le_tsum _
      (fun m _ => by simp only [Set.indicator]; split_ifs <;> simp_all)
      (hsum.indicator (Set.Ioi k))

/-- Lemma `lem:volume`, including its stated tail constant and Roe-algebra
conclusion. The Schur estimate in fact gives the same bound with constant one. -/
theorem volume_approximation {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) (a : Operator X)
    (hsum : Summable (fun m => (volumeFunction X (m + 1) : ℝ) * coefficientTail a m)) :
    (∀ k : ℕ, ∃ b : Operator X, HasFinitePropagation b ∧
      ‖a - b‖ ≤ 2 * ∑' m : Set.Ioi k,
        (volumeFunction X (m.1 + 1) : ℝ) * coefficientTail a m.1) ∧
      a ∈ uniformRoe (CoarseStructure.ofPseudoMetric X) := by
  have hb : ∀ m, 0 ≤ (volumeFunction X (m + 1) : ℝ) * coefficientTail a m :=
    fun m => mul_nonneg (Nat.cast_nonneg _) (coefficientTail_nonneg a m)
  constructor
  · intro k
    have ht : 0 ≤ ∑' m : Set.Ioi k,
        (volumeFunction X (m.1 + 1) : ℝ) * coefficientTail a m.1 :=
      tsum_nonneg fun m => hb m.1
    have htail : HasSchurBound (matrixTail a ((k : ℝ) + 1))
        (∑' m : Set.Ioi k, (volumeFunction X (m.1 + 1) : ℝ) * coefficientTail a m.1) := by
      constructor
      · intro x s
        simpa only [matrixTail, apply_ite norm, norm_zero] using
          finite_tail_shell_tsum_bound s (dist x) (fun y => ‖matrixEntry a x y‖)
            (fun m => (volumeFunction X (m + 1) : ℝ) * coefficientTail a m)
            (fun _ => dist_nonneg) hb hsum (matrixEntry_row_shell_sum_le_volume hX a x) k
      · intro y s
        simpa only [matrixTail, apply_ite norm, norm_zero] using
          finite_tail_shell_tsum_bound s (fun x => dist x y) (fun x => ‖matrixEntry a x y‖)
            (fun m => (volumeFunction X (m + 1) : ℝ) * coefficientTail a m)
            (fun _ => dist_nonneg) hb hsum (matrixEntry_col_shell_sum_le_volume hX a y) k
    obtain ⟨b, hbprop, hab⟩ := finitePropagation_approximation_of_schur_tail a
      (by positivity : 0 < (k : ℝ) + 1) ht htail
    exact ⟨b, hbprop, hab.trans (by linarith)⟩
  · exact uniformRoe_of_summable_shell_bounds a hsum
      (matrixEntry_row_shell_sum_le_volume hX a) (matrixEntry_col_shell_sum_le_volume hX a)

end DynamicalCStarAlgebras
