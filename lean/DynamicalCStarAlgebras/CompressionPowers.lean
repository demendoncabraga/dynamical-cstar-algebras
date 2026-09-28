import DynamicalCStarAlgebras.PolynomialDecay

noncomputable section

namespace DynamicalCStarAlgebras

universe u

theorem coordinateProjection_apply_norm_le {X : Type u} (A : Set X) (v : HilbertSpace X) :
    ‖coordinateProjection A v‖ ≤ ‖v‖ :=
  ((coordinateProjection A).le_opNorm v).trans
    (mul_le_of_le_one_left (norm_nonneg v) (coordinateProjection_norm_le A))

theorem coordinateProjection_mul_of_subset {X : Type u} {A B : Set X} (hAB : A ⊆ B) :
    coordinateProjection A * coordinateProjection B = coordinateProjection A := by
  refine ContinuousLinearMap.ext fun v => lp.ext (funext fun x => ?_)
  change coordinateProjection A (coordinateProjection B v) x = coordinateProjection A v x
  by_cases hx : x ∈ A
  · rw [coordinateProjection_apply_of_mem A _ hx, coordinateProjection_apply_of_mem A _ hx,
      coordinateProjection_apply_of_mem B _ (hAB hx)]
  · rw [coordinateProjection_apply_of_not_mem A _ hx, coordinateProjection_apply_of_not_mem A _ hx]

theorem delta_norm {X : Type u} (x : X) : ‖delta x‖ = 1 := by
  classical
  simpa only [delta, norm_one] using lp.norm_single (E := fun _ : X => ℂ)
    (by norm_num : (0 : ENNReal) < 2) x (1 : ℂ)

/-- Iterated application of a, localized to the ball of radius n*r after step n. -/
def ballPower {X : Type u} [PseudoMetricSpace X] (a : Operator X) (x : X) (r : ℝ) :
    ℕ → HilbertSpace X
  | 0 => delta x
  | n + 1 => coordinateProjection (Metric.closedBall x ((n + 1 : ℕ) * r))
      (a (ballPower a x r n))

theorem ballPower_supported {X : Type u} [PseudoMetricSpace X]
    (a : Operator X) (x : X) (r : ℝ) (n : ℕ) :
    coordinateProjection (Metric.closedBall x (n * r)) (ballPower a x r n) = ballPower a x r n := by
  cases n with
  | zero => simpa only [ballPower, Nat.cast_zero, zero_mul] using
      coordinateProjection_delta_of_mem (Metric.mem_closedBall_self (le_refl (0 : ℝ)))
  | succ n =>
    exact congrArg (fun T : Operator X => T (a (ballPower a x r n)))
      (coordinateProjection_mul_of_subset (A := Metric.closedBall x ((n + 1 : ℕ) * r)) Set.Subset.rfl)

theorem ballPower_norm_le {X : Type u} [PseudoMetricSpace X]
    (a : Operator X) (x : X) (r : ℝ) (n : ℕ) : ‖ballPower a x r n‖ ≤ ‖a‖ ^ n := by
  induction n with
  | zero => simp only [ballPower, delta_norm, pow_zero, le_refl]
  | succ n ih =>
    simpa only [ballPower, pow_succ'] using! (coordinateProjection_apply_norm_le _ _).trans
      ((a.le_opNorm _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg a)))

theorem coordinateProjection_eq_self_of_subset {X : Type u} {A B : Set X}
    (hAB : A ⊆ B) {v : HilbertSpace X} (hv : coordinateProjection A v = v) :
    coordinateProjection B v = v :=
  (coordinateProjection_eq_self_iff B v).mpr fun x hx =>
    (coordinateProjection_eq_self_iff A v).mp hv x (fun hxA => hx (hAB hxA))

theorem projected_step_norm_le {X : Type u} (a : Operator X) {S T : Set X}
    (hST : S ⊆ T) (v : HilbertSpace X) (hv : coordinateProjection T v = v) :
    ‖coordinateProjection S (a v)‖ ≤ ‖coordinateProjection T * a * coordinateProjection T‖ * ‖v‖ := by
  have he : coordinateProjection S (a v) =
      coordinateProjection S ((coordinateProjection T * a * coordinateProjection T) v) := by
    change coordinateProjection S (a v) = coordinateProjection S (coordinateProjection T (a (coordinateProjection T v)))
    rw [hv]
    exact congrArg (fun L : Operator X => L (a v)) (coordinateProjection_mul_of_subset hST).symm
  exact he ▸ (coordinateProjection_apply_norm_le S _).trans
    ((coordinateProjection T * a * coordinateProjection T).le_opNorm v)

theorem closedBall_nat_mul_mono {X : Type u} [PseudoMetricSpace X] (x : X)
    {r : ℝ} (hr : 0 ≤ r) {n m : ℕ} (hnm : n ≤ m) :
    Metric.closedBall x (n * r) ⊆ Metric.closedBall x (m * r) :=
  fun _ hy => (Metric.mem_closedBall.mp hy).trans
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnm) hr)

theorem ballPower_compression_norm_le {X : Type u} [PseudoMetricSpace X]
    (a : Operator X) (x : X) {r : ℝ} (hr : 0 ≤ r) (m : ℕ) :
    ∀ n ≤ m, ‖ballPower a x r n‖ ≤
      ‖coordinateProjection (Metric.closedBall x (m * r)) * a *
        coordinateProjection (Metric.closedBall x (m * r))‖ ^ n := by
  intro n
  induction n with
  | zero => intro _; simp only [ballPower, delta_norm, pow_zero, le_refl]
  | succ n ih =>
    intro hn
    have hb := projected_step_norm_le a (closedBall_nat_mul_mono x hr hn) (ballPower a x r n)
      (coordinateProjection_eq_self_of_subset
        (closedBall_nat_mul_mono x hr (Nat.le_of_succ_le hn)) (ballPower_supported a x r n))
    simpa only [ballPower, pow_succ'] using! hb.trans
      (mul_le_mul_of_nonneg_left (ih (Nat.le_of_succ_le hn)) (norm_nonneg _))

theorem sub_coordinateProjection {X : Type u} (A : Set X) (v : HilbertSpace X) :
    v - coordinateProjection A v = coordinateProjection Aᶜ v := by
  have he : coordinateProjection A v + coordinateProjection Aᶜ v = v :=
    congrArg (fun L : Operator X => L v) (coordinateProjection_add_compl A)
  exact sub_eq_iff_eq_add.mpr (he.symm.trans (add_comm _ _))

theorem ballPower_step_error {X : Type u} [PseudoMetricSpace X]
    (a : Operator X) (x : X) (r : ℝ) (n : ℕ) :
    ‖a (ballPower a x r n) - ballPower a x r (n + 1)‖ ≤ quasiLocalModulus a r * ‖a‖ ^ n := by
  have hsep : ∀ z ∈ (Metric.closedBall x ((n + 1 : ℕ) * r))ᶜ,
      ∀ y ∈ Metric.closedBall x (n * r), r ≤ dist z y := by
    intro z hz y hy
    have hz' : (n + 1 : ℕ) * r < dist z x := lt_of_not_ge hz
    simp only [Nat.cast_add, Nat.cast_one] at hz'
    linarith [Metric.mem_closedBall.mp hy, dist_triangle z y x]
  rw [ballPower, sub_coordinateProjection]
  have hb := (quasiLocalModulus_le_iff a r _).mp le_rfl _ _ hsep
  have hv := (coordinateProjection (Metric.closedBall x ((n + 1 : ℕ) * r))ᶜ * a *
    coordinateProjection (Metric.closedBall x (n * r))).le_opNorm (ballPower a x r n)
  simpa only [mul_apply_eq_comp, ballPower_supported] using! hv.trans
    (mul_le_mul hb (ballPower_norm_le a x r n) (norm_nonneg _) (quasiLocalModulus_nonneg a r))

theorem ballPower_error_le {X : Type u} [PseudoMetricSpace X]
    (a : Operator X) (x : X) (r : ℝ) (n : ℕ) :
    ‖(a ^ n) (delta x) - ballPower a x r n‖ ≤
      (n : ℝ) * ‖a‖ ^ (n - 1) * quasiLocalModulus a r := by
  induction n with
  | zero => simp [ballPower]
  | succ n ih =>
    have hl : ‖(a ^ (n + 1)) (delta x) - a (ballPower a x r n)‖ ≤
        ‖a‖ * ‖(a ^ n) (delta x) - ballPower a x r n‖ := by
      simpa only [pow_succ', mul_apply_eq_comp, map_sub] using!
        a.le_opNorm ((a ^ n) (delta x) - ballPower a x r n)
    have hp := (norm_sub_le_norm_sub_add_norm_sub ((a ^ (n + 1)) (delta x))
      (a (ballPower a x r n)) (ballPower a x r (n + 1))).trans
      (add_le_add (hl.trans (mul_le_mul_of_nonneg_left ih (norm_nonneg a)))
        (ballPower_step_error a x r n))
    refine hp.trans_eq ?_
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ']
      ring

/-- Lemma compression: powers are controlled by a ball compression and the quasi-locality modulus. -/
theorem norm_pow_delta_le_compression {X : Type u} [PseudoMetricSpace X]
    (a : Operator X) (x : X) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    ‖(a ^ m) (delta x)‖ ≤
      ‖coordinateProjection (Metric.closedBall x (m * r)) * a *
        coordinateProjection (Metric.closedBall x (m * r))‖ ^ m +
      (m : ℝ) * ‖a‖ ^ (m - 1) * quasiLocalModulus a r :=
  (norm_le_norm_add_norm_sub (ballPower a x r m) ((a ^ m) (delta x))).trans
    (add_le_add (ballPower_compression_norm_le a x hr.le m m le_rfl)
      ((norm_sub_rev _ _).trans_le (ballPower_error_le a x r m)))

end DynamicalCStarAlgebras
