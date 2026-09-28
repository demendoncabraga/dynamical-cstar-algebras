import DynamicalCStarAlgebras.GraphBallCounting

noncomputable section
open Filter
open scoped Topology
namespace DynamicalCStarAlgebras

lemma entropy_card_le_sqrt_bound {a N k : ℝ} (hN : 1 ≤ N) (ha : 1 ≤ a)
    (hcard : a ≤ k * Real.sqrt N) :
    a / N * Real.log (Real.exp 1 / (a / N)) ≤ k * Real.log (Real.exp 1 * N) / Real.sqrt N := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hratio : a / N ≤ k / Real.sqrt N := by
    apply (div_le_div_iff₀ hN0 hs).mpr
    have hh := mul_le_mul_of_nonneg_right hcard hs.le
    nlinarith [Real.sq_sqrt hN0.le]
  have hlog : Real.log (Real.exp 1 / (a / N)) ≤ Real.log (Real.exp 1 * N) := by
    apply Real.log_le_log (by positivity)
    rw [div_div_eq_mul_div]
    exact div_le_self (by positivity) ha
  have hlog0 : 0 ≤ Real.log (Real.exp 1 * N) := by
    apply Real.log_nonneg
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith
  calc
    _ ≤ a / N * Real.log (Real.exp 1 * N) := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ k / Real.sqrt N * Real.log (Real.exp 1 * N) := mul_le_mul_of_nonneg_right hratio hlog0
    _ = _ := by ring

lemma projection_compression_norm_sq {X : Type*} (p : Operator X)
    (hp : IsStarProjection p) (A : Set X) :
    ‖coordinateProjection A * p * coordinateProjection A‖ = ‖coordinateProjection A * p‖ ^ 2 := by
  have h := CStarRing.norm_self_mul_star (x := coordinateProjection A * p)
  simpa only [star_mul, hp.isSelfAdjoint.star_eq, coordinateProjection_star, mul_assoc,
    ← mul_assoc p p, hp.isIdempotentElem.eq, pow_two] using h

/-- Claim.ddd.q: the source compression estimate on sets of size at most `k sqrt N`. -/
theorem small_projection_compression_bound {X : Type*} [Fintype X]
    (p : Operator X) (hp : IsStarProjection p) (A : Finset X) (hA : A.Nonempty)
    {C α k : ℝ} (hN : 1 < (Fintype.card X : ℝ))
    (hcard : (A.card : ℝ) ≤ k * Real.sqrt (Fintype.card X))
    (hbound : ‖coordinateProjection (A : Set X) * p‖ ≤ C * Real.sqrt
      (1 / Real.log (Fintype.card X) ^ (2 * α) + (A.card : ℝ) / Fintype.card X *
        Real.log (Real.exp 1 * Fintype.card X / A.card))) :
    ‖coordinateProjection (A : Set X) * p * coordinateProjection (A : Set X)‖ ≤
      C ^ 2 * (1 / Real.log (Fintype.card X) ^ (2 * α) +
        k * Real.log (Real.exp 1 * Fintype.card X) / Real.sqrt (Fintype.card X)) := by
  have ha : (1 : ℝ) ≤ A.card := by exact_mod_cast hA.card_pos
  have ha0 : (0 : ℝ) < A.card := zero_lt_one.trans_le ha
  have hN0 : (0 : ℝ) < Fintype.card X := zero_lt_one.trans hN
  have hsub : (A.card : ℝ) ≤ Fintype.card X := by exact_mod_cast Finset.card_le_univ A
  have hlog : 0 ≤ Real.log (Real.exp 1 * Fintype.card X / A.card) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ ha0).mpr
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith
  have he := entropy_card_le_sqrt_bound hN.le ha hcard
  rw [div_div_eq_mul_div] at he
  have hs := pow_le_pow_left₀ (norm_nonneg _) hbound 2
  rw [mul_pow, Real.sq_sqrt (by positivity)] at hs
  rw [projection_compression_norm_sq p hp]
  exact hs.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl he) (sq_nonneg C))

/-- The majorant in Choiceofn tends to zero for every positive decay exponent. -/
lemma tendsto_small_compression_majorant {α : ℝ} (hα : 0 < α) (C k : ℝ) :
    Tendsto (fun N : ℝ => C ^ 2 * (1 / Real.log N ^ (2 * α) +
      k * Real.log (Real.exp 1 * N) / Real.sqrt N)) atTop (𝓝 0) := by
  have hfirst : Tendsto (fun N : ℝ => 1 / Real.log N ^ (2 * α)) atTop (𝓝 0) :=
    ((tendsto_rpow_atTop (by positivity : 0 < 2 * α)).comp Real.tendsto_log_atTop).const_div_atTop 1
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hone := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_div_atTop 1
  have hsum : Tendsto (fun N : ℝ => Real.log (Real.exp 1 * N) / Real.sqrt N) atTop (𝓝 0) := by
    have hh := hone.add hlog
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
    rw [Real.log_mul (Real.exp_ne_zero _) hN.ne', Real.log_exp, Real.sqrt_eq_rpow, add_div]
  simpa only [zero_add, mul_zero, mul_div_assoc] using (hfirst.add (hsum.const_mul k)).const_mul (C ^ 2)

/-- Equation Choiceofn, with the component threshold depending on the requested error. -/
theorem eventually_small_compression_majorant {N : ℕ → ℝ} (hN : Tendsto N atTop atTop)
    {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (C k : ℝ) :
    ∀ᶠ n in atTop, C ^ 2 * (1 / Real.log (N n) ^ (2 * α) +
      k * Real.log (Real.exp 1 * N n) / Real.sqrt (N n)) ≤ δ := by
  exact ((tendsto_small_compression_majorant hα C k).comp hN).eventually
    (eventually_le_nhds hδ)

end DynamicalCStarAlgebras
