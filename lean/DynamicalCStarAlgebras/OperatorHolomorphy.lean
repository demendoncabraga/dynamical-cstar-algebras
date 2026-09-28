import DynamicalCStarAlgebras.FinitePropagationExtension

noncomputable section

namespace DynamicalCStarAlgebras

universe u

/-- A scalar Schwarz estimate suitable for uniform operator bounds. -/
theorem norm_sub_le_of_bounded_entire {f : ℂ → ℂ} {c z : ℂ} {D : ℝ}
    (hf : Differentiable ℂ f) (hD : ∀ w ∈ Metric.ball c 1, ‖f w‖ ≤ D)
    (hz : z ∈ Metric.ball c 1) : ‖f z - f c‖ ≤ (2 * D) * dist z c := by
  have hm : Set.MapsTo f (Metric.ball c 1) (Metric.closedBall (f c) (2 * D)) :=
    fun w hw => by
      simpa only [Metric.mem_closedBall, dist_eq_norm, two_mul] using
        (norm_sub_le (f w) (f c)).trans (add_le_add (hD w hw) (hD c (Metric.mem_ball_self zero_lt_one)))
  simpa only [div_one, dist_eq_norm] using
    Complex.dist_le_div_mul_dist_of_mapsTo_ball hf.differentiableOn hm hz

/-- Entire finite vector pairings and a uniform ball bound control operator norm differences. -/
theorem norm_sub_operatorFamily_le {X : Type u} {F : ℂ → Operator X} {c z : ℂ} {D : ℝ}
    (hD0 : 0 ≤ D) (hD : ∀ w ∈ Metric.ball c 1, ‖F w‖ ≤ D)
    (hd : ∀ v w : X →₀ ℂ, Differentiable ℂ (fun z => finiteMatrixForm (matrixEntry (F z)) v w))
    (hz : z ∈ Metric.ball c 1) : ‖F z - F c‖ ≤ (2 * D) * dist z c := by
  refine norm_le_of_finiteMatrixForm_bound _ (by positivity) fun v w => ?_
  have hb (u : ℂ) (hu : u ∈ Metric.ball c 1) :
      ‖finiteMatrixForm (matrixEntry (F u)) v w‖ ≤ D * ‖finiteVector v‖ * ‖finiteVector w‖ :=
    (norm_finiteMatrixForm_matrixEntry_le _ _ _).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hD u hu)
        (norm_nonneg _)) (norm_nonneg _))
  simpa only [finiteMatrixForm_matrixEntry, sub_apply, inner_sub_right,
    mul_assoc, mul_comm, mul_left_comm] using norm_sub_le_of_bounded_entire (hd v w) hb hz

/-- Local bounds and entire finite pairings imply operator-norm continuity. -/
theorem continuous_operatorFamily {X : Type u} {F : ℂ → Operator X}
    (hd : ∀ v w : X →₀ ℂ, Differentiable ℂ (fun z => finiteMatrixForm (matrixEntry (F z)) v w))
    (hb : ∀ c : ℂ, ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ Metric.ball c 1, ‖F z‖ ≤ D) :
    Continuous F := by
  refine continuous_iff_continuousAt.mpr fun c => ?_
  obtain ⟨D, hD0, hD⟩ := hb c
  have ht : Filter.Tendsto (fun z : ℂ => (2 * D) * dist z c) (nhds c) (nhds 0) := by
    simpa only [dist_self, mul_zero] using
      (show Continuous (fun z : ℂ => (2 * D) * dist z c) by fun_prop).tendsto c
  exact tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero'
    (Filter.Eventually.of_forall fun z => dist_nonneg (x := F z) (y := F c))
    (Filter.Eventually.mono (Metric.ball_mem_nhds c zero_lt_one) fun z hz => by
      simpa only [dist_eq_norm] using norm_sub_operatorFamily_le hD0 hD hd hz) ht)

theorem matrixEntry_circleIntegral {X : Type u} {F : ℂ → Operator X} {c : ℂ} {R : ℝ}
    (hF : CircleIntegrable F c R) (x y : X) :
    matrixEntry (circleIntegral F c R) x y = circleIntegral (fun z => matrixEntry (F z) x y) c R := by
  simpa only [circleIntegral, map_smul, matrixEntryCLM_apply] using!
    ((matrixEntryCLM x y).intervalIntegral_comp_comm hF.out).symm

theorem matrixEntry_smul {X : Type u} (c : ℂ) (a : Operator X) (x y : X) :
    matrixEntry (c • a) x y = c * matrixEntry a x y :=
  (matrixEntryCLM x y).map_smul c a

/-- Cauchy's formula for a continuous operator family with entire matrix coefficients. -/
theorem operatorFamily_cauchy {X : Type u} {F : ℂ → Operator X} (hF : Continuous F)
    (hd : ∀ x y, Differentiable ℂ (fun z => matrixEntry (F z) x y))
    {c w : ℂ} (hw : w ∈ Metric.ball c 1) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ • circleIntegral (fun z => (z - w)⁻¹ • F z) c 1 = F w := by
  have hi : CircleIntegrable (fun z => (z - w)⁻¹ • F z) c 1 :=
    ContinuousOn.circleIntegrable zero_le_one
      (((continuousOn_id.sub (continuousOn_const : ContinuousOn (fun _ : ℂ => w) (Metric.sphere c 1))).inv₀ (fun z hz => sub_ne_zero.mpr fun he =>
        (ne_of_lt (Metric.mem_ball.mp hw)) (Metric.mem_sphere.mp ((show z = w from he) ▸ hz)))).smul hF.continuousOn)
  refine operator_ext fun x y => ?_
  simpa only [matrixEntry_smul, matrixEntry_circleIntegral hi, smul_eq_mul] using!
    (hd x y).diffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw

/-- Continuous operator-valued functions with entire matrix coefficients are entire. -/
theorem differentiable_operatorFamily {X : Type u} {F : ℂ → Operator X} (hF : Continuous F)
    (hd : ∀ x y, Differentiable ℂ (fun z => matrixEntry (F z) x y)) : Differentiable ℂ F :=
  fun c => (hasFPowerSeriesOn_cauchy_integral (R := (1 : NNReal))
    (ContinuousOn.circleIntegrable zero_le_one hF.continuousOn) zero_lt_one).analyticAt.differentiableAt
      |>.congr_of_eventuallyEq (Filter.Eventually.mono (Metric.ball_mem_nhds c zero_lt_one)
        fun _w hw => (operatorFamily_cauchy hF hd hw).symm)

end DynamicalCStarAlgebras
