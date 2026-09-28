import DynamicalCStarAlgebras.FourierBox

namespace DynamicalCStarAlgebras

open MeasureTheory Filter
open scoped Topology

universe u

theorem fejerKernel_neg (s t : ℝ) : fejerKernel (-s) t = -fejerKernel s t := by
  simp [fejerKernel, neg_mul, neg_div, Real.sinc_neg]

theorem integrable_fejerKernel_all (s : ℝ) : Integrable (fejerKernel s) := by
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · exact (integrable_fejerKernel (neg_pos.mpr hs)).neg.congr
      (Filter.Eventually.of_forall fun t => by simp [Pi.neg_apply, fejerKernel_neg])
  · exact (integrable_zero ℝ ℝ volume).congr
      (Filter.Eventually.of_forall fun t => by simp [fejerKernel])
  · exact integrable_fejerKernel hs

/-- Fejer averaging, defined also at nonpositive scales by the same integral formula. -/
noncomputable def fejerAverage {X : Type u} (h : X → ℝ) (s : ℝ) (a : Operator X) : Operator X :=
  averagingOperator h (integrable_fejerKernel_all s).ofReal a

/-- Lemma support.ThetaKsa: the propagation is at most the positive scale s. -/
theorem matrixEntry_fejerAverage_eq_zero {X : Type u} (h : X → ℝ) {s : ℝ}
    (hs : 0 < s) (a : Operator X) (x y : X) (hxy : s < |h x - h y|) :
    matrixEntry (fejerAverage h s a) x y = 0 := by
  rw [fejerAverage, matrixEntry_averagingOperator]
  erw [fourierPlus_fejerKernel hs]
  have hz : 1 - |h x - h y| / s ≤ 0 :=
    sub_nonpos.mpr ((le_div_iff₀ hs).mpr (by simpa using hxy.le))
  simp only [max_eq_right hz, Complex.ofReal_zero, zero_mul]

theorem fejerAverage_hasFinitePropagation {X : Type u} (h : X → ℝ) {s : ℝ}
    (hs : 0 < s) (a : Operator X) :
    @HasFinitePropagation X (realPullbackPseudoMetric h) (fejerAverage h s a) :=
  ⟨s, hs, fun x y hxy => matrixEntry_fejerAverage_eq_zero h hs a x y
    ((realPullbackPseudoMetric_dist h x y) ▸ hxy)⟩

theorem fejerKernel_scale (s t : ℝ) : fejerKernel s t = s * fejerKernel 1 (s * t) := by
  simp only [fejerKernel, one_mul]
  ring

theorem fejerAverage_eq_integral {X : Type u} (h : X → ℝ) (s : ℝ)
    (a : Operator X) (ha : a ∈ continuityPoints h) :
    fejerAverage h s a = ∫ t, fejerKernel s t • diagonalFlow h t a := by
  simpa only [Complex.coe_smul] using!
    averagingOperator_eq_integral h (integrable_fejerKernel_all s).ofReal a ha

theorem fejerAverage_eq_scaled_integral {X : Type u} (h : X → ℝ) {s : ℝ}
    (hs : 0 < s) (a : Operator X) (ha : a ∈ continuityPoints h) :
    fejerAverage h s a = ∫ t, fejerKernel 1 t • diagonalFlow h (t / s) a := by
  have hi := Measure.integral_comp_mul_left
    (fun t : ℝ => fejerKernel 1 t • diagonalFlow h (t / s) a) s
  have hj := congrArg (fun b : Operator X => s • b) hi
  simp only [mul_div_cancel_left₀ _ hs.ne', abs_of_pos (inv_pos.mpr hs),
    smul_smul, mul_inv_cancel₀ hs.ne', one_smul] at hj
  simpa only [fejerAverage_eq_integral h s a ha, fejerKernel_scale s, mul_smul,
    integral_smul] using hj

theorem tendsto_fejer_scaled_integral {X : Type u} (h : X → ℝ)
    (a : Operator X) (ha : a ∈ continuityPoints h) :
    Tendsto (fun s : ℝ => ∫ t, fejerKernel 1 t • diagonalFlow h (t / s) a)
      atTop (𝓝 a) := by
  have hl : Tendsto (fun s : ℝ => ∫ t, fejerKernel 1 t • diagonalFlow h (t / s) a)
      atTop (𝓝 (∫ t, fejerKernel 1 t • a)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => fejerKernel 1 t * ‖a‖)
      ?_ ?_ ((integrable_fejerKernel zero_lt_one).mul_const ‖a‖) ?_
    · exact Eventually.of_forall fun s => ((continuous_fejerKernel 1).smul
        (ha.comp (continuous_id.div_const s))).aestronglyMeasurable
    · exact Eventually.of_forall fun s => Eventually.of_forall fun t => by
        simp only [norm_smul, Real.norm_of_nonneg (fejerKernel_nonneg zero_le_one t),
          diagonalFlow_norm, le_refl]
    · exact Eventually.of_forall fun t => by
        simpa only [Function.comp_def, diagonalFlow_zero, id_eq] using!
          (ha.continuousAt.tendsto.comp (tendsto_const_nhds.div_atTop tendsto_id)).const_smul
            (fejerKernel 1 t)
  simpa only [integral_smul_const, integral_fejerKernel zero_lt_one, one_smul] using hl

/-- Lemma ThetaKs(a).tends.to.a: Fejer averages converge in operator norm. -/
theorem tendsto_fejerAverage {X : Type u} (h : X → ℝ)
    (a : Operator X) (ha : a ∈ continuityPoints h) :
    Tendsto (fun s : ℝ => fejerAverage h s a) atTop (𝓝 a) :=
  (tendsto_fejer_scaled_integral h a ha).congr'
    ((eventually_gt_atTop 0).mono fun _s hs => (fejerAverage_eq_scaled_integral h hs a ha).symm)

/-- The forward inclusion in Theorem A, retaining the invariant possibly nonunital subalgebra. -/
theorem continuityPoint_mem_closure_finitePropagation {X : Type u} (h : X → ℝ)
    (A : NonUnitalStarSubalgebra ℂ (Operator X)) (hA : IsClosed (A : Set (Operator X)))
    (hinv : ∀ t a, a ∈ A → diagonalFlow h t a ∈ A)
    (a : Operator X) (ha : a ∈ continuityPoints h) (haA : a ∈ A) :
    a ∈ closure {b : Operator X | @HasFinitePropagation X (realPullbackPseudoMetric h) b ∧ b ∈ A} := by
  refine isClosed_closure.mem_of_tendsto (tendsto_fejerAverage h a ha) ?_
  exact (eventually_gt_atTop 0).mono fun s hs => subset_closure
    ⟨fejerAverage_hasFinitePropagation h hs a,
      averagingOperator_mem_invariant_subalgebra h (integrable_fejerKernel_all s).ofReal
        A hA hinv a ha haA⟩

end DynamicalCStarAlgebras
