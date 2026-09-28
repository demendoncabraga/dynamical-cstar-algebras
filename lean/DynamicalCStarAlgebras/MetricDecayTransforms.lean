import DynamicalCStarAlgebras.ExpanderTheorems
import DynamicalCStarAlgebras.ConstructedExpanderUnion

noncomputable section
namespace DynamicalCStarAlgebras

/-- The square-root metric has the same bounded-distance coarse structure. -/
@[instance_reducible] def sqrtPseudoMetric {X : Type*} [PseudoMetricSpace X] :
    PseudoMetricSpace X where
  dist x y := Real.sqrt (dist x y)
  dist_self x := by simp
  dist_comm x y := by rw [dist_comm]
  dist_triangle x y z := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have h₁ := Real.sq_sqrt (dist_nonneg (x := x) (y := y))
    have h₂ := Real.sq_sqrt (dist_nonneg (x := y) (y := z))
    nlinarith [dist_triangle x y z,
      mul_nonneg (Real.sqrt_nonneg (dist x y)) (Real.sqrt_nonneg (dist y z))]

lemma sqrtPseudoMetric_coarse {X : Type*} [m : PseudoMetricSpace X] :
    @CoarseStructure.ofPseudoMetric X (sqrtPseudoMetric (X := X)) =
      CoarseStructure.ofPseudoMetric X := by
  simp only [CoarseStructure.ofPseudoMetric, CoarseStructure.mk.injEq]
  ext E
  change (∃ R : ℝ, ∀ p ∈ E, Real.sqrt (dist p.1 p.2) ≤ R) ↔
    ∃ R : ℝ, ∀ p ∈ E, dist p.1 p.2 ≤ R
  constructor
  · rintro ⟨R, hR⟩
    exact ⟨R ^ 2, fun p hp => (Real.sqrt_le_iff.mp (hR p hp)).2⟩
  · rintro ⟨R, hR⟩
    exact ⟨Real.sqrt R, fun p hp => Real.sqrt_le_sqrt (hR p hp)⟩

lemma quasiLocalModulus_sqrtMetric {X : Type*} [PseudoMetricSpace X]
    (a : Operator X) {r : ℝ} (hr : 0 ≤ r) :
    @quasiLocalModulus X (sqrtPseudoMetric (X := X)) a r = quasiLocalModulus a (r ^ 2) := by
  unfold quasiLocalModulus
  congr 1
  ext s
  simp only [compressionNorms, Set.mem_ofPred_eq]
  change (∃ A B : Set X, (∀ x ∈ A, ∀ y ∈ B, r ≤ Real.sqrt (dist x y)) ∧ _) ↔ _
  simp_rw [Real.le_sqrt hr dist_nonneg]

lemma hasPolynomialDecay_sqrtMetric {X : Type*} [PseudoMetricSpace X]
    (a : Operator X) (α : ℝ) :
    @HasPolynomialDecay X (sqrtPseudoMetric (X := X)) α a ↔ HasPolynomialDecay (α / 2) a := by
  constructor
  · rintro ⟨M, hM, hb⟩
    refine ⟨M, hM, fun r hr => ?_⟩
    have hh := hb (Real.sqrt r) (Real.sqrt_pos.mpr hr)
    rw [quasiLocalModulus_sqrtMetric a (Real.sqrt_nonneg _), Real.sq_sqrt hr.le] at hh
    convert hh using 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hr.le]
    congr 2
    ring
  · rintro ⟨M, hM, hb⟩
    refine ⟨M, hM, fun r hr => ?_⟩
    rw [quasiLocalModulus_sqrtMetric a hr.le]
    have hh := hb (r ^ 2) (sq_pos_of_pos hr)
    convert hh using 1
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    congr 2
    ring

lemma polynomialQuasiLocal_sqrtMetric {X : Type*} [PseudoMetricSpace X] (α : ℝ) :
    @polynomialQuasiLocal X (sqrtPseudoMetric (X := X)) α = polynomialQuasiLocal (α / 2) := by
  unfold polynomialQuasiLocal
  congr 1
  ext a
  exact hasPolynomialDecay_sqrtMetric a α

/-- A logarithmic change of scale, without truncation of large distances. -/
@[instance_reducible] def logPseudoMetric {X : Type*} [PseudoMetricSpace X] :
    PseudoMetricSpace X where
  dist x y := Real.log (1 + dist x y)
  dist_self x := by simp
  dist_comm x y := by rw [dist_comm]
  dist_triangle x y z := by
    have hp (a b : X) : 0 < 1 + dist a b := by positivity
    calc
      Real.log (1 + dist x z) ≤ Real.log ((1 + dist x y) * (1 + dist y z)) := by
        apply Real.log_le_log (hp _ _)
        nlinarith [dist_triangle x y z, mul_nonneg (dist_nonneg (x := x) (y := y))
          (dist_nonneg (x := y) (y := z))]
      _ = _ := Real.log_mul (hp _ _).ne' (hp _ _).ne'

lemma logPseudoMetric_coarse {X : Type*} [m : PseudoMetricSpace X] :
    @CoarseStructure.ofPseudoMetric X (logPseudoMetric (X := X)) =
      CoarseStructure.ofPseudoMetric X := by
  simp only [CoarseStructure.ofPseudoMetric, CoarseStructure.mk.injEq]
  ext E
  change (∃ R : ℝ, ∀ p ∈ E, Real.log (1 + dist p.1 p.2) ≤ R) ↔
    ∃ R : ℝ, ∀ p ∈ E, dist p.1 p.2 ≤ R
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨Real.exp R - 1, fun p hp => ?_⟩
    have hb := (Real.log_le_iff_le_exp (by positivity : 0 < 1 + dist p.1 p.2)).mp (hR p hp)
    linarith
  · rintro ⟨R, hR⟩
    refine ⟨Real.log (1 + max R 0), fun p hp => ?_⟩
    apply Real.log_le_log (by positivity)
    exact add_le_add_right ((hR p hp).trans (le_max_left R 0)) 1

lemma quasiLocalModulus_logMetric {X : Type*} [PseudoMetricSpace X]
    (a : Operator X) (r : ℝ) :
    @quasiLocalModulus X (logPseudoMetric (X := X)) a r =
      quasiLocalModulus a (Real.exp r - 1) := by
  unfold quasiLocalModulus
  congr 1
  ext s
  simp only [compressionNorms, Set.mem_ofPred_eq]
  change (∃ A B : Set X, (∀ x ∈ A, ∀ y ∈ B, r ≤ Real.log (1 + dist x y)) ∧ _) ↔ _
  have he (x y : X) : r ≤ Real.log (1 + dist x y) ↔ Real.exp r - 1 ≤ dist x y := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    constructor <;> intro h <;> linarith
  simp_rw [he]

lemma hasExponentialDecay_logMetric_of_polynomial {X : Type*} [PseudoMetricSpace X]
    {a : Operator X} (ha : HasPolynomialDecay 1 a) :
    @HasExponentialDecay X (logPseudoMetric (X := X)) a := by
  obtain ⟨M, hM, hbound⟩ := ha
  refine ⟨1, by norm_num, 2 * (M + ‖a‖ + 1), by positivity, fun r hr => ?_⟩
  rw [quasiLocalModulus_logMetric, neg_one_mul]
  by_cases hlarge : Real.log 2 ≤ r
  · have he : 2 ≤ Real.exp r := (Real.log_le_iff_le_exp (by norm_num)).mp hlarge
    have hepos := Real.exp_pos r
    have hu : 0 < Real.exp r - 1 := by linarith
    have hb := hbound (Real.exp r - 1) hu
    rw [Real.rpow_neg_one] at hb
    have hi : (Real.exp r - 1)⁻¹ ≤ 2 * Real.exp (-r) := by
      rw [Real.exp_neg]
      apply (inv_le_iff_one_le_mul₀ hu).mpr
      have hiE := (inv_le_inv₀ hepos (by norm_num : (0 : ℝ) < 2)).mpr he
      norm_num at hiE
      nlinarith [mul_inv_cancel₀ hepos.ne']
    exact hb.trans ((mul_le_mul_of_nonneg_left hi hM.le).trans (by
      nlinarith [Real.exp_pos (-r), norm_nonneg a]))
  · have he : (1 / 2 : ℝ) ≤ Real.exp (-r) := by
      have hh : Real.exp r ≤ 2 := (Real.exp_le_exp.mpr (le_of_not_ge hlarge)).trans_eq
        (Real.exp_log (by norm_num))
      rw [Real.exp_neg]
      exact (le_inv_comm₀ (by norm_num : (0 : ℝ) < 1 / 2) (Real.exp_pos r)).mpr (by norm_num; exact hh)
    exact (quasiLocalModulus_le_norm a _).trans (by
      nlinarith [norm_nonneg a, mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ M + ‖a‖ + 1)])

lemma polynomialQuasiLocal_subset_exponentialQuasiLocal_logMetric
    {X : Type*} [PseudoMetricSpace X] :
    polynomialQuasiLocal (X := X) 1 ⊆
      @exponentialQuasiLocal X (logPseudoMetric (X := X)) :=
  closure_mono fun _ ha => hasExponentialDecay_logMetric_of_polynomial ha

/-- Nondegeneracy is retained by the square-root change of metric. -/
@[instance_reducible] def sqrtMetric {X : Type*} [MetricSpace X] : MetricSpace X :=
  { sqrtPseudoMetric (X := X) with
    eq_of_dist_eq_zero := fun {x y} h => by
      change Real.sqrt (dist x y) = 0 at h
      have he := congrArg (fun r : ℝ => r ^ 2) h
      rw [Real.sq_sqrt dist_nonneg, zero_pow (by decide : 2 ≠ 0)] at he
      exact dist_eq_zero.mp he }

/-- Nondegeneracy is retained by the logarithmic change of metric. -/
@[instance_reducible] def logMetric {X : Type*} [MetricSpace X] : MetricSpace X :=
  { logPseudoMetric (X := X) with
    eq_of_dist_eq_zero := fun {x y} h => by
      change Real.log (1 + dist x y) = 0 at h
      have he := congrArg Real.exp h
      rw [Real.exp_log (by positivity), Real.exp_zero] at he
      exact dist_eq_zero.mp (by linarith) }

/-- Every expander gives a square-root remetrization changing every polynomial
algebra, although the bounded-distance coarse structure is exactly unchanged. -/
theorem ExpanderGraphUnionData.polynomial_metric_counterexample
    {X : Type*} [m : MetricSpace X] (D : ExpanderGraphUnionData X) {α : ℝ} (hα : 0 < α) :
    ∃ m' : MetricSpace X,
      @CoarseStructure.ofPseudoMetric X (MetricSpace.toPseudoMetricSpace (self := m')) =
        @CoarseStructure.ofPseudoMetric X (MetricSpace.toPseudoMetricSpace (self := m)) ∧
      @polynomialQuasiLocal X (MetricSpace.toPseudoMetricSpace (self := m)) α ⊂
        @polynomialQuasiLocal X (MetricSpace.toPseudoMetricSpace (self := m')) α := by
  refine ⟨sqrtMetric, sqrtPseudoMetric_coarse, ?_⟩
  change polynomialQuasiLocal (X := X) α ⊂
    @polynomialQuasiLocal X (sqrtPseudoMetric (X := X)) α
  rw [polynomialQuasiLocal_sqrtMetric]
  exact (D.toExpanderGraphUnion.strict_decay_inclusions (half_pos hα) (by linarith)).2.1

/-- Every expander gives a logarithmic remetrization changing its exponential
algebra, again with exactly the same bounded-distance coarse structure. -/
theorem ExpanderGraphUnionData.exponential_metric_counterexample
    {X : Type*} [m : MetricSpace X] (D : ExpanderGraphUnionData X) :
    ∃ m' : MetricSpace X,
      @CoarseStructure.ofPseudoMetric X (MetricSpace.toPseudoMetricSpace (self := m')) =
        @CoarseStructure.ofPseudoMetric X (MetricSpace.toPseudoMetricSpace (self := m)) ∧
      @exponentialQuasiLocal X (MetricSpace.toPseudoMetricSpace (self := m)) ⊂
        @exponentialQuasiLocal X (MetricSpace.toPseudoMetricSpace (self := m')) := by
  refine ⟨logMetric, logPseudoMetric_coarse, ?_⟩
  change (exponentialQuasiLocal : Set (Operator X)) ⊂
    @exponentialQuasiLocal X (logPseudoMetric (X := X))
  have hs := (D.toExpanderGraphUnion.strict_decay_inclusions
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).1
  exact hs.trans_le polynomialQuasiLocal_subset_exponentialQuasiLocal_logMetric

/-- Polynomial quantitative quasi-locality is not a bijective coarse invariant,
with an actual pair of uniformly locally finite metrics for every positive exponent. -/
theorem polynomialDecay_not_coarse_invariant {α : ℝ} (hα : 0 < α) :
    ∃ m' : MetricSpace ConstructedExpanderSpace,
      @UniformlyLocallyFinite ConstructedExpanderSpace m'.toPseudoMetricSpace ∧
      @CoarseStructure.ofPseudoMetric ConstructedExpanderSpace m'.toPseudoMetricSpace =
        @CoarseStructure.ofPseudoMetric ConstructedExpanderSpace
          constructedExpanderMetric.toPseudoMetricSpace ∧
      @polynomialQuasiLocal ConstructedExpanderSpace constructedExpanderMetric.toPseudoMetricSpace α ⊂
        @polynomialQuasiLocal ConstructedExpanderSpace m'.toPseudoMetricSpace α := by
  obtain ⟨m', hc, hp⟩ := constructedExpanderUnionData.polynomial_metric_counterexample hα
  refine ⟨m', ?_, hc, hp⟩
  apply (@coarse_uniformlyLocallyFinite_iff ConstructedExpanderSpace m'.toPseudoMetricSpace).mp
  rw [hc]
  exact (@coarse_uniformlyLocallyFinite_iff ConstructedExpanderSpace
    constructedExpanderMetric.toPseudoMetricSpace).mpr constructedExpanderSpace_uniformlyLocallyFinite

/-- Exponential quantitative quasi-locality likewise changes on a concrete
uniformly locally finite space while its coarse structure is fixed. -/
theorem exponentialDecay_not_coarse_invariant :
    ∃ m' : MetricSpace ConstructedExpanderSpace,
      @UniformlyLocallyFinite ConstructedExpanderSpace m'.toPseudoMetricSpace ∧
      @CoarseStructure.ofPseudoMetric ConstructedExpanderSpace m'.toPseudoMetricSpace =
        @CoarseStructure.ofPseudoMetric ConstructedExpanderSpace
          constructedExpanderMetric.toPseudoMetricSpace ∧
      @exponentialQuasiLocal ConstructedExpanderSpace constructedExpanderMetric.toPseudoMetricSpace ⊂
        @exponentialQuasiLocal ConstructedExpanderSpace m'.toPseudoMetricSpace := by
  obtain ⟨m', hc, hp⟩ := constructedExpanderUnionData.exponential_metric_counterexample
  refine ⟨m', ?_, hc, hp⟩
  apply (@coarse_uniformlyLocallyFinite_iff ConstructedExpanderSpace m'.toPseudoMetricSpace).mp
  rw [hc]
  exact (@coarse_uniformlyLocallyFinite_iff ConstructedExpanderSpace
    constructedExpanderMetric.toPseudoMetricSpace).mpr constructedExpanderSpace_uniformlyLocallyFinite

end DynamicalCStarAlgebras
