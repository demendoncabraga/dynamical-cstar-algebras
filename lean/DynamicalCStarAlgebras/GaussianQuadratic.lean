import DynamicalCStarAlgebras.HaarUnitaryMoments
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
open Classical MeasureTheory ProbabilityTheory Real
namespace DynamicalCStarAlgebras

lemma gaussianPDF_mul_exp_sq (t x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (t * x ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * x ^ 2) := by
  unfold gaussianPDFReal
  norm_num only [NNReal.coe_one, mul_one, sub_zero, one_div]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma integrable_exp_sq_gaussian {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (ae_of_all _ (fun x => gaussianPDF_lt_top))]
  simpa only [smul_eq_mul, toReal_gaussianPDF, gaussianPDF_mul_exp_sq] using
    (integrable_exp_neg_mul_sq (show 0 < 1 / 2 - t by linarith)).const_mul
      (Real.sqrt (2 * Real.pi))⁻¹

/-- The exact moment-generating function of a squared standard Gaussian. -/
theorem integral_exp_sq_gaussian {t : ℝ} (ht : t < 1 / 2) :
    (∫ x : ℝ, Real.exp (t * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp_rw [smul_eq_mul, gaussianPDF_mul_exp_sq]
  rw [integral_const_mul, integral_gaussian]
  have hpos : 0 < 1 - 2 * t := by linarith
  rw [show 1 / 2 - t = (1 - 2 * t) / 2 by ring, div_div_eq_mul_div,
    Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
  field_simp
  rw [Real.sqrt_mul Real.pi_pos.le, mul_comm]

lemma integrable_exp_weighted_gaussian_squares {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (ht : ∀ i, t i < 1 / 2) :
    Integrable (fun x : ι → ℝ => Real.exp (∑ i, t i * x i ^ 2))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  simpa only [Real.exp_sum] using
    Integrable.fintype_prod_dep (fun i => integrable_exp_sq_gaussian (ht i))

theorem integral_exp_weighted_gaussian_squares {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (ht : ∀ i, t i < 1 / 2) :
    (∫ x : ι → ℝ, Real.exp (∑ i, t i * x i ^ 2)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
        ∏ i, (Real.sqrt (1 - 2 * t i))⁻¹ := by
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => Real.exp (t i * x ^ 2))]
  exact Finset.prod_congr rfl (fun i _ => integral_exp_sq_gaussian (ht i))

/-- Chernoff's bound for arbitrary finite weighted sums of Gaussian squares. -/
theorem weighted_gaussian_squares_nonneg_probability {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (ht : ∀ i, t i < 1 / 2) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1))
      {x | 0 ≤ ∑ i, t i * x i ^ 2} ≤
        ENNReal.ofReal (∏ i, (Real.sqrt (1 - 2 * t i))⁻¹) := by
  rw [← integral_exp_weighted_gaussian_squares t ht]
  exact (integrable_exp_weighted_gaussian_squares t ht).measure_le_integral
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))
    (fun _ hx => Real.one_le_exp hx)

lemma gaussian_pair_product {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (ht : ∀ i, t i < 1 / 2) :
    (∏ p : ι × Fin 2, (Real.sqrt (1 - 2 * t p.1))⁻¹) =
      ∏ i, (1 - 2 * t i)⁻¹ := by
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fin.prod_univ_two]
  rw [← mul_inv, Real.mul_self_sqrt (by linarith [ht i])]

/-- Chernoff's bound for paired real coordinates, one pair per complex coordinate. -/
theorem paired_gaussian_squares_nonneg_probability {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (ht : ∀ i, t i < 1 / 2) :
    (Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1))
      {x | 0 ≤ ∑ p, t p.1 * x p ^ 2} ≤
        ENNReal.ofReal (∏ i, (1 - 2 * t i)⁻¹) := by
  simpa only [gaussian_pair_product t ht] using
    weighted_gaussian_squares_nonneg_probability (fun p : ι × Fin 2 => t p.1)
      (fun p => ht p.1)

/-- A logarithmic inequality underlying the Gaussian projection tail. -/
lemma weighted_log_ratio_ge_sqrt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    2 * a - 2 * Real.sqrt a * Real.sqrt b ≤ a * Real.log (a / b) := by
  have hp : 0 < Real.sqrt (b / a) := Real.sqrt_pos.mpr (div_pos hb ha)
  have hl := Real.log_le_sub_one_of_pos hp
  have he : Real.log (a / b) = -2 * Real.log (Real.sqrt (b / a)) := by
    rw [Real.log_sqrt (div_nonneg hb.le ha.le), Real.log_div hb.ne' ha.ne',
      Real.log_div ha.ne' hb.ne']
    ring
  have hr : a * Real.sqrt (b / a) = Real.sqrt a * Real.sqrt b := by
    rw [Real.sqrt_div hb.le]
    have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
    field_simp
    nlinarith [Real.sq_sqrt ha.le]
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hl ha.le]

/-- Bernoulli relative entropy dominates squared distance between the square roots. -/
theorem bernoulli_entropy_ge_sqrt_distance {q s : ℝ}
    (hq : 0 < q) (hqone : q < 1) (hs : 0 < s) (hsone : s < 1) :
    (Real.sqrt s - Real.sqrt q) ^ 2 ≤
      q * Real.log (q / s) + (1 - q) * Real.log ((1 - q) / (1 - s)) := by
  have h₁ := weighted_log_ratio_ge_sqrt hq hs
  have h₂ := weighted_log_ratio_ge_sqrt (sub_pos.mpr hqone) (sub_pos.mpr hsone)
  have h₃ := sq_nonneg (Real.sqrt (1 - s) - Real.sqrt (1 - q))
  nlinarith [Real.sq_sqrt hq.le, Real.sq_sqrt hs.le,
    Real.sq_sqrt (sub_nonneg.mpr hqone.le), Real.sq_sqrt (sub_nonneg.mpr hsone.le)]

/-- Gaussian mass in a set of complex coordinates, expressed in real coordinate pairs. -/
def gaussianCoordinateMass {ι : Type*} [Fintype ι] (A : Finset ι)
    (x : ι × Fin 2 → ℝ) : ℝ := ∑ i ∈ A, ∑ j : Fin 2, x (i, j) ^ 2

lemma gaussian_coordinate_weighted_sum {ι : Type*} [Fintype ι]
    (A : Finset ι) (a b : ℝ) (x : ι × Fin 2 → ℝ) :
    (∑ p : ι × Fin 2, (if p.1 ∈ A then a else b) * x p ^ 2) =
      a * gaussianCoordinateMass A x + b * gaussianCoordinateMass Aᶜ x := by
  rw [Fintype.sum_prod_type, ← Finset.sum_add_sum_compl A]
  simp only [gaussianCoordinateMass, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j _
    simp only [hi, if_pos]
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j _
    simp [Finset.mem_compl.mp hi]

/-- Chernoff's explicit entropy estimate for the ratio of Gaussian coordinate masses. -/
theorem gaussian_coordinate_ratio_entropy_bound {ι : Type*} [Fintype ι]
    (A : Finset ι) {q s : ℝ} (hq : 0 < q) (hqone : q < 1)
    (hqs : q < s) (hsone : s < 1)
    (hcard : (A.card : ℝ) = Fintype.card ι * q) :
    (Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1))
      {x | s * (gaussianCoordinateMass A x + gaussianCoordinateMass Aᶜ x) ≤
        gaussianCoordinateMass A x} ≤
      ENNReal.ofReal (Real.exp (-(Fintype.card ι : ℝ) *
        (q * Real.log (q / s) + (1 - q) * Real.log ((1 - q) / (1 - s))))) := by
  have hs : 0 < s := hq.trans hqs
  let a := (1 - q / s) / 2
  let b := (1 - (1 - q) / (1 - s)) / 2
  let t (i : ι) := if i ∈ A then a else b
  have ht (i : ι) : t i < 1 / 2 := by
    dsimp [t, a, b]
    split_ifs
    · have := div_pos hq hs
      linarith
    · have := div_pos (sub_pos.mpr hqone) (sub_pos.mpr hsone)
      linarith
  have hsub : {x | s * (gaussianCoordinateMass A x + gaussianCoordinateMass Aᶜ x) ≤
        gaussianCoordinateMass A x} ⊆ {x | 0 ≤ ∑ p : ι × Fin 2, t p.1 * x p ^ 2} := by
    intro x hx
    change 0 ≤ ∑ p : ι × Fin 2, (if p.1 ∈ A then a else b) * x p ^ 2
    rw [gaussian_coordinate_weighted_sum A a b x]
    have hid : a * gaussianCoordinateMass A x + b * gaussianCoordinateMass Aᶜ x =
        (s - q) / (2 * s * (1 - s)) *
          (gaussianCoordinateMass A x - s *
            (gaussianCoordinateMass A x + gaussianCoordinateMass Aᶜ x)) := by
      dsimp [a, b]
      field_simp [hs.ne', (sub_pos.mpr hsone).ne']
      ring
    rw [hid]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hx)
  refine (measure_mono hsub).trans ((paired_gaussian_squares_nonneg_probability t ht).trans_eq ?_)
  congr 1
  have hi (i : ι) : (1 - 2 * t i)⁻¹ =
      Real.exp (if i ∈ A then -Real.log (q / s) else -Real.log ((1 - q) / (1 - s))) := by
    dsimp [t, a, b]
    split_ifs
    · rw [Real.exp_neg, Real.exp_log (div_pos hq hs)]
      congr 1
      ring
    · rw [Real.exp_neg, Real.exp_log (div_pos (sub_pos.mpr hqone) (sub_pos.mpr hsone))]
      congr 1
      ring
  simp_rw [hi, ← Real.exp_sum]
  congr 1
  rw [Finset.sum_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.univ.filter (fun i : ι => i ∉ A)).card = Fintype.card ι - A.card := by
    have he : Finset.univ.filter (fun i : ι => i ∉ A) = Aᶜ := by ext i; simp
    rw [he, Finset.card_compl]
  rw [hc, Nat.cast_sub A.card_le_univ, hcard]
  ring

/-- The normalized Gaussian coordinate-mass upper tail, with the sharp
square-root exponent needed by the frame-subspace argument. -/
theorem gaussian_coordinate_ratio_sqrt_bound {ι : Type*} [Fintype ι]
    (A : Finset ι) {q s : ℝ} (hq : 0 < q) (hqone : q < 1)
    (hqs : q < s) (hsone : s < 1)
    (hcard : (A.card : ℝ) = Fintype.card ι * q) :
    (Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1))
      {x | s * (gaussianCoordinateMass A x + gaussianCoordinateMass Aᶜ x) ≤
        gaussianCoordinateMass A x} ≤
      ENNReal.ofReal (Real.exp (-(Fintype.card ι : ℝ) *
        (Real.sqrt s - Real.sqrt q) ^ 2)) := by
  apply (gaussian_coordinate_ratio_entropy_bound A hq hqone hqs hsone hcard).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left
    (bernoulli_entropy_ge_sqrt_distance hq hqone (hq.trans hqs) hsone)
    (neg_nonpos.mpr (Nat.cast_nonneg _))

end DynamicalCStarAlgebras
