import DynamicalCStarAlgebras.HaarFrameSubspaces
import DynamicalCStarAlgebras.GaussianSphereLaw
import DynamicalCStarAlgebras.GaussianQuadratic

/-! Complex Gaussian coordinate concentration and the frame-subspace theorem
cited in paper/main.tex as `cor.lem:frame` (Li--Zhang--Zhu, Proposition 6.3,
https://arxiv.org/html/2608.22439v2#S6.SS2).
Pairing real standard Gaussians realizes the underlying-real complex Gaussian.
Its normalized law is the Haar orbit law. The checked Gaussian ratio bound
then supplies coordinate concentration and closes the finite-net construction
with the universal constant 32. -/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DynamicalCStarAlgebras

/-- Pair successive real coordinates into complex coordinates. -/
def pairedComplexVector {ι : Type*} [Fintype ι] (x : ι × Fin 2 → ℝ) :
    EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => ⟨x (i, 0), x (i, 1)⟩)

lemma pairedComplexVector_coordinate_norm_sq {ι : Type*} [Fintype ι]
    (x : ι × Fin 2 → ℝ) (i : ι) :
    ‖pairedComplexVector x i‖ ^ 2 = ∑ j : Fin 2, x (i, j) ^ 2 := by
  change ‖(⟨x (i, 0), x (i, 1)⟩ : ℂ)‖ ^ 2 = _
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Fin.sum_univ_two, pow_two]

lemma pairedComplexVector_norm_sq {ι : Type*} [Fintype ι] (x : ι × Fin 2 → ℝ) :
    ‖pairedComplexVector x‖ ^ 2 = ∑ i, ∑ j : Fin 2, x (i, j) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [pairedComplexVector_coordinate_norm_sq]

lemma pairedComplexVector_restriction_norm_sq {ι : Type*} [Fintype ι]
    (A : Finset ι) (x : ι × Fin 2 → ℝ) :
    ‖euclideanCoordinateRestriction A (pairedComplexVector x)‖ ^ 2 =
      ∑ i ∈ A, ∑ j : Fin 2, x (i, j) ^ 2 := by
  rw [norm_sq_euclideanCoordinateRestriction]
  simp only [pairedComplexVector_coordinate_norm_sq]

/-- Pairing real coordinates is a real linear isometric equivalence. -/
def pairedRealComplexEquiv (ι : Type*) [Fintype ι] :
    EuclideanSpace ℝ (ι × Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι where
  toFun x := pairedComplexVector x
  invFun z := WithLp.toLp 2 (fun p => if p.2 = 0 then (z p.1).re else (z p.1).im)
  left_inv x := by
    ext ⟨i, j⟩
    fin_cases j <;> rfl
  right_inv z := by ext i; rfl
  map_add' x y := by ext i; rfl
  map_smul' c x := by
    ext i : 1
    apply Complex.ext <;> simp [pairedComplexVector]
  norm_map' x := by
    change ‖pairedComplexVector x‖ = ‖x‖
    have hsq : ‖pairedComplexVector x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [pairedComplexVector_norm_sq, EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
    nlinarith [norm_nonneg (pairedComplexVector x), norm_nonneg x]


/-- Independent real Gaussian pairs give the standard Gaussian of the complex
space regarded as a real inner product space. -/
theorem map_pairedComplexVector_stdGaussian {ι : Type*} [Fintype ι] :
    (Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)).map pairedComplexVector =
      stdGaussian (EuclideanSpace ℂ ι) := by
  change (Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)).map
    (pairedRealComplexEquiv ι ∘ WithLp.toLp 2) = _
  rw [← Measure.map_map (pairedRealComplexEquiv ι).continuous.measurable
      (PiLp.continuous_toLp 2 (fun _ : ι × Fin 2 => ℝ)).measurable,
    map_pi_eq_stdGaussian, stdGaussian_map]


lemma measurable_pairedComplexVector {ι : Type*} [Fintype ι] :
    Measurable (pairedComplexVector (ι := ι)) :=
  (pairedRealComplexEquiv ι).continuous.measurable.comp
    (PiLp.continuous_toLp 2 (fun _ : ι × Fin 2 => ℝ)).measurable

/-- The Haar orbit law represented using explicit independent real coordinate pairs. -/
theorem unitaryOrbitLaw_eq_map_paired_normalized_gaussian {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    unitaryOrbitLaw v = (Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)).map
      (gaussianSphereNormalize ∘ pairedComplexVector) := by
  rw [← gaussianDirectionLaw_eq_unitaryOrbitLaw v hv, gaussianDirectionLaw,
    ← map_pairedComplexVector_stdGaussian,
    Measure.map_map measurable_gaussianSphereNormalize measurable_pairedComplexVector]

lemma gaussianSphereNormalize_norm_le_one {ι : Type*} [Fintype ι]
    (z : EuclideanSpace ℂ ι) : ‖gaussianSphereNormalize z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz, gaussianSphereNormalize]
  · exact (gaussianSphereNormalize_norm hz).le

lemma gaussianSphereNormalize_restriction_sq_mul_norm_sq {ι : Type*} [Fintype ι]
    (A : Finset ι) (z : EuclideanSpace ℂ ι) :
    ‖euclideanCoordinateRestriction A (gaussianSphereNormalize z)‖ ^ 2 * ‖z‖ ^ 2 =
      ‖euclideanCoordinateRestriction A z‖ ^ 2 := by
  by_cases hz : z = 0
  · simp only [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
    change 0 = ‖(euclideanCoordinateRestrictionCLM A) 0‖ ^ 2
    simp
  · change ‖‖z‖⁻¹ • euclideanCoordinateRestriction A z‖ ^ 2 * ‖z‖ ^ 2 = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z))]
    field_simp


lemma pairedComplexVector_total_mass {ι : Type*} [Fintype ι]
    (A : Finset ι) (x : ι × Fin 2 → ℝ) :
    ‖pairedComplexVector x‖ ^ 2 = gaussianCoordinateMass A x + gaussianCoordinateMass Aᶜ x := by
  rw [pairedComplexVector_norm_sq, ← Finset.sum_add_sum_compl A]
  rfl

/-- The Haar coordinate tail from Gaussian ratios; this is stronger than (6.6). -/
theorem unitaryOrbitLaw_coordinate_tail {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) (A : Finset ι) (hA : A.Nonempty)
    {t : ℝ} (ht : 0 ≤ t) :
    (unitaryOrbitLaw v) {z | Real.sqrt ((A.card : ℝ) / Fintype.card ι) + t <
      ‖euclideanCoordinateRestriction A z‖} ≤
        ENNReal.ofReal (Real.exp (-(Fintype.card ι : ℝ) * t ^ 2)) := by
  by_cases ht0 : t = 0
  · simp only [ht0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      Real.exp_zero, ENNReal.ofReal_one]
    exact prob_le_one
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hmeas : MeasurableSet {z : EuclideanSpace ℂ ι |
      Real.sqrt ((A.card : ℝ) / Fintype.card ι) + t < ‖euclideanCoordinateRestriction A z‖} :=
    measurableSet_lt measurable_const (euclideanCoordinateRestrictionCLM A).continuous.norm.measurable
  rw [unitaryOrbitLaw_eq_map_paired_normalized_gaussian v hv,
    Measure.map_apply (measurable_gaussianSphereNormalize.comp measurable_pairedComplexVector) hmeas]
  let q : ℝ := (A.card : ℝ) / Fintype.card ι
  have hd : 0 < Fintype.card ι := hA.card_pos.trans_le (Finset.card_le_univ A)
  have hdR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hd
  have hq : 0 < q := div_pos (by exact_mod_cast hA.card_pos) hdR
  by_cases hthreshold : Real.sqrt q + t < 1
  · let s : ℝ := (Real.sqrt q + t) ^ 2
    have hqs : q < s := by
      dsimp [s]
      nlinarith [Real.sq_sqrt hq.le, Real.sqrt_nonneg q]
    have hsone : s < 1 := by
      dsimp [s]
      nlinarith [Real.sqrt_nonneg q]
    have hqone : q < 1 := hqs.trans hsone
    have hcard : (A.card : ℝ) = Fintype.card ι * q := by dsimp [q]; field_simp
    have hsub : (gaussianSphereNormalize ∘ pairedComplexVector) ⁻¹'
        {z | Real.sqrt ((A.card : ℝ) / Fintype.card ι) + t <
          ‖euclideanCoordinateRestriction A z‖} ⊆
        {x | s * (gaussianCoordinateMass A x + gaussianCoordinateMass Aᶜ x) ≤
          gaussianCoordinateMass A x} := by
      intro x hx
      have hh : s ≤ ‖euclideanCoordinateRestriction A
          (gaussianSphereNormalize (pairedComplexVector x))‖ ^ 2 := by
        change Real.sqrt q + t < ‖euclideanCoordinateRestriction A
          (gaussianSphereNormalize (pairedComplexVector x))‖ at hx
        dsimp [s]
        nlinarith [Real.sqrt_nonneg q]
      have hm := mul_le_mul_of_nonneg_right hh
        (sq_nonneg ‖pairedComplexVector x‖)
      rw [gaussianSphereNormalize_restriction_sq_mul_norm_sq,
        pairedComplexVector_restriction_norm_sq, pairedComplexVector_total_mass A] at hm
      exact hm
    have hprob := (measure_mono hsub).trans
      (gaussian_coordinate_ratio_sqrt_bound A hq hqone hqs hsone hcard)
    have hsqrt : Real.sqrt s - Real.sqrt q = t := by
      dsimp [s]
      rw [Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg q) ht)]
      ring
    simpa only [hsqrt] using hprob
  · have hempty : (gaussianSphereNormalize ∘ pairedComplexVector) ⁻¹'
        {z | Real.sqrt ((A.card : ℝ) / Fintype.card ι) + t <
          ‖euclideanCoordinateRestriction A z‖} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hnorm := (euclideanCoordinateRestriction_norm_le A
        (gaussianSphereNormalize (pairedComplexVector x))).trans
          (gaussianSphereNormalize_norm_le_one _)
      exact (not_lt_of_ge (hnorm.trans (le_of_not_gt hthreshold))) hx
    rw [hempty, measure_empty]
    exact bot_le


/-- The cited complex frame-subspace theorem, with the universal constant 32.
No probabilistic or external mathematical hypothesis remains. -/
theorem exists_frame_subspace (d r : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d) :
    ∃ W : ClosedSubmodule ℂ (HilbertSpace (Fin d)),
      Module.finrank ℂ W.toSubmodule = r ∧ ∀ (A : Finset (Fin d)), A.Nonempty →
      ‖coordinateProjection (A : Set (Fin d)) * W.toSubmodule.starProjection‖ ≤
        32 * Real.sqrt ((r : ℝ) / d + (A.card : ℝ) / d *
          Real.log (Real.exp 1 * d / A.card)) := by
  apply exists_frame_subspace_of_haar_coordinate_tails hr hrd
  intro v hv A hA t ht _htone
  have htail := unitaryOrbitLaw_coordinate_tail v hv A hA ht
  simp only [Fintype.card_fin] at htail
  refine (measure_mono ?_).trans (htail.trans (ENNReal.ofReal_le_ofReal ?_))
  · intro z hz
    have hshift : 0 ≤ 12 / Real.sqrt (2 * (d : ℝ)) := by positivity
    change Real.sqrt ((A.card : ℝ) / d) + 12 / Real.sqrt (2 * d) + t <
      ‖euclideanCoordinateRestriction A z‖ at hz
    change Real.sqrt ((A.card : ℝ) / d) + t < ‖euclideanCoordinateRestriction A z‖
    linarith
  · nlinarith [Real.exp_pos (-(d : ℝ) * t ^ 2)]

end DynamicalCStarAlgebras
