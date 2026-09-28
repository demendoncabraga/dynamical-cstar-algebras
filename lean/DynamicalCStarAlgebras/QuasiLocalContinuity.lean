import DynamicalCStarAlgebras.QuasiLocalCommutator

noncomputable section

namespace DynamicalCStarAlgebras

/-- Translate a real contraction into the unit interval. -/
theorem half_add_one_mem_unitInterval {r : ℝ} (hr : |r| ≤ 1) :
    0 ≤ (r + 1) / 2 ∧ (r + 1) / 2 ≤ 1 := by
  constructor <;> linarith [(abs_le.mp hr).1, (abs_le.mp hr).2]

/-- Estimate a complex commutator using its normalized real and imaginary parts. -/
theorem norm_commutator_complex_parts {X : Type*} (f : BoundedDiagonal X)
    (r s : BoundedDiagonal X) (a : Operator X)
    (hr : ∀ x, r x = (((f x).re + 1) / 2 : ℝ))
    (hs : ∀ x, s x = (((f x).im + 1) / 2 : ℝ)) :
    ‖diagonalCommutator f a‖ ≤
      2 * ‖diagonalCommutator r a‖ + 2 * ‖diagonalCommutator s a‖ := by
  have he : diagonalCommutator f a = (2 : ℂ) • diagonalCommutator r a +
      (2 * Complex.I) • diagonalCommutator s a := by
    refine operator_ext fun x y => ?_
    change _ = (matrixEntryCLM x y) (_ + _)
    simp only [map_add, map_smul, matrixEntryCLM_apply, matrixEntry_diagonalCommutator,
      hr, hs, smul_eq_mul, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one,
      Complex.ofReal_ofNat]
    calc
      _ = (((f x).re + (f x).im * Complex.I) -
          ((f y).re + (f y).im * Complex.I)) * matrixEntry a x y := by
        rw [Complex.re_add_im, Complex.re_add_im]
      _ = _ := by ring
  rw [he]
  simpa only [norm_smul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one] using
    norm_add_le ((2 : ℂ) • diagonalCommutator r a) ((2 * Complex.I) • diagonalCommutator s a)

theorem half_add_one_variation {r q δ : ℝ} (h : |r - q| ≤ 2 * δ) :
    |(r + 1) / 2 - (q + 1) / 2| ≤ δ := by
  rw [show (r + 1) / 2 - (q + 1) / 2 = (r - q) / 2 by ring, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- A complex version sufficient for the unitary phases defining the flows. -/
theorem quasiLocal_complex_commutator_bound {X : Type*} (f : BoundedDiagonal X)
    (hf : ∀ x, ‖f x‖ ≤ 1) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (a : Operator X) {E : Set (X × X)} (ha : IsQuasiLocalAt a ε E)
    (hr : ∀ p ∈ E, |(f p.1).re - (f p.2).re| ≤ 2 * δ)
    (hi : ∀ p ∈ E, |(f p.1).im - (f p.2).im| ≤ 2 * δ) :
    ‖diagonalCommutator f a‖ ≤ 16 * δ * ‖a‖ + 8 * δ⁻¹ * ε := by
  let r : X → ℝ := fun x => ((f x).re + 1) / 2
  let s : X → ℝ := fun x => ((f x).im + 1) / 2
  have hrange : ∀ x, 0 ≤ r x ∧ r x ≤ 1 := fun x =>
    half_add_one_mem_unitInterval ((Complex.abs_re_le_norm (f x)).trans (hf x))
  have sirange : ∀ x, 0 ≤ s x ∧ s x ≤ 1 := fun x =>
    half_add_one_mem_unitInterval ((Complex.abs_im_le_norm (f x)).trans (hf x))
  have hrb := quasiLocal_commutator_bound r hrange hδ hε a ha
    (fun p hp => half_add_one_variation (hr p hp))
  have hib := quasiLocal_commutator_bound s sirange hδ hε a ha
    (fun p hp => half_add_one_variation (hi p hp))
  have hp := norm_commutator_complex_parts f
    (boundedRealDiagonal r 1 (fun x => (abs_of_nonneg (hrange x).1).trans_le (hrange x).2))
    (boundedRealDiagonal s 1 (fun x => (abs_of_nonneg (sirange x).1).trans_le (sirange x).2))
    a (fun _ => rfl) (fun _ => rfl)
  linarith

/-- The bounded diagonal underlying the phase unitary. -/
def phaseDiagonal {X : Type*} (h : X → ℝ) (t : ℝ) : BoundedDiagonal X :=
  ⟨diagonalPhase h t, memℓp_infty ⟨1, fun _ ⟨x, hx⟩ => hx ▸ (diagonalPhase_norm h t x).le⟩⟩

theorem diagonalMultiplier_phaseDiagonal {X : Type*} (h : X → ℝ) (t : ℝ) :
    diagonalMultiplier (phaseDiagonal h t) = diagonalUnitary h t := by
  exact ContinuousLinearMap.ext fun v => lp.ext (funext fun x => rfl)

theorem diagonalFlow_sub_norm_le_commutator {X : Type*} (h : X → ℝ) (t : ℝ)
    (a : Operator X) :
    ‖diagonalFlow h t a - a‖ ≤ ‖diagonalCommutator (phaseDiagonal h t) a‖ := by
  have he : diagonalFlow h t a - a =
      diagonalCommutator (phaseDiagonal h t) a * diagonalUnitary h (-t) := by
    rw [diagonalCommutator, diagonalMultiplier_phaseDiagonal, sub_mul, mul_assoc a,
      ← diagonalUnitary_add, add_neg_cancel, diagonalUnitary_zero, mul_one]
    rfl
  rw [he]
  exact (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _)
    (diagonalUnitary_norm_le h (-t)))

/-- Quantitative orbit continuity from quasi-locality on one controlled relation. -/
theorem quasiLocal_diagonalFlow_bound {X : Type*} (h : X → ℝ) (t : ℝ)
    {δ ε R : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε) (a : Operator X)
    {E : Set (X × X)} (ha : IsQuasiLocalAt a ε E)
    (hR : ∀ p ∈ E, dist (h p.1) (h p.2) ≤ R) (ht : |t| * R ≤ 2 * δ) :
    ‖diagonalFlow h t a - a‖ ≤ 16 * δ * ‖a‖ + 8 * δ⁻¹ * ε := by
  refine (diagonalFlow_sub_norm_le_commutator h t a).trans
    (quasiLocal_complex_commutator_bound (phaseDiagonal h t)
      (fun x => (diagonalPhase_norm h t x).le) hδ hε a ha ?_ ?_)
  · simp only [phaseDiagonal, diagonalPhase, Complex.exp_ofReal_mul_I_re]
    intro p hp
    refine (Real.abs_cos_sub_cos_le _ _).trans (le_trans ?_ ht)
    simpa only [← mul_sub, abs_mul, Real.dist_eq] using
      mul_le_mul_of_nonneg_left (hR p hp) (abs_nonneg t)
  · simp only [phaseDiagonal, diagonalPhase, Complex.exp_ofReal_mul_I_im]
    intro p hp
    refine (Real.abs_sin_sub_sin_le _ _).trans (le_trans ?_ ht)
    simpa only [← mul_sub, abs_mul, Real.dist_eq] using
      mul_le_mul_of_nonneg_left (hR p hp) (abs_nonneg t)

/-- Quasi-local operators have continuous orbits under every coarse real flow,
for an arbitrary coarse space (the forward inclusion in Theorem B). -/
theorem quasiLocal_subset_coarseContinuityPoints {X : Type*} (C : CoarseStructure X) :
    quasiLocal C ⊆ coarseContinuityPoints C := by
  intro a ha h hh
  apply (mem_continuityPoints_iff_continuousAt_zero h a).mpr
  refine Metric.continuousAt_iff.mpr fun η hη => ?_
  let δ := η / (64 * (‖a‖ + 1))
  have hδ : 0 < δ := div_pos hη (by positivity)
  obtain ⟨E, hE, haE⟩ := ha (η * δ / 32) (by positivity)
  obtain ⟨R, hR⟩ := hh E hE
  refine ⟨δ / (|R| + 1), by positivity, fun t ht => ?_⟩
  have ht' : |t| * (|R| + 1) < δ := (lt_div_iff₀ (by positivity)).mp (by
    simpa only [Real.dist_eq, sub_zero] using ht)
  have hb := quasiLocal_diagonalFlow_bound h t hδ (by positivity) a haE hR
    (show |t| * R ≤ 2 * δ by
      nlinarith [mul_le_mul_of_nonneg_left (le_abs_self R) (abs_nonneg t), abs_nonneg t])
  have he : 8 * δ⁻¹ * (η * δ / 32) = η / 4 := by field_simp; ring
  have hd : δ * (64 * (‖a‖ + 1)) = η := div_mul_cancel₀ η (by positivity)
  rw [he] at hb
  rw [diagonalFlow_zero, dist_eq_norm]
  nlinarith

end DynamicalCStarAlgebras
