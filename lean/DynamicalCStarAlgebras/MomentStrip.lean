import DynamicalCStarAlgebras.MomentSeries

noncomputable section

namespace DynamicalCStarAlgebras

/-- Translate the Taylor series to a real center by the isometric diagonal flow. -/
def diagonalMomentDisk {X : Type*} (h : X → ℝ) (b : ℕ → Operator X) (t : ℝ)
    (z : ℂ) : Operator X :=
  diagonalFlow h t ((diagonalMomentSeries b).sum (z - (t : ℂ)))

/-- Every real-centered Taylor disk has the same complex-time matrix coefficients. -/
theorem matrixEntry_diagonalMomentDisk {X : Type*} {h : X → ℝ} {a : Operator X}
    {b : ℕ → Operator X} (hb : IsDiagonalMomentSequence h a b) (t : ℝ) (z : ℂ)
    (hz : z - (t : ℂ) ∈ Metric.eball 0 (diagonalMomentSeries b).radius) (x y : X) :
    matrixEntry (diagonalMomentDisk h b t z) x y =
      Complex.exp (Complex.I * z * ((h x - h y : ℝ) : ℂ)) * matrixEntry a x y := by
  rw [diagonalMomentDisk, matrixEntry_diagonalFlow, matrixEntry_diagonalMomentSeries_sum hb hz,
    ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The Taylor disk is holomorphic at every point in its convergence region. -/
theorem differentiableAt_diagonalMomentDisk {X : Type*} (h : X → ℝ)
    (b : ℕ → Operator X) (t : ℝ) (z : ℂ)
    (hz : z - (t : ℂ) ∈ Metric.eball 0 (diagonalMomentSeries b).radius) :
    DifferentiableAt ℂ (diagonalMomentDisk h b t) z := by
  have hd := ((diagonalMomentSeries b).analyticOnNhd _ hz).differentiableAt
  exact ((differentiableAt_const (diagonalUnitary h t)).mul (hd.comp z
    (differentiableAt_id.sub_const (t : ℂ)))).mul_const (diagonalUnitary h (-t))

/-- Use the Taylor disk centered at the real part of each point. -/
def diagonalMomentExtension {X : Type*} (h : X → ℝ) (b : ℕ → Operator X)
    (z : ℂ) : Operator X := diagonalMomentDisk h b z.re z

/-- The assembled extension has the prescribed entries throughout the open strip. -/
theorem matrixEntry_diagonalMomentExtension {X : Type*} {h : X → ℝ} {a : Operator X}
    {b : ℕ → Operator X} (hm : IsDiagonalMomentSequence h a b) {A B : ℝ}
    (hB : 0 < B) (hb : ∀ k, ‖b k‖ ≤ A * B ^ k * k.factorial)
    {z : ℂ} (hz : |z.im| < B⁻¹) (x y : X) :
    matrixEntry (diagonalMomentExtension h b z) x y =
      Complex.exp (Complex.I * z * ((h x - h y : ℝ) : ℂ)) * matrixEntry a x y := by
  apply matrixEntry_diagonalMomentDisk hm
  apply diagonalMomentSeries_mem_ball b hB hb
  have hn : ‖z - (z.re : ℂ)‖ ≤ |z.im| := by
    simpa using Complex.norm_le_abs_re_add_abs_im (z - (z.re : ℂ))
  exact hn.trans_lt hz

/-- The assembled extension agrees with any Taylor disk wherever that disk converges. -/
theorem diagonalMomentExtension_eq_disk {X : Type*} {h : X → ℝ} {a : Operator X}
    {b : ℕ → Operator X} (hm : IsDiagonalMomentSequence h a b) {A B : ℝ}
    (hB : 0 < B) (hb : ∀ k, ‖b k‖ ≤ A * B ^ k * k.factorial)
    (t : ℝ) {z : ℂ} (hz : ‖z - (t : ℂ)‖ < B⁻¹) :
    diagonalMomentExtension h b z = diagonalMomentDisk h b t z := by
  have hi : |z.im| < B⁻¹ := (by
    simpa using Complex.abs_im_le_norm (z - (t : ℂ)) : |z.im| ≤ ‖z - (t : ℂ)‖).trans_lt hz
  exact operator_ext fun x y => (matrixEntry_diagonalMomentExtension hm hB hb hi x y).trans
    (matrixEntry_diagonalMomentDisk hm t z (diagonalMomentSeries_mem_ball b hB hb hz) x y).symm

/-- Local agreement with a fixed Taylor disk proves holomorphy of the assembled extension. -/
theorem differentiableAt_diagonalMomentExtension {X : Type*} {h : X → ℝ} {a : Operator X}
    {b : ℕ → Operator X} (hm : IsDiagonalMomentSequence h a b) {A B : ℝ}
    (hB : 0 < B) (hb : ∀ k, ‖b k‖ ≤ A * B ^ k * k.factorial)
    {z : ℂ} (hz : |z.im| < B⁻¹) : DifferentiableAt ℂ (diagonalMomentExtension h b) z := by
  have hn : ‖z - (z.re : ℂ)‖ < B⁻¹ :=
    (by simpa using Complex.norm_le_abs_re_add_abs_im (z - (z.re : ℂ)) :
      ‖z - (z.re : ℂ)‖ ≤ |z.im|).trans_lt hz
  apply (differentiableAt_diagonalMomentDisk h b z.re z
    (diagonalMomentSeries_mem_ball b hB hb hn)).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt (show Continuous (fun w : ℂ => ‖w - (z.re : ℂ)‖) by fun_prop)
    continuous_const).mem_nhds hn] with w hw
  exact diagonalMomentExtension_eq_disk hm hB hb z.re hw

/-- The moment extension is continuous on every smaller closed strip and holomorphic inside. -/
theorem diagonalMomentExtension_isStripExtension {X : Type*} {h : X → ℝ} {a : Operator X}
    {b : ℕ → Operator X} (hm : IsDiagonalMomentSequence h a b) {A B δ : ℝ}
    (hB : 0 < B) (hb : ∀ k, ‖b k‖ ≤ A * B ^ k * k.factorial) (hδ : δ < B⁻¹) :
    IsStripExtension h a δ (diagonalMomentExtension h b) where
  continuousOn z hz := (differentiableAt_diagonalMomentExtension hm hB hb
    ((abs_le.mpr hz).trans_lt hδ)).continuousAt.continuousWithinAt
  differentiableOn z hz := (differentiableAt_diagonalMomentExtension hm hB hb
    ((abs_lt.mpr hz).trans hδ)).differentiableWithinAt
  on_real t := by
    apply operator_ext
    intro x y
    rw [matrixEntry_diagonalMomentExtension hm hB hb (by simpa using inv_pos.mpr hB),
      matrixEntry_diagonalFlow]
    push_cast
    congr 2
    ring

/-- Lemma BandFromMoments: factorial commutator growth gives every width below 1/B. -/
theorem stripExtension_of_factorial_moments {X : Type*} {h : X → ℝ} {a : Operator X}
    {b : ℕ → Operator X} (hm : IsDiagonalMomentSequence h a b) {A B : ℝ}
    (hB : 0 < B) (hb : ∀ k, ‖b k‖ ≤ A * B ^ k * k.factorial) :
    (∃ δ : ℝ, 0 < δ ∧ ∃ F, IsStripExtension h a δ F) ∧
      ∀ δ : ℝ, 0 < δ → δ < B⁻¹ → ∃ F, IsStripExtension h a δ F := by
  have he (δ : ℝ) (hδ : δ < B⁻¹) : ∃ F, IsStripExtension h a δ F :=
    ⟨_, diagonalMomentExtension_isStripExtension hm hB hb hδ⟩
  exact ⟨⟨B⁻¹ / 2, half_pos (inv_pos.mpr hB), he _ (half_lt_self (inv_pos.mpr hB))⟩,
    fun δ _ hδ => he δ hδ⟩

end DynamicalCStarAlgebras
