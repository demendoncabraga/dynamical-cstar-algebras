import DynamicalCStarAlgebras.RoeAlgebra

noncomputable section

namespace DynamicalCStarAlgebras

universe u

/-- A continuous matrix coefficient functional on the operator algebra. -/
def matrixEntryCLM {X : Type u} (x y : X) : Operator X →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : X => ℂ) 2 x).comp
    (ContinuousLinearMap.apply ℂ (HilbertSpace X) (delta y))

theorem matrixEntryCLM_apply {X : Type u} (x y : X) (a : Operator X) :
    matrixEntryCLM x y a = matrixEntry a x y := rfl

/-- The extension is specified on the closed strip; values outside it are unrestricted. -/
structure IsStripExtension {X : Type u} (h : X → ℝ) (a : Operator X)
    (δ : ℝ) (F : ℂ → Operator X) : Prop where
  continuousOn : ContinuousOn F (Complex.im ⁻¹' Set.Icc (-δ) δ)
  differentiableOn : DifferentiableOn ℂ F (Complex.im ⁻¹' Set.Ioo (-δ) δ)
  on_real : ∀ t : ℝ, F t = diagonalFlow h t a

/-- Scalar identity theorem on a closed horizontal strip, including its boundary. -/
theorem eqOn_closedStrip {δ : ℝ} (hδ : 0 < δ) {f g : ℂ → ℂ}
    (hf : ContinuousOn f (Complex.im ⁻¹' Set.Icc (-δ) δ))
    (hg : ContinuousOn g (Complex.im ⁻¹' Set.Icc (-δ) δ))
    (hdf : DifferentiableOn ℂ f (Complex.im ⁻¹' Set.Ioo (-δ) δ))
    (hdg : DifferentiableOn ℂ g (Complex.im ⁻¹' Set.Ioo (-δ) δ))
    (he : ∀ t : ℝ, f t = g t) :
    Set.EqOn f g (Complex.im ⁻¹' Set.Icc (-δ) δ) := by
  have ho : IsOpen (Complex.im ⁻¹' Set.Ioo (-δ) δ) :=
    isOpen_Ioo.preimage Complex.continuous_im
  have hc : IsPreconnected (Complex.im ⁻¹' Set.Ioo (-δ) δ) :=
    ((convex_Ioo (-δ) δ).linear_preimage Complex.imLm).isPreconnected
  have hm : (0 : ℂ) ∈ closure (Complex.ofReal '' Set.Ioi (0 : ℝ)) := by
    simpa only [Complex.ofReal_zero] using mem_closure_image
      Complex.continuous_ofReal.continuousAt (show (0 : ℝ) ∈ closure (Set.Ioi 0) by simp)
  have hs : Complex.ofReal '' Set.Ioi (0 : ℝ) ⊆ {z | f z = g z} \ {0} :=
    fun z ⟨t, ht, hz⟩ => hz ▸ ⟨he t, fun hn =>
      (ne_of_gt ht) (Complex.ofReal_injective (hn : (t : ℂ) = (0 : ℝ)))⟩
  have hi : Set.EqOn f g (Complex.im ⁻¹' Set.Ioo (-δ) δ) :=
    (hdf.analyticOnNhd ho).eqOn_of_preconnected_of_mem_closure
      (hdg.analyticOnNhd ho) hc (by simpa using And.intro (neg_neg_of_pos hδ) hδ)
      (closure_mono hs hm)
  exact hi.of_subset_closure hf hg (fun _ hz => ⟨hz.1.le, hz.2.le⟩)
    (by rw [Complex.closure_preimage_im, closure_Ioo (ne_of_lt (neg_lt_self hδ))])

/-- Proposition Prop.xy.coordinates.ana.extension, including the boundary of the strip. -/
theorem IsStripExtension.matrixEntry_eq {X : Type u} {h : X → ℝ} {a : Operator X}
    {δ : ℝ} {F : ℂ → Operator X} (hF : IsStripExtension h a δ F) (hδ : 0 < δ)
    {z : ℂ} (hz : |z.im| ≤ δ) (x y : X) :
    matrixEntry (F z) x y =
      Complex.exp (Complex.I * z * ((h x - h y : ℝ) : ℂ)) * matrixEntry a x y := by
  have hdg : Differentiable ℂ (fun z : ℂ =>
      Complex.exp (Complex.I * z * ((h x - h y : ℝ) : ℂ)) * matrixEntry a x y) :=
    (Complex.differentiable_exp.comp
      (((differentiable_const Complex.I).mul differentiable_id).mul_const _)).mul_const _
  refine eqOn_closedStrip hδ
    ((matrixEntryCLM x y).continuous.comp_continuousOn hF.continuousOn)
    hdg.continuous.continuousOn
    ((matrixEntryCLM x y).differentiable.comp_differentiableOn hF.differentiableOn)
    hdg.differentiableOn ?_ (abs_le.mp hz)
  intro t
  simp only [Function.comp_apply, matrixEntryCLM_apply, hF.on_real,
    matrixEntry_diagonalFlow, Complex.ofReal_mul, mul_assoc, mul_comm]


/-- Analytic extensions of one diagonal orbit agree everywhere on their common closed strip. -/
theorem IsStripExtension.unique {X : Type u} {h : X → ℝ} {a : Operator X}
    {δ : ℝ} {F G : ℂ → Operator X} (hF : IsStripExtension h a δ F)
    (hG : IsStripExtension h a δ G) (hδ : 0 < δ) {z : ℂ} (hz : |z.im| ≤ δ) :
    F z = G z :=
  operator_ext fun x y => (hF.matrixEntry_eq hδ hz x y).trans (hG.matrixEntry_eq hδ hz x y).symm

end DynamicalCStarAlgebras
