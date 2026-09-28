import DynamicalCStarAlgebras.StripAnalyticPoints

noncomputable section

namespace DynamicalCStarAlgebras

/-- A strip extension restricts to every narrower strip. -/
theorem IsStripExtension.restrict {X : Type*} {h : X → ℝ} {a : Operator X}
    {δ ε : ℝ} {F : ℂ → Operator X} (hF : IsStripExtension h a δ F) (he : ε ≤ δ) :
    IsStripExtension h a ε F where
  continuousOn := hF.continuousOn.mono (fun _ hz =>
    ⟨(neg_le_neg he).trans hz.1, hz.2.trans he⟩)
  differentiableOn := hF.differentiableOn.mono (fun _ hz =>
    ⟨(neg_le_neg he).trans_lt hz.1, hz.2.trans_le he⟩)
  on_real := hF.on_real

/-- Adding two extensions on one strip extends the sum. -/
theorem IsStripExtension.add {X : Type*} {h : X → ℝ} {a b : Operator X}
    {δ : ℝ} {F G : ℂ → Operator X}
    (hF : IsStripExtension h a δ F) (hG : IsStripExtension h b δ G) :
    IsStripExtension h (a + b) δ (fun z => F z + G z) where
  continuousOn := hF.continuousOn.add hG.continuousOn
  differentiableOn := hF.differentiableOn.add hG.differentiableOn
  on_real t := by simp only [hF.on_real, hG.on_real, ← diagonalFlowEquiv_apply, map_add]

/-- Multiplying two extensions on one strip extends the product. -/
theorem IsStripExtension.mul {X : Type*} {h : X → ℝ} {a b : Operator X}
    {δ : ℝ} {F G : ℂ → Operator X}
    (hF : IsStripExtension h a δ F) (hG : IsStripExtension h b δ G) :
    IsStripExtension h (a * b) δ (fun z => F z * G z) where
  continuousOn := hF.continuousOn.mul hG.continuousOn
  differentiableOn := hF.differentiableOn.mul hG.differentiableOn
  on_real t := by simp only [hF.on_real, hG.on_real, ← diagonalFlowEquiv_apply, map_mul]

/-- Conjugate reflection of a strip extension extends the adjoint. -/
theorem IsStripExtension.starExtension {X : Type*} {h : X → ℝ} {a : Operator X}
    {δ : ℝ} {F : ℂ → Operator X} (hF : IsStripExtension h a δ F) :
    IsStripExtension h (star a) δ (fun z => star (F (star z))) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hF.continuousOn.star.comp continuous_star.continuousOn
      (fun z hz => by simpa only [Set.mem_preimage, Set.mem_Icc, Complex.star_def, Complex.conj_im] using
        (show -δ ≤ -z.im ∧ -z.im ≤ δ from ⟨by linarith [hz.2], by linarith [hz.1]⟩))
  · intro z hz
    have hs : star z ∈ Complex.im ⁻¹' Set.Ioo (-δ) δ := by
      simp only [Set.mem_preimage, Set.mem_Ioo, Complex.star_def, Complex.conj_im]
      exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
    have hd := (hF.differentiableOn (star z) hs).differentiableAt
      ((isOpen_Ioo.preimage Complex.continuous_im).mem_nhds hs)
    simpa only [star_star, Function.comp_apply] using! hd.star_star.differentiableWithinAt
  · intro t
    simp only [Complex.star_def, Complex.conj_ofReal, hF.on_real,
      ← diagonalFlowEquiv_apply, map_star]

/-- Scalar operators admit constant strip extensions. -/
theorem exists_stripExtension_algebraMap {X : Type*} (h : X → ℝ) (c : ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ F, IsStripExtension h (algebraMap ℂ (Operator X) c) δ F := by
  obtain ⟨F, hF, _⟩ := isEntireExponentialType_algebraMap h c
  exact ⟨1, zero_lt_one, F, hF.onStrip 1⟩

/-- The common strip-analytic operators form a unital complex star-subalgebra. -/
def coarseStripStarSubalgebra {X : Type*} (C : CoarseStructure X) :
    StarSubalgebra ℂ (Operator X) where
  carrier := {a | ∀ h : X → ℝ, IsCoarseReal C h →
    ∃ δ : ℝ, 0 < δ ∧ ∃ F, IsStripExtension h a δ F}
  zero_mem' h _ := by simpa only [map_zero] using! exists_stripExtension_algebraMap h 0
  one_mem' h _ := by simpa only [map_one] using! exists_stripExtension_algebraMap h 1
  add_mem' ha hb h hh := by
    obtain ⟨δ, hδ, F, hF⟩ := ha h hh
    obtain ⟨ε, hε, G, hG⟩ := hb h hh
    exact ⟨min δ ε, lt_min hδ hε, _,
      (hF.restrict (min_le_left δ ε)).add (hG.restrict (min_le_right δ ε))⟩
  mul_mem' ha hb h hh := by
    obtain ⟨δ, hδ, F, hF⟩ := ha h hh
    obtain ⟨ε, hε, G, hG⟩ := hb h hh
    exact ⟨min δ ε, lt_min hδ hε, _,
      (hF.restrict (min_le_left δ ε)).mul (hG.restrict (min_le_right δ ε))⟩
  star_mem' ha h hh := by
    obtain ⟨δ, hδ, F, hF⟩ := ha h hh
    exact ⟨δ, hδ, _, hF.starExtension⟩
  algebraMap_mem' c h _ := exists_stripExtension_algebraMap h c

/-- The norm-closed strip algebra of Definition Defi.AP_band. -/
def stripAnalyticPointsStarSubalgebra {X : Type*} (C : CoarseStructure X) :
    StarSubalgebra ℂ (Operator X) := (coarseStripStarSubalgebra C).topologicalClosure

/-- The closed unital complex star-subalgebra assertion following Defi.AP_band. -/
theorem stripAnalyticPoints_algebra {X : Type*} (C : CoarseStructure X) :
    (stripAnalyticPointsStarSubalgebra C : Set (Operator X)) = stripAnalyticPoints C ∧
      IsClosed (stripAnalyticPointsStarSubalgebra C : Set (Operator X)) :=
  ⟨rfl, (coarseStripStarSubalgebra C).isClosed_topologicalClosure⟩

end DynamicalCStarAlgebras
