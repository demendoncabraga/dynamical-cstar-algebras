import DynamicalCStarAlgebras.QuasiLocalCharacterization

noncomputable section

namespace DynamicalCStarAlgebras

/-- Horizontal translation of a strip extension agrees with the original isometric flow. -/
theorem IsStripExtension.translate {X : Type*} {h : X → ℝ} {a : Operator X}
    {δ : ℝ} {F : ℂ → Operator X} (hF : IsStripExtension h a δ F) (hδ : 0 < δ)
    (t s : ℝ) (hs : |s| ≤ δ) :
    F ((t : ℂ) + (s : ℂ) * Complex.I) = diagonalFlow h t (F ((s : ℂ) * Complex.I)) := by
  refine operator_ext fun x y => ?_
  rw [hF.matrixEntry_eq hδ (by simpa using hs), matrixEntry_diagonalFlow,
    hF.matrixEntry_eq hδ (by simpa using hs), ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The norm on a strip depends only on the imaginary coordinate. -/
theorem IsStripExtension.norm_eq_imaginary {X : Type*} {h : X → ℝ} {a : Operator X}
    {δ : ℝ} {F : ℂ → Operator X} (hF : IsStripExtension h a δ F) (hδ : 0 < δ)
    {z : ℂ} (hz : |z.im| ≤ δ) : ‖F z‖ = ‖F ((z.im : ℂ) * Complex.I)‖ := by
  simpa only [Complex.re_add_im, diagonalFlow_norm] using
    congrArg norm (hF.translate hδ z.re z.im hz)

/-- The global strip norm has a finite maximum on the compact imaginary segment. -/
theorem IsStripExtension.strip_maximum {X : Type*} {h : X → ℝ} {a : Operator X}
    {δ : ℝ} {F : ℂ → Operator X} (hF : IsStripExtension h a δ F) (hδ : 0 < δ) :
    ∃ s ∈ Set.Icc (-δ) δ, ∀ z : ℂ, |z.im| ≤ δ →
      ‖F z‖ ≤ ‖F ((s : ℂ) * Complex.I)‖ := by
  have hc : ContinuousOn (fun s : ℝ => ‖F ((s : ℂ) * Complex.I)‖) (Set.Icc (-δ) δ) :=
    hF.continuousOn.norm.comp (by fun_prop) (fun s hs => by simpa using hs)
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by linarith : -δ ≤ δ)) hc
  exact ⟨s, hs, fun z hz => (hF.norm_eq_imaginary hδ hz).trans_le (hmax (abs_le.mp hz))⟩

/-- The supremum over the whole closed strip equals an attained imaginary-segment value. -/
theorem IsStripExtension.strip_norm_supremum {X : Type*} {h : X → ℝ} {a : Operator X}
    {δ : ℝ} {F : ℂ → Operator X} (hF : IsStripExtension h a δ F) (hδ : 0 < δ) :
    ∃ s ∈ Set.Icc (-δ) δ,
      sSup ((fun z => ‖F z‖) '' {z : ℂ | |z.im| ≤ δ}) = ‖F ((s : ℂ) * Complex.I)‖ := by
  obtain ⟨s, hs, hmax⟩ := hF.strip_maximum hδ
  have hm : ‖F ((s : ℂ) * Complex.I)‖ ∈
      (fun z => ‖F z‖) '' {z : ℂ | |z.im| ≤ δ} :=
    ⟨_, by simpa using abs_le.mpr hs, rfl⟩
  have hb : ∀ r ∈ (fun z => ‖F z‖) '' {z : ℂ | |z.im| ≤ δ},
      r ≤ ‖F ((s : ℂ) * Complex.I)‖ := fun r ⟨z, hz, he⟩ => he ▸ hmax z hz
  exact ⟨s, hs, le_antisymm (csSup_le ⟨_, hm⟩ hb) (le_csSup ⟨_, hb⟩ hm)⟩

end DynamicalCStarAlgebras
