import DynamicalCStarAlgebras.StripStructure

namespace DynamicalCStarAlgebras

/-- Analyticity on a specified positive-width closed strip. -/
def IsStripAnalyticAt {X : Type*} (h : X → ℝ) (a : Operator X) (δ : ℝ) : Prop :=
  0 < δ ∧ ∃ F : ℂ → Operator X, IsStripExtension h a δ F

/-- Analyticity on some positive-width strip, with width depending on the orbit. -/
def IsStripAnalytic {X : Type*} (h : X → ℝ) (a : Operator X) : Prop :=
  ∃ δ : ℝ, IsStripAnalyticAt h a δ

/-- Exponential type on a finite strip, with strictly positive growth constants. -/
def IsStripExponentialType {X : Type*} (h : X → ℝ) (a : Operator X) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ F : ℂ → Operator X, IsStripExtension h a δ F ∧
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 0 < K ∧
      ∀ z : ℂ, |z.im| ≤ δ → ‖F z‖ ≤ C * Real.exp (K * |z.im|)

/-- On a finite strip, the norm maximum supplies the exponential-type bound
in Definition Def.BandAnalytic.functions. The entire version is stronger. -/
theorem isStripExponentialType_iff_stripAnalytic {X : Type*} (h : X → ℝ) (a : Operator X) :
    IsStripExponentialType h a ↔ IsStripAnalytic h a := by
  constructor
  · rintro ⟨δ, hδ, F, hF, _⟩
    exact ⟨δ, hδ, F, hF⟩
  · rintro ⟨δ, hδ, F, hF⟩
    obtain ⟨s, _, hs⟩ := hF.strip_maximum hδ
    refine ⟨δ, hδ, F, hF, ‖F ((s : ℂ) * Complex.I)‖ + 1, by positivity, 1, by positivity, ?_⟩
    intro z hz
    have he : 1 ≤ Real.exp (1 * |z.im|) := Real.one_le_exp (by positivity)
    nlinarith [hs z hz, norm_nonneg (F ((s : ℂ) * Complex.I))]

end DynamicalCStarAlgebras
