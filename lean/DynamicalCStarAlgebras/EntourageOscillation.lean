import DynamicalCStarAlgebras.CosineSmoothingEstimate

noncomputable section
namespace DynamicalCStarAlgebras

/-- Real oscillation on a bounded-variation entourage; adjoining zero gives
zero for an empty entourage. Only its bounded-variation use is asserted below. -/
def entourageOscillation {X : Type*} (h : X → ℝ) (E : Set (X × X)) : ℝ :=
  sSup (insert 0 {r | ∃ p ∈ E, r = |h p.1 - h p.2|})

lemma entourageOscillation_bddAbove {X : Type*} {h : X → ℝ} {E : Set (X × X)}
    (hE : BoundedVariation h E) :
    BddAbove (insert 0 {r | ∃ p ∈ E, r = |h p.1 - h p.2|}) := by
  obtain ⟨R, hR⟩ := hE
  refine ⟨max R 0, ?_⟩
  rintro r (rfl | ⟨p, hp, rfl⟩)
  · exact le_max_right R 0
  · simpa only [Real.dist_eq] using (hR p hp).trans (le_max_left R 0)

lemma entourageOscillation_nonneg {X : Type*} {h : X → ℝ} {E : Set (X × X)}
    (hE : BoundedVariation h E) : 0 ≤ entourageOscillation h E :=
  le_csSup (entourageOscillation_bddAbove hE) (Set.mem_insert 0 _)

lemma abs_sub_le_entourageOscillation {X : Type*} {h : X → ℝ} {E : Set (X × X)}
    (hE : BoundedVariation h E) {p : X × X} (hp : p ∈ E) :
    |h p.1 - h p.2| ≤ entourageOscillation h E :=
  le_csSup (entourageOscillation_bddAbove hE) (Set.mem_insert_of_mem _ ⟨p, hp, rfl⟩)

/-- Lemma lem:smoothing, with the source oscillation and exact error constants.
The construction also works for delta>1, though the source only asks for delta≤1. -/
theorem quasiLocal_smoothing {X : Type*} (C : CoarseStructure X) (h : X → ℝ)
    (hh : IsCoarseReal C h) {ε δ s : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (_hδone : δ ≤ 1) (E : Set (X × X)) (hE : E ∈ C.controlled)
    (a : Operator X) (ha : IsQuasiLocalAt a ε E)
    (hs : 2 * Real.pi * entourageOscillation h E / δ < s) :
    ∃ b : Operator X,
      (∀ x y, s < |h x - h y| → matrixEntry b x y = 0) ∧
      ‖a - b‖ ≤ 16 * δ * ‖a‖ + 8 * δ⁻¹ * ε := by
  have hB := hh E hE
  have hzero := entourageOscillation_nonneg hB
  have hlt : entourageOscillation h E < s * δ / (2 * Real.pi) := by
    apply (lt_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    have hh := (div_lt_iff₀ hδ).mp hs
    nlinarith
  obtain ⟨ω, hωlo, hωhi⟩ := exists_between hlt
  have hω : 0 < ω := hzero.trans_lt hωlo
  have hL : 0 < Real.pi * ω / δ := by positivity
  refine ⟨cosineSmoothing h (Real.pi * ω / δ) a, ?_, ?_⟩
  · intro x y hxy
    apply (cosineSmoothing_spec h hL a).2.2 x y
    have hωs := (lt_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hωhi
    have hLs : 2 * (Real.pi * ω / δ) < s := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hδ).mpr
      nlinarith
    exact hLs.trans hxy
  · exact cosineSmoothing_error_bound h hω hδ hε.le a ha
      (fun p hp => (abs_sub_le_entourageOscillation hB hp).trans hωlo.le)

end DynamicalCStarAlgebras
