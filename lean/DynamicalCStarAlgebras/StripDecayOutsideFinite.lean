import DynamicalCStarAlgebras.LipschitzGluing

noncomputable section

namespace DynamicalCStarAlgebras

/-- The uniform weighted gluing bound gives exponential decay away from a finite region. -/
theorem strip_decay_outside_finite {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) (x₀ : X) (a : Operator X)
    (ha : ∀ h : X → ℝ, LipschitzWith 1 h →
      ∃ δ : ℝ, 0 < δ ∧ ∃ F, IsStripExtension h a δ F) :
    ∃ (N : ℝ) (G : Set X), 0 < N ∧ G.Finite ∧
      ∀ (r : ℝ) (A B : Set X), A ⊆ Gᶜ → B ⊆ Gᶜ →
        (∀ x ∈ A, ∀ y ∈ B, r ≤ dist x y) →
        ‖coordinateProjection A * a * coordinateProjection B‖ ≤
          N * Real.exp (-(N⁻¹ / 2) * r) := by
  obtain ⟨n, G, hG, hglue⟩ := exists_uniform_weighted_gluing hX x₀ a ha
  have hN : 0 < (n : ℝ) + 1 := by positivity
  refine ⟨(n : ℝ) + 1, G, hN, hG, fun r A B hAG hBG hAB => ?_⟩
  rcases Set.eq_empty_or_nonempty B with rfl | hB
  · rw [compression_eq_zero_of_entries a A ∅ (fun _ _ _ hy => hy.elim), norm_zero]
    positivity
  · obtain ⟨f, c, hf, hbound, he⟩ := hglue (fun x => Metric.infDist x B)
      (Metric.lipschitz_infDist_pt B)
    obtain ⟨b, hb, hentries⟩ := (hasWeightedOperatorBound_iff a f _ hN.le).mp hbound
    have hlow : ∀ x ∈ A, r / 2 + c ≤ f x := by
      intro x hx
      rw [he x (hAG hx)]
      have hd := (Metric.le_infDist hB).mpr (fun y hy => hAB x hx y hy)
      linarith
    have hupp : ∀ y ∈ B, f y ≤ c := by
      intro y hy
      simp [he y (hBG hy), Metric.infDist_zero_of_mem hy]
    have hg := gapEstimate_of_bounds f (inv_nonneg.mpr hN.le) a b hentries
      A B (r / 2 + c) c hlow hupp
    have heq : -((n : ℝ) + 1)⁻¹ * (r / 2 + c - c) =
        -(((n : ℝ) + 1)⁻¹ / 2) * r := by ring
    simpa only [heq, mul_comm] using
      hg.trans (mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _))

end DynamicalCStarAlgebras
