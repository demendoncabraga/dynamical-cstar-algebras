import DynamicalCStarAlgebras.StripFiniteRows

noncomputable section

namespace DynamicalCStarAlgebras

/-- Restricting rows preserves an exponential modulus bound with the same constants. -/
theorem HasExponentialDecay.coordinateProjection_mul {X : Type*} [PseudoMetricSpace X]
    {a : Operator X} (ha : HasExponentialDecay a) (S : Set X) :
    HasExponentialDecay (coordinateProjection S * a) := by
  obtain ⟨c, hc, M, hM, haM⟩ := ha
  refine ⟨c, hc, M, hM, fun r hr => ?_⟩
  refine (quasiLocalModulus_le_iff _ _ _).mpr fun A B hAB => ?_
  rw [← mul_assoc, coordinateProjection_mul_inter]
  exact (quasiLocalModulus_le_iff _ _ _).mp (haM r hr) (A ∩ S) B
    (fun x hx y hy => hAB x hx.1 y hy)

/-- Analyticity on a strip for every 1-Lipschitz height forces exponential decay. -/
theorem strip_analytic_hasExponentialDecay {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) (a : Operator X)
    (ha : ∀ h : X → ℝ, LipschitzWith 1 h →
      ∃ δ : ℝ, 0 < δ ∧ ∃ F, IsStripExtension h a δ F) :
    HasExponentialDecay a := by
  cases isEmpty_or_nonempty X with
  | inl h =>
    have he : a = 0 := operator_ext (fun x _ => isEmptyElim x)
    simpa only [he] using! (exponentialDecayStarSubalgebra (X := X)).zero_mem
  | inr h =>
    obtain ⟨x₀⟩ := h
    obtain ⟨N, G, hN, hG, hb⟩ := strip_decay_outside_finite hX x₀ a ha
    have hbulk : HasExponentialDecay (coordinateProjection Gᶜ * a * coordinateProjection Gᶜ) := by
      refine ⟨N⁻¹ / 2, half_pos (inv_pos.mpr hN), N, hN, fun r hr => ?_⟩
      refine (quasiLocalModulus_le_iff _ _ _).mpr fun A B hAB => ?_
      rw [compression_remove_buffer]
      exact hb r (A \ G) (B \ G) (fun _ hx => hx.2) (fun _ hy => hy.2)
        (fun x hx y hy => hAB x hx.1 y hy.1)
    have hcomp : coordinateProjection Gᶜ = 1 - coordinateProjection G := by
      apply eq_sub_iff_add_eq.mpr
      rw [add_comm, coordinateProjection_add_compl]
    have he : a = coordinateProjection Gᶜ * a * coordinateProjection Gᶜ +
        coordinateProjection G * a + coordinateProjection Gᶜ * (a * coordinateProjection G) := by
      rw [hcomp]
      noncomm_ring
    exact he.symm ▸ (hbulk.add (strip_finite_rows_decay a hG ha)).add
      ((strip_finite_columns_decay a hG ha).coordinateProjection_mul Gᶜ)

end DynamicalCStarAlgebras
