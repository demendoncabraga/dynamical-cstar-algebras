import DynamicalCStarAlgebras.ExpanderSeparation

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

/-- The separation estimate bounds each distance by the logarithm of the graph size. -/
theorem graph_dist_le_log_card {X : Type*} [Fintype X] (G : SimpleGraph X)
    {κ : ℝ} (hκ : 1 < κ)
    (hsep : ∀ (A B : Finset X) (r : ℝ), 0 ≤ r →
      (∀ a ∈ A, ∀ b ∈ B, r ≤ (G.dist a b : ℝ)) →
      min ((A.card : ℝ) / Fintype.card X) ((B.card : ℝ) / Fintype.card X) ≤ κ ^ (-r / 2))
    (x y : X) :
    (G.dist x y : ℝ) ≤ 2 * Real.log (Fintype.card X) / Real.log κ := by
  have hN : (0 : ℝ) < Fintype.card X := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨x⟩)
  have hs := hsep {x} {y} (G.dist x y) (by positivity)
    (fun a ha b hb => by simpa only [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb]
      using (le_refl (G.dist x y : ℝ)))
  simp only [Finset.card_singleton, Nat.cast_one, min_self] at hs
  have hl := Real.log_le_log (one_div_pos.mpr hN) hs
  rw [Real.log_div one_ne_zero hN.ne', Real.log_one, zero_sub, Real.log_rpow (by linarith : 0 < κ)] at hl
  apply (le_div_iff₀ (Real.log_pos hκ)).mpr
  nlinarith

/-- Equation Eq.t.t.e.tb: the exact logarithmic diameter bound from the separation constant. -/
theorem graph_diameter_le_log_card {X : Type*} [Fintype X] (G : SimpleGraph X) (hc : G.Connected)
    {κ : ℝ} (hκ : 1 < κ)
    (hsep : ∀ (A B : Finset X) (r : ℝ), 0 ≤ r →
      (∀ a ∈ A, ∀ b ∈ B, r ≤ (G.dist a b : ℝ)) →
      min ((A.card : ℝ) / Fintype.card X) ((B.card : ℝ) / Fintype.card X) ≤ κ ^ (-r / 2)) :
    letI := connectedGraphMetric G hc
    Metric.diam (Set.univ : Set X) ≤ 2 * Real.log (Fintype.card X) / Real.log κ := by
  let inst := connectedGraphMetric G hc
  have hne : (Set.univ : Set X).Nonempty := hc.nonempty.elim fun x => ⟨x, Set.mem_univ x⟩
  apply Metric.diam_le_of_forall_dist_le_of_nonempty hne
  intro x _ y _
  exact graph_dist_le_log_card G hκ hsep x y

end DynamicalCStarAlgebras
