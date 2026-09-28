import DynamicalCStarAlgebras.PolynomialNonmembership

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- The logarithmic diameter estimate gives the polynomial term in `eq:diam`. -/
lemma inverse_log_power_le_radius {N κ r α : ℝ} (hκ : 1 < κ) (hr : 0 < r)
    (hα : 0 ≤ α) (hdiam : r ≤ 2 * Real.log N / Real.log κ) :
    1 / Real.log N ^ (2 * α) ≤
      (Real.log κ / 2) ^ (-2 * α) * r ^ (-2 * α) := by
  have hc : 0 < Real.log κ / 2 := half_pos (Real.log_pos hκ)
  have hlower : (Real.log κ / 2) * r ≤ Real.log N := by
    have h := (le_div_iff₀ (Real.log_pos hκ)).mp hdiam
    linarith
  have hlog : 0 < Real.log N := (mul_pos hc hr).trans_le hlower
  calc
    _ = Real.log N ^ (-2 * α) := by
      rw [show -2 * α = -(2 * α) by ring, Real.rpow_neg hlog.le, one_div]
    _ ≤ ((Real.log κ / 2) * r) ^ (-2 * α) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos hc hr) hlower (by linarith)
    _ = _ := Real.mul_rpow hc.le hr.le

/-- The finite-component compression estimate in the proof of
`Prop.palpha.is.inQLalpha.exp`, uniformly in the graph size. -/
theorem expander_projection_compression_bound {X : Type*} [Fintype X]
    (G : SimpleGraph X) (p : Operator X) (hp : IsSelfAdjoint p)
    {κ α C : ℝ} (hκ : 1 < κ) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hsep : ∀ (A B : Finset X) (r : ℝ), 0 ≤ r →
      (∀ a ∈ A, ∀ b ∈ B, r ≤ (G.dist a b : ℝ)) →
      min ((A.card : ℝ) / Fintype.card X) ((B.card : ℝ) / Fintype.card X) ≤ κ ^ (-r / 2))
    (hbound : ∀ A : Finset X, A.Nonempty →
      ‖coordinateProjection (A : Set X) * p‖ ≤ C * Real.sqrt
        (1 / Real.log (Fintype.card X) ^ (2 * α) +
          (A.card : ℝ) / Fintype.card X *
            Real.log (Real.exp 1 * Fintype.card X / A.card)))
    (A B : Finset X) (hA : A.Nonempty) (hB : B.Nonempty)
    {r : ℝ} (hr : 0 < r) (hAB : ∀ a ∈ A, ∀ b ∈ B, r ≤ (G.dist a b : ℝ)) :
    ‖coordinateProjection (A : Set X) * p * coordinateProjection (B : Set X)‖ ≤
      C * Real.sqrt ((Real.log κ / 2) ^ (-2 * α) * r ^ (-2 * α) +
        (1 + (Real.log κ / 2) * r) * Real.exp (-(Real.log κ / 2) * r)) := by
  have hN : (0 : ℝ) < Fintype.card X := by
    obtain ⟨x, _⟩ := hA
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨x⟩
  have hdiam : r ≤ 2 * Real.log (Fintype.card X) / Real.log κ := by
    obtain ⟨x, hx⟩ := hA
    obtain ⟨y, hy⟩ := hB
    exact (hAB x hx y hy).trans (graph_dist_le_log_card G hκ hsep x y)
  have hpoly := inverse_log_power_le_radius hκ hr hα hdiam
  have hside (S : Finset X) (hS : S.Nonempty)
      (hs : (S.card : ℝ) / Fintype.card X ≤ κ ^ (-r / 2)) :
      ‖coordinateProjection (S : Set X) * p‖ ≤
        C * Real.sqrt ((Real.log κ / 2) ^ (-2 * α) * r ^ (-2 * α) +
          (1 + (Real.log κ / 2) * r) * Real.exp (-(Real.log κ / 2) * r)) := by
    have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    have he := entropy_mass_of_exponential_bound hκ hr.le (div_pos hcard hN) hs
    rw [div_div_eq_mul_div] at he
    have hexp : κ ^ (-r / 2) = Real.exp (-(Real.log κ / 2) * r) := by
      rw [Real.rpow_def_of_pos (by linarith : 0 < κ)]
      congr 1
      ring
    rw [hexp, show 1 + r * Real.log κ / 2 = 1 + (Real.log κ / 2) * r by ring] at he
    exact (hbound S hS).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (add_le_add hpoly he)) hC)
  have hmin := hsep A B r hr.le hAB
  rcases min_le_iff.mp hmin with h | h
  · exact ((norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _)
      (coordinateProjection_norm_le (B : Set X)))).trans (hside A hA h)
  · rw [← hp.star_eq, compression_star_norm]
    exact ((norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _)
      (coordinateProjection_norm_le (A : Set X)))).trans (hside B hB h)

/-- Uniform finite-component quasi-locality estimate in the expander projection proof. -/
theorem expander_projection_modulus_bound {X : Type*} [Fintype X] [PseudoMetricSpace X]
    (G : SimpleGraph X) (hdist : ∀ x y, dist x y = (G.dist x y : ℝ))
    (p : Operator X) (hp : IsSelfAdjoint p)
    {κ α C : ℝ} (hκ : 1 < κ) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hsep : ∀ (A B : Finset X) (r : ℝ), 0 ≤ r →
      (∀ a ∈ A, ∀ b ∈ B, r ≤ (G.dist a b : ℝ)) →
      min ((A.card : ℝ) / Fintype.card X) ((B.card : ℝ) / Fintype.card X) ≤ κ ^ (-r / 2))
    (hbound : ∀ A : Finset X, A.Nonempty →
      ‖coordinateProjection (A : Set X) * p‖ ≤ C * Real.sqrt
        (1 / Real.log (Fintype.card X) ^ (2 * α) +
          (A.card : ℝ) / Fintype.card X *
            Real.log (Real.exp 1 * Fintype.card X / A.card)))
    {r : ℝ} (hr : 0 < r) :
    quasiLocalModulus p r ≤
      C * Real.sqrt ((Real.log κ / 2) ^ (-2 * α) * r ^ (-2 * α) +
        (1 + (Real.log κ / 2) * r) * Real.exp (-(Real.log κ / 2) * r)) := by
  apply (quasiLocalModulus_le_iff _ _ _).mpr
  intro A B hAB
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · simpa only [Set.coe_toFinset] using
        expander_projection_compression_bound G p hp hκ hα hC hsep hbound
          A.toFinset B.toFinset (by simpa using hA) (by simpa using hB) hr
          (by
            intro a ha b hb
            rw [← hdist]
            exact hAB a (by simpa using ha) b (by simpa using hb))
    · have he : coordinateProjection A * p * coordinateProjection B = 0 := by
        apply operator_ext
        intro x y
        rw [matrixEntry_compression]
        simp [Set.not_nonempty_iff_eq_empty.mp hB, matrixEntry]
      rw [he, norm_zero]
      exact mul_nonneg hC (Real.sqrt_nonneg _)
  · have he : coordinateProjection A * p * coordinateProjection B = 0 := by
      apply operator_ext
      intro x y
      rw [matrixEntry_compression]
      simp [Set.not_nonempty_iff_eq_empty.mp hA, matrixEntry]
    rw [he, norm_zero]
    exact mul_nonneg hC (Real.sqrt_nonneg _)

end DynamicalCStarAlgebras
