import DynamicalCStarAlgebras.ExponentialProjectionBounds
import DynamicalCStarAlgebras.BlockNorms

noncomputable section

namespace DynamicalCStarAlgebras

/-- Equation Eq.UnifExpDecay for an ambient block-diagonal contraction. The
source good-subspace data remain explicit; their existence is a separate result. -/
theorem CoarseGraphUnion.good_projection_block_exponential_bound
    {X : Type*} [PseudoMetricSpace X] (D : CoarseGraphUnion X)
    (a : Operator X) (ha : ‖a‖ ≤ 1)
    (hblock : ∀ x y, D.component x ≠ D.component y → matrixEntry a x y = 0)
    {γ C : ℝ} (hγ : 0 < γ) (hC : 1 ≤ C)
    (hExp : ∀ n, letI := @Fintype.ofFinite {x : X // D.component x = n} (D.finite n)
      HasVertexExpansion (D.graph n) γ)
    (hdata : ∀ n,
      let b := componentOperator (fun x : {x : X // D.component x = n} => (x : X))
        Subtype.val_injective a
      ∃ (m : ℕ) (p : Operator {x : X // D.component x = n}),
        IsSelfAdjoint p ∧ (Nat.card {x : X // D.component x = n} : ℝ) ^ (1 / 4 : ℝ) ≤ m ∧
        p * b = b ∧ b * p = b ∧
        ∀ (S : Finset {x : X // D.component x = n}) (δ : ℝ),
          1 / (m : ℝ) ≤ δ → δ ≤ 1 / 2 →
          (S.card : ℝ) ≤ δ * Nat.card {x : X // D.component x = n} →
          ‖coordinateProjection (S : Set {x : X // D.component x = n}) * p‖ ≤
            C * Real.sqrt (δ * Real.log (1 / δ))) :
    ∃ κ : ℝ, 1 < κ ∧
      (∀ r : ℝ, 0 ≤ r → quasiLocalModulus a r ≤ 2 * C * κ ^ (-r / 24)) ∧
      HasExponentialDecay a := by
  let : ∀ n, Fintype {x : X // D.component x = n} :=
    fun n => @Fintype.ofFinite _ (D.finite n)
  obtain ⟨κ, hκ, hsep⟩ := vertex_expansion_uniform_separation hγ
  have hC0 : 0 ≤ C := by linarith
  have hmod (r : ℝ) (hr : 0 ≤ r) : quasiLocalModulus a r ≤ 2 * C * κ ^ (-r / 24) := by
    apply quasiLocalModulus_le_of_component_bounds D.component a hblock
      (by positivity)
    intro n
    obtain ⟨m, p, hp, hm, hleft, hright, hgood⟩ := hdata n
    apply finite_good_projection_modulus _ p hp ((norm_componentOperator_le _ _ a).trans ha)
      hleft hright hC hκ (by simpa only [Nat.card_eq_fintype_card] using hm)
      (by simpa only [Nat.card_eq_fintype_card] using hgood)
    intro A B s hs hAB
    exact hsep (D.graph n) (hExp n) A B s hs (fun x hx y hy => by
      rw [← D.dist_eq n]
      exact hAB x hx y hy)
    exact hr
  refine ⟨κ, hκ, hmod, Real.log κ / 24, div_pos (Real.log_pos hκ) (by norm_num),
    2 * C, by linarith, fun r hr => ?_⟩
  have hid : κ ^ (-r / 24) = Real.exp (-(Real.log κ / 24) * r) := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < κ)]
    congr 1
    ring
  simpa only [hid] using hmod r hr

end DynamicalCStarAlgebras
