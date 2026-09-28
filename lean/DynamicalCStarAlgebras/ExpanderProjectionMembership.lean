import DynamicalCStarAlgebras.BlockNorms
import DynamicalCStarAlgebras.ExpanderProjectionDecay

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- The projections of Assumption.1 have polynomial decay on an expander union.
Zero components allow the prescribed finite initial segment to be omitted. -/
theorem CoarseGraphUnion.projection_hasPolynomialDecay
    {X : Type*} [PseudoMetricSpace X] (D : CoarseGraphUnion X)
    (p : Operator X) (hp : IsSelfAdjoint p)
    (hblock : ∀ x y, D.component x ≠ D.component y → matrixEntry p x y = 0)
    {γ α C : ℝ} (hγ : 0 < γ) (hα : 0 ≤ α) (hC : 0 < C)
    (hExp : ∀ n, letI := @Fintype.ofFinite {x : X // D.component x = n} (D.finite n)
      HasVertexExpansion (D.graph n) γ)
    (hdata : ∀ n,
      let q := componentOperator (fun x : {x : X // D.component x = n} => (x : X))
        Subtype.val_injective p
      q = 0 ∨ ∀ A : Finset {x : X // D.component x = n}, A.Nonempty →
        ‖coordinateProjection (A : Set {x : X // D.component x = n}) * q‖ ≤ C * Real.sqrt
          (1 / Real.log (Nat.card {x : X // D.component x = n}) ^ (2 * α) +
            (A.card : ℝ) / Nat.card {x : X // D.component x = n} *
              Real.log (Real.exp 1 * Nat.card {x : X // D.component x = n} / A.card))) :
    HasPolynomialDecay α p := by
  let : ∀ n, Fintype {x : X // D.component x = n} :=
    fun n => @Fintype.ofFinite _ (D.finite n)
  obtain ⟨κ, hκ, hsep⟩ := vertex_expansion_uniform_separation hγ
  apply polynomialDecay_of_expander_modulus_bound p (D := (Real.log κ / 2) ^ (-2 * α))
    hα hC (Real.rpow_nonneg (half_pos (Real.log_pos hκ)).le _) (half_pos (Real.log_pos hκ))
  intro r hr
  apply quasiLocalModulus_le_of_component_bounds D.component p hblock
    (mul_nonneg hC.le (Real.sqrt_nonneg _))
  intro n
  rcases hdata n with hz | hb
  · rw [hz]
    apply (quasiLocalModulus_le_iff _ _ _).mpr
    intro A B _
    simp only [mul_zero, zero_mul, norm_zero]
    positivity
  · apply expander_projection_modulus_bound (D.graph n) (D.dist_eq n)
      _ (componentOperator_selfAdjoint _ _ hp) hκ hα hC.le
      (hsep (D.graph n) (hExp n)) _ hr
    simpa only [Nat.card_eq_fintype_card] using hb

/-- `Prop.palpha.is.inQLalpha.exp`: the block projection specified in Assumption.1
belongs to the polynomial quasi-local algebra with its prescribed exponent. -/
theorem CoarseGraphUnion.projection_mem_polynomialQuasiLocal
    {X : Type*} [PseudoMetricSpace X] (D : CoarseGraphUnion X)
    (p : Operator X) (hp : IsSelfAdjoint p)
    (hblock : ∀ x y, D.component x ≠ D.component y → matrixEntry p x y = 0)
    {γ α C : ℝ} (hγ : 0 < γ) (hα : 0 < α) (hC : 0 < C)
    (hExp : ∀ n, letI := @Fintype.ofFinite {x : X // D.component x = n} (D.finite n)
      HasVertexExpansion (D.graph n) γ)
    (n₀ : ℕ)
    (hzero : ∀ n < n₀, componentOperator
      (fun x : {x : X // D.component x = n} => (x : X)) Subtype.val_injective p = 0)
    (hbound : ∀ n, n₀ ≤ n →
      let q := componentOperator (fun x : {x : X // D.component x = n} => (x : X))
        Subtype.val_injective p
      ∀ A : Finset {x : X // D.component x = n}, A.Nonempty →
        ‖coordinateProjection (A : Set {x : X // D.component x = n}) * q‖ ≤ C * Real.sqrt
          (1 / Real.log (Nat.card {x : X // D.component x = n}) ^ (2 * α) +
            (A.card : ℝ) / Nat.card {x : X // D.component x = n} *
              Real.log (Real.exp 1 * Nat.card {x : X // D.component x = n} / A.card))) :
    p ∈ polynomialQuasiLocal α := by
  apply subset_closure
  apply D.projection_hasPolynomialDecay p hp hblock hγ hα.le hC hExp
  intro n
  by_cases hn : n < n₀
  · exact Or.inl (hzero n hn)
  · exact Or.inr (hbound n (Nat.le_of_not_gt hn))

end DynamicalCStarAlgebras
