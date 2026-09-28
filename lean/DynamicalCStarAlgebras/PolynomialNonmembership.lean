import DynamicalCStarAlgebras.PolynomialApproximation
noncomputable section
open Filter Classical
namespace DynamicalCStarAlgebras

/-- Global polynomial-algebra membership contradicts the component rank and compression data. -/
theorem projection_not_mem_polynomialQuasiLocal {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) {Y : ℕ → Type*}
    [∀ n, Fintype (Y n)] [∀ n, PseudoMetricSpace (Y n)]
    (ι : ∀ n, Y n → X) (hinj : ∀ n, Function.Injective (ι n)) (hi : ∀ n, Isometry (ι n))
    (G : ∀ n, SimpleGraph (Y n)) (hconn : ∀ n, (G n).Connected)
    (hdist : ∀ n (x y : Y n), dist x y = ((G n).dist x y : ℝ))
    (hN : Tendsto (fun n => (Fintype.card (Y n) : ℝ)) atTop atTop)
    (p : Operator X) (hp : IsSelfAdjoint p) {α β C : ℝ} (hα : 0 < α) (hβ : α < β)
    (hdata : ∀ᶠ n in atTop,
      let q := componentOperator (ι n) (hinj n) p
      IsStarProjection q ∧ Module.finrank ℂ (LinearMap.range q.toLinearMap) =
        ⌊(Fintype.card (Y n) : ℝ) / Real.log (Fintype.card (Y n)) ^ (2 * α)⌋₊ ∧
      ∀ A : Finset (Y n), A.Nonempty →
        ‖coordinateProjection (A : Set (Y n)) * q‖ ≤ C * Real.sqrt
          (1 / Real.log (Fintype.card (Y n)) ^ (2 * α) +
            (A.card : ℝ) / Fintype.card (Y n) *
              Real.log (Real.exp 1 * Fintype.card (Y n) / A.card))) :
    p ∉ polynomialQuasiLocal β := by
  intro hmem
  obtain ⟨k, hk, hdeg⟩ := uniform_degree_of_isometric_graphs hX ι hinj hi G hdist
  apply component_approximation_obstruction G hconn hdist k hk hdeg hN
    (fun n => componentOperator (ι n) (hinj n) p) hα hβ hdata
  intro δ hδ
  obtain ⟨a, ha, hdecay, hap⟩ := exists_selfAdjoint_polynomial_approx hp (hα.trans hβ) hδ hmem
  obtain ⟨D, hD, hmod⟩ := hdecay
  refine ⟨fun n => componentOperator (ι n) (hinj n) a, D, hD, fun n => ?_⟩
  refine ⟨componentOperator_selfAdjoint _ _ ha, ?_, fun r hr => ?_⟩
  · rw [← componentOperator_sub]
    exact (norm_componentOperator_le _ _ _).trans hap
  · exact (quasiLocalModulus_componentOperator_le _ _ (hi n) a r).trans (hmod r hr)

/-- Thm.QLthetaDoesNotContainP in the setting of Assumption.1. Existence of
projections with these prescribed component estimates is a separate assertion. -/
theorem CoarseGraphUnion.projection_not_mem_polynomialQuasiLocal
    {X : Type*} [PseudoMetricSpace X] (D : CoarseGraphUnion X)
    (hX : UniformlyLocallyFinite X)
    (hN : Tendsto (fun n => (Nat.card {x : X // D.component x = n} : ℝ)) atTop atTop)
    (p : Operator X) (hp : IsSelfAdjoint p) {α β C : ℝ} (hα : 0 < α) (hβ : α < β)
    (hdata : ∀ᶠ n in atTop,
      let q := componentOperator (fun x : {x : X // D.component x = n} => (x : X))
        Subtype.val_injective p
      IsStarProjection q ∧ Module.finrank ℂ (LinearMap.range q.toLinearMap) =
        ⌊(Nat.card {x : X // D.component x = n} : ℝ) /
          Real.log (Nat.card {x : X // D.component x = n}) ^ (2 * α)⌋₊ ∧
      ∀ A : Finset {x : X // D.component x = n}, A.Nonempty →
        ‖coordinateProjection (A : Set {x : X // D.component x = n}) * q‖ ≤ C * Real.sqrt
          (1 / Real.log (Nat.card {x : X // D.component x = n}) ^ (2 * α) +
            (A.card : ℝ) / Nat.card {x : X // D.component x = n} *
              Real.log (Real.exp 1 * Nat.card {x : X // D.component x = n} / A.card))) :
    p ∉ polynomialQuasiLocal β := by
  let : ∀ n, Fintype {x : X // D.component x = n} :=
    fun n => @Fintype.ofFinite _ (D.finite n)
  apply DynamicalCStarAlgebras.projection_not_mem_polynomialQuasiLocal hX
    (fun n (x : {x : X // D.component x = n}) => (x : X))
    (fun _ => Subtype.val_injective) (fun _ => Isometry.of_dist_eq fun _ _ => rfl)
    D.graph D.connected D.dist_eq
    (by simpa only [Nat.card_eq_fintype_card] using hN) p hp hα hβ
  simpa only [Nat.card_eq_fintype_card] using hdata

end DynamicalCStarAlgebras
