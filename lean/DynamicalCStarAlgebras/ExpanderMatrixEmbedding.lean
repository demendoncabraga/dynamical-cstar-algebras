import DynamicalCStarAlgebras.ExponentialProjectionScaling
import DynamicalCStarAlgebras.BlockProduct

noncomputable section

open Filter
open scoped ENNReal

namespace DynamicalCStarAlgebras

set_option maxHeartbeats 800000 in
/-- The complete matrix-product embedding argument of
Thm.Exp.decay.Still.Contains, conditional on the actual good subspaces supplied
by LemmaGoodSubspacesQuarterPower. Existence of those subspaces is not asserted. -/
theorem CoarseGraphUnion.exists_matrixProduct_embedding_of_good_subspaces
    {X : Type*} [PseudoMetricSpace X] (D : CoarseGraphUnion X)
    {γ C : ℝ} (hγ : 0 < γ) (hC : 1 ≤ C)
    (hExp : ∀ n, letI := @Fintype.ofFinite {x : X // D.component x = n} (D.finite n)
      HasVertexExpansion (D.graph n) γ)
    (hN : Tendsto (fun n => (Nat.card {x : X // D.component x = n} : ℝ)) atTop atTop)
    (W : ∀ n, ClosedSubmodule ℂ (HilbertSpace {x : X // D.component x = n}))
    (hdim : ∀ n, Module.finrank ℂ (W n).toSubmodule =
      ⌈(Nat.card {x : X // D.component x = n} : ℝ) ^ (1 / 4 : ℝ)⌉₊)
    (hgood : ∀ (n : ℕ) (S : Finset {x : X // D.component x = n}) (δ : ℝ),
      1 / (Module.finrank ℂ (W n).toSubmodule : ℝ) ≤ δ → δ ≤ 1 / 2 →
      (S.card : ℝ) ≤ δ * Nat.card {x : X // D.component x = n} →
      ‖coordinateProjection (S : Set {x : X // D.component x = n}) *
        (W n).toSubmodule.starProjection‖ ≤ C * Real.sqrt (δ * Real.log (1 / δ))) :
    ∃ Φ : BoundedMatrixProduct →⋆ₙₐ[ℂ] Operator X,
      Function.Injective Φ ∧ Isometry Φ ∧
      ∀ a, HasExponentialDecay (Φ a) ∧ Φ a ∈ exponentialQuasiLocal := by
  let : ∀ n, Fintype {x : X // D.component x = n} :=
    fun n => @Fintype.ofFinite _ (D.finite n)
  let : ∀ n, NormedAddCommGroup (W n).toSubmodule := fun n => inferInstance
  let : ∀ n, InnerProductSpace ℂ (W n).toSubmodule := fun n => inferInstance
  let : ∀ n, CompleteSpace (W n).toSubmodule := fun n => inferInstance
  let : ∀ n, FiniteDimensional ℂ (W n).toSubmodule := fun n => inferInstance
  have hdimLower (n : ℕ) :
      (Nat.card {x : X // D.component x = n} : ℝ) ^ (1 / 4 : ℝ) ≤
        Module.finrank ℂ (W n).toSubmodule := by
    rw [hdim]
    exact Nat.le_ceil _
  have hgrow : Tendsto (fun n => Module.finrank ℂ (W n).toSubmodule) atTop atTop := by
    apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
    exact tendsto_atTop_mono hdimLower
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hN)
  obtain ⟨φ, hφ, hφiso⟩ := exists_boundedMatrixProduct_embedding
    (fun n => (W n).toSubmodule) hgrow
  let corner (n : ℕ) := isometryCornerHom (W n).toSubmodule.subtypeₗᵢ
  have hcorner (n : ℕ) : Function.Injective (corner n) := isometryCornerHom_injective _
  let Ψ := boundedProductHom (A := fun n => (W n).toSubmodule →L[ℂ] (W n).toSubmodule)
    id corner hcorner
  have hΨ : Function.Injective Ψ := boundedProductHom_injective
    (A := fun n => (W n).toSubmodule →L[ℂ] (W n).toSubmodule)
    id Function.surjective_id corner hcorner
  let Φ := (fiberAssemblyHom D.component).comp (Ψ.comp φ)
  have hΦ : Function.Injective Φ := (fiberAssemblyHom_injective D.component).comp (hΨ.comp hφ)
  have hΦiso : Isometry Φ := (fiberAssemblyHom_isometry D.component).comp
    ((NonUnitalStarAlgHom.isometry Ψ hΨ).comp hφiso)
  refine ⟨Φ, hΦ, hΦiso, fun a => ?_⟩
  have ha : HasExponentialDecay (Φ a) := by
    apply D.good_projection_block_hasExponentialDecay (Φ a)
      (fiberAssemblyHom_blockDiagonal D.component (Ψ (φ a))) hγ hC hExp
    intro n
    refine ⟨Module.finrank ℂ (W n).toSubmodule, (W n).toSubmodule.starProjection,
      isSelfAdjoint_starProjection _, hdimLower n, ?_, ?_, hgood n⟩
    · change (W n).toSubmodule.starProjection *
        componentOperator _ _ (fiberAssemblyHom D.component (Ψ (φ a))) =
        componentOperator _ _ (fiberAssemblyHom D.component (Ψ (φ a)))
      rw [fiberAssemblyHom_component]
      exact (subspace_corner_supported (W n).toSubmodule (φ a n)).1
    · change componentOperator _ _ (fiberAssemblyHom D.component (Ψ (φ a))) *
        (W n).toSubmodule.starProjection =
        componentOperator _ _ (fiberAssemblyHom D.component (Ψ (φ a)))
      rw [fiberAssemblyHom_component]
      exact (subspace_corner_supported (W n).toSubmodule (φ a n)).2
  exact ⟨ha, subset_closure ha⟩

end DynamicalCStarAlgebras
