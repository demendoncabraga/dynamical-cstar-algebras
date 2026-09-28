import DynamicalCStarAlgebras.BlockProjectionAssembly
import DynamicalCStarAlgebras.BoundedMatrixProducts

noncomputable section
open Classical
open scoped ENNReal
namespace DynamicalCStarAlgebras

/-- The unique diagonal assembly of a bounded family of fiber operators. -/
def fiberAssembly {X I : Type*} (π : X → I)
    (a : lp (fun i => Operator {x : X // π x = i}) ∞) : Operator X :=
  (exists_assembled_components π a (norm_nonneg a)
    (fun i => lp.norm_apply_le_norm ENNReal.top_ne_zero a i)).choose

lemma fiberAssembly_spec {X I : Type*} (π : X → I)
    (a : lp (fun i => Operator {x : X // π x = i}) ∞) :
    ‖fiberAssembly π a‖ ≤ ‖a‖ ∧
      (∀ x y, π x ≠ π y → matrixEntry (fiberAssembly π a) x y = 0) ∧
      ∀ i, componentOperator (fun x : {x : X // π x = i} => (x : X))
        Subtype.val_injective (fiberAssembly π a) = a i :=
  (exists_assembled_components π a (norm_nonneg a)
    (fun i => lp.norm_apply_le_norm ENNReal.top_ne_zero a i)).choose_spec

set_option synthInstance.maxHeartbeats 80000 in
/-- Assembly respects all nonunital complex star algebra operations. -/
def fiberAssemblyHom {X I : Type*} (π : X → I) :
    lp (fun i => Operator {x : X // π x = i}) ∞ →⋆ₙₐ[ℂ] Operator X where
  toFun := fiberAssembly π
  map_zero' := by
    apply blockDiagonal_ext π _ _ (fiberAssembly_spec π 0).2.1
      (fun _ _ _ => rfl)
    intro i
    rw [(fiberAssembly_spec π 0).2.2 i]
    simp [componentOperator]
  map_add' a b := by
    apply blockDiagonal_ext π _ _ (fiberAssembly_spec π (a + b)).2.1
    · intro x y hxy
      change matrixEntry (fiberAssembly π a) x y + matrixEntry (fiberAssembly π b) x y = 0
      rw [(fiberAssembly_spec π a).2.1 x y hxy, (fiberAssembly_spec π b).2.1 x y hxy, add_zero]
    · intro i
      rw [(fiberAssembly_spec π (a + b)).2.2 i]
      change a i + b i = _
      simp only [componentOperator, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
      exact congrArg₂ (· + ·) ((fiberAssembly_spec π a).2.2 i).symm
        ((fiberAssembly_spec π b).2.2 i).symm
  map_mul' a b := by
    apply blockDiagonal_ext π _ _ (fiberAssembly_spec π (a * b)).2.1
      (blockDiagonal_mul π _ _ (fiberAssembly_spec π a).2.1 (fiberAssembly_spec π b).2.1)
    intro i
    rw [componentOperator_mul_of_blockDiagonal π _ _ (fiberAssembly_spec π b).2.1 i,
      (fiberAssembly_spec π (a * b)).2.2 i, (fiberAssembly_spec π a).2.2 i,
      (fiberAssembly_spec π b).2.2 i]
    rfl
  map_smul' c a := by
    apply blockDiagonal_ext π _ _ (fiberAssembly_spec π (c • a)).2.1
    · intro x y hxy
      rw [matrixEntry_smul, (fiberAssembly_spec π a).2.1 x y hxy, mul_zero]
    · intro i
      rw [(fiberAssembly_spec π (c • a)).2.2 i]
      change c • a i = _
      simp only [componentOperator, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
      exact congrArg (c • ·) ((fiberAssembly_spec π a).2.2 i).symm
  map_star' a := by
    apply blockDiagonal_ext π _ _ (fiberAssembly_spec π (star a)).2.1
    · intro x y hxy
      rw [matrixEntry_star, (fiberAssembly_spec π a).2.1 y x (Ne.symm hxy), star_zero]
    · intro i
      rw [(fiberAssembly_spec π (star a)).2.2 i]
      change star (a i) = _
      rw [← (fiberAssembly_spec π a).2.2 i]
      change (componentOperator _ _ (fiberAssembly π a)).adjoint = _
      simp only [componentOperator, ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]
      rfl

theorem fiberAssemblyHom_component {X I : Type*} (π : X → I)
    (a : lp (fun i => Operator {x : X // π x = i}) ∞) (i : I) :
    componentOperator (fun x : {x : X // π x = i} => (x : X))
      Subtype.val_injective (fiberAssemblyHom π a) = a i :=
  (fiberAssembly_spec π a).2.2 i

theorem fiberAssemblyHom_blockDiagonal {X I : Type*} (π : X → I)
    (a : lp (fun i => Operator {x : X // π x = i}) ∞) :
    ∀ x y, π x ≠ π y → matrixEntry (fiberAssemblyHom π a) x y = 0 :=
  (fiberAssembly_spec π a).2.1

theorem fiberAssemblyHom_injective {X I : Type*} (π : X → I) :
    Function.Injective (fiberAssemblyHom π) := by
  intro a b hab
  apply lp.ext
  funext i
  rw [← fiberAssemblyHom_component π a i, ← fiberAssemblyHom_component π b i, hab]

theorem fiberAssemblyHom_isometry {X I : Type*} (π : X → I) :
    Isometry (fiberAssemblyHom π) :=
  NonUnitalStarAlgHom.isometry _ (fiberAssemblyHom_injective π)

end DynamicalCStarAlgebras
