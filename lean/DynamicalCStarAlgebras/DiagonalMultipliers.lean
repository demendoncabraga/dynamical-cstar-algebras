import DynamicalCStarAlgebras.QuasiLocalFlow

noncomputable section

namespace DynamicalCStarAlgebras

universe u
open scoped ENNReal

/-- Bounded complex functions on an arbitrary set, with their supremum norm. -/
abbrev BoundedDiagonal (X : Type u) := lp (fun _ : X => ℂ) ∞

theorem diagonalScalar_norm_le_sup {X : Type u} (f : BoundedDiagonal X) (x : X) :
    ‖f x • ContinuousLinearMap.id ℂ ℂ‖ ≤ ‖f‖ := by
  simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using
    lp.norm_apply_le_norm ENNReal.top_ne_zero f x

/-- The diagonal multiplication operator associated to a bounded function. -/
def diagonalMultiplier {X : Type u} (f : BoundedDiagonal X) : Operator X :=
  lp.mapCLM 2 (fun x => f x • ContinuousLinearMap.id ℂ ℂ)
    (norm_nonneg f) (diagonalScalar_norm_le_sup f)

theorem diagonalMultiplier_apply {X : Type u} (f : BoundedDiagonal X)
    (v : HilbertSpace X) (x : X) : diagonalMultiplier f v x = f x * v x := rfl

theorem diagonalMultiplier_norm_le {X : Type u} (f : BoundedDiagonal X) :
    ‖diagonalMultiplier f‖ ≤ ‖f‖ :=
  lp.norm_mapCLM_le 2 _ (norm_nonneg f) (diagonalScalar_norm_le_sup f)

theorem diagonalMultiplier_delta {X : Type u} (f : BoundedDiagonal X) (y : X) :
    diagonalMultiplier f (delta y) = f y • delta y := by
  classical
  refine lp.ext (funext fun x => ?_)
  by_cases hxy : x = y
  all_goals simp [diagonalMultiplier_apply, delta, hxy, lp.coeFn_smul]

theorem diagonalMultiplier_norm {X : Type u} (f : BoundedDiagonal X) :
    ‖diagonalMultiplier f‖ = ‖f‖ := by
  refine le_antisymm (diagonalMultiplier_norm_le f) (lp.norm_le_of_forall_le
    (norm_nonneg _) fun x => ?_)
  classical
  have hd : ‖delta x‖ = 1 := by
    simpa only [delta, norm_one] using lp.norm_single (E := fun _ : X => ℂ) (by norm_num : (0 : ℝ≥0∞) < 2) x (1 : ℂ)
  simpa only [diagonalMultiplier_delta, norm_smul, hd, mul_one] using
    (diagonalMultiplier f).le_opNorm (delta x)

/-- The canonical complex algebra representation of bounded diagonal functions. -/
def diagonalMultiplierHom {X : Type u} : BoundedDiagonal X →ₐ[ℂ] Operator X where
  toFun := diagonalMultiplier
  map_one' := by
    refine ContinuousLinearMap.ext fun v => lp.ext (funext fun x => ?_)
    simp [diagonalMultiplier_apply]
  map_mul' := fun f g => by
    refine ContinuousLinearMap.ext fun v => lp.ext (funext fun x => ?_)
    simp [diagonalMultiplier_apply, mul_apply_eq_comp, lp.infty_coeFn_mul, mul_assoc]
  map_zero' := by
    refine ContinuousLinearMap.ext fun v => lp.ext (funext fun x => ?_)
    simp [diagonalMultiplier_apply]
  map_add' := fun f g => by
    refine ContinuousLinearMap.ext fun v => lp.ext (funext fun x => ?_)
    simp [diagonalMultiplier_apply, add_mul]
  commutes' := fun r => by
    refine ContinuousLinearMap.ext fun v => lp.ext (funext fun x => ?_)
    simp [diagonalMultiplier_apply, Algebra.algebraMap_eq_smul_one]

theorem matrixEntry_diagonalMultiplier {X : Type u} [DecidableEq X] (f : BoundedDiagonal X) (x y : X) :
    matrixEntry (diagonalMultiplier f) x y = if x = y then f x else 0 := by
  classical
  simp [matrixEntry, diagonalMultiplier_apply, delta, Pi.single_apply, mul_ite]

theorem diagonalMultiplier_star {X : Type u} (f : BoundedDiagonal X) :
    diagonalMultiplier (star f) = star (diagonalMultiplier f) := by
  classical
  refine operator_ext fun x y => ?_
  simp only [matrixEntry_star, matrixEntry_diagonalMultiplier, lp.star_apply]
  split_ifs <;> simp_all

/-- The canonical star-algebra representation of l-infinity on complex l2. -/
def diagonalMultiplierStarHom {X : Type u} : BoundedDiagonal X →⋆ₐ[ℂ] Operator X :=
  { diagonalMultiplierHom with map_star' := diagonalMultiplier_star }

theorem diagonalMultiplier_isometry {X : Type u} :
    Isometry (diagonalMultiplier : BoundedDiagonal X → Operator X) :=
  AddMonoidHomClass.isometry_of_norm (diagonalMultiplierHom (X := X)) diagonalMultiplier_norm

theorem diagonalMultiplier_hasControlledPropagation {X : Type u} (C : CoarseStructure X)
    (f : BoundedDiagonal X) : HasControlledPropagation C (diagonalMultiplier f) := by
  classical
  refine C.subset (fun p hp => ?_) C.diagonal
  exact Classical.byContradiction fun hne => hp (by
    rw [matrixEntry_diagonalMultiplier, if_neg (show p.1 ≠ p.2 from hne)])

theorem diagonalMultiplier_mem_uniformRoe {X : Type u} (C : CoarseStructure X)
    (f : BoundedDiagonal X) : diagonalMultiplier f ∈ uniformRoe C :=
  subset_closure (diagonalMultiplier_hasControlledPropagation C f)

end DynamicalCStarAlgebras
