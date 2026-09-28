import DynamicalCStarAlgebras.QuasiLocal

noncomputable section

namespace DynamicalCStarAlgebras

universe u

theorem delta_mem_coordinateSubspace {X : Type u} {A : Set X} {x : X} (hx : x ∈ A) :
    delta x ∈ coordinateSubspace A :=
  (mem_coordinateSubspace A (delta x)).mpr fun y hy =>
    @lp.single_apply_ne X (fun _ => ℂ) _ (Classical.decEq X) 2 x 1 y
      (fun h => hy (h.symm ▸ hx))

theorem coordinateProjection_apply_of_not_mem {X : Type u} (A : Set X)
    (v : HilbertSpace X) {x : X} (hx : x ∉ A) : coordinateProjection A v x = 0 :=
  (mem_coordinateSubspace A _).mp
    ((coordinateSubspace A).toSubmodule.starProjection_apply_mem v) x hx

theorem coordinateProjection_apply_of_mem {X : Type u} (A : Set X)
    (v : HilbertSpace X) {x : X} (hx : x ∈ A) : coordinateProjection A v x = v x := by
  have hz := (coordinateSubspace A).toSubmodule.starProjection_inner_eq_zero v
    (delta x) (delta_mem_coordinateSubspace hx)
  have he : v x - coordinateProjection A v x = 0 := by
    simpa [delta, lp.inner_single_left, lp.coeFn_sub, coordinateProjection]
      using (inner_eq_zero_symm.mp hz)
  exact (sub_eq_zero.mp he).symm

theorem operator_ext {X : Type u} {a b : Operator X}
    (h : ∀ x y, matrixEntry a x y = matrixEntry b x y) : a = b := by
  classical
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro y
  ext x
  exact h x y

theorem coordinateProjection_delta_of_mem {X : Type u} {A : Set X} {y : X}
    (hy : y ∈ A) : coordinateProjection A (delta y) = delta y :=
  (coordinateSubspace A).toSubmodule.starProjection_eq_self_iff.mpr
    (delta_mem_coordinateSubspace hy)

theorem coordinateProjection_delta_of_not_mem {X : Type u} {A : Set X} {y : X}
    (hy : y ∉ A) : coordinateProjection A (delta y) = 0 := by
  apply lp.ext
  funext x
  by_cases hx : x ∈ A
  · exact (coordinateProjection_apply_of_mem A (delta y) hx).trans
      (@lp.single_apply_ne X (fun _ => ℂ) _ (Classical.decEq X) 2 y 1 x
        (ne_of_mem_of_not_mem hx hy))
  · exact coordinateProjection_apply_of_not_mem A (delta y) hx

theorem compression_eq_zero_of_entries {X : Type u} (a : Operator X) (A B : Set X)
    (h : ∀ x ∈ A, ∀ y ∈ B, matrixEntry a x y = 0) :
    coordinateProjection A * a * coordinateProjection B = 0 := by
  refine operator_ext fun x y => ?_
  change coordinateProjection A (a (coordinateProjection B (delta y))) x = 0
  by_cases hy : y ∈ B
  · rw [coordinateProjection_delta_of_mem hy]
    exact (Classical.em (x ∈ A)).elim
      (fun hx => (coordinateProjection_apply_of_mem A _ hx).trans (h x hx y hy))
      (coordinateProjection_apply_of_not_mem A _)
  · simp [coordinateProjection_delta_of_not_mem hy]

/-- Compression vanishes when the corresponding rectangle misses the matrix support. -/
theorem compression_eq_zero_of_disjoint_support {X : Type u} (a : Operator X)
    (A B : Set X) (h : Disjoint (A ×ˢ B) (operatorSupport a)) :
    coordinateProjection A * a * coordinateProjection B = 0 :=
  compression_eq_zero_of_entries a A B fun x hx y hy =>
    Classical.byContradiction fun hne =>
      Set.disjoint_left.mp h (show (x, y) ∈ A ×ˢ B from ⟨hx, hy⟩) hne

/-- Controlled-propagation operators are quasi-local on every coarse space. -/
theorem HasControlledPropagation.isQuasiLocal {X : Type u} {C : CoarseStructure X}
    {a : Operator X} (ha : HasControlledPropagation C a) : IsQuasiLocal C a :=
  fun _ hε => ⟨operatorSupport a, ha, fun A B hAB =>
    (compression_eq_zero_of_disjoint_support a A B hAB) ▸
      (norm_zero : ‖(0 : Operator X)‖ = 0) ▸ hε.le⟩

/-- Section 2.2: the uniform Roe algebra is contained in the quasi-local algebra. -/
theorem uniformRoe_subset_quasiLocal {X : Type u} (C : CoarseStructure X) :
    uniformRoe C ⊆ quasiLocal C :=
  closure_minimal (fun _ ha => ha.isQuasiLocal) (isClosed_quasiLocal C)

end DynamicalCStarAlgebras
