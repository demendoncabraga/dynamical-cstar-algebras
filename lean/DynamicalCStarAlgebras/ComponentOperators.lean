import DynamicalCStarAlgebras.BlockModulus

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

/-- A coordinate line, with its Hilbert-space norm. -/
def coordinateLine {X : Type*} (x : X) : ℂ →ₗᵢ[ℂ] HilbertSpace X where
  toLinearMap := lp.lsingle (𝕜 := ℂ) (E := fun _ : X => ℂ) 2 x
  norm_map' z := by
    change ‖lp.single (E := fun _ : X => ℂ) 2 x z‖ = ‖z‖
    exact lp.norm_single (E := fun _ : X => ℂ) (by norm_num : (0 : ENNReal) < 2) x z

/-- Distinct coordinate lines are orthogonal. -/
theorem coordinateLine_orthogonal {X Y : Type*} (ι : Y → X) (hι : Function.Injective ι) :
    OrthogonalFamily ℂ (fun _ : Y => ℂ) (fun y => coordinateLine (ι y)) := by
  intro i j hij z w
  simp [coordinateLine, lp.inner_single_left, lp.single_apply, hι.ne hij]

/-- Extension along an injective coordinate map, preserving the Hilbert norm. -/
def coordinateEmbedding {X Y : Type*} (ι : Y → X) (hι : Function.Injective ι) :
    HilbertSpace Y →ₗᵢ[ℂ] HilbertSpace X :=
  (coordinateLine_orthogonal ι hι).linearIsometry

@[simp] theorem coordinateEmbedding_delta {X Y : Type*} (ι : Y → X)
    (hι : Function.Injective ι) (y : Y) :
    coordinateEmbedding ι hι (delta y) = delta (ι y) := by
  exact (coordinateLine_orthogonal ι hι).linearIsometry_apply_single 1

/-- Restriction of an ambient operator to the coordinate subspace. -/
def componentOperator {X Y : Type*} (ι : Y → X) (hι : Function.Injective ι)
    (a : Operator X) : Operator Y :=
  (coordinateEmbedding ι hι).toContinuousLinearMap.adjoint.comp
    (a.comp (coordinateEmbedding ι hι).toContinuousLinearMap)

@[simp] theorem matrixEntry_componentOperator {X Y : Type*} (ι : Y → X)
    (hι : Function.Injective ι) (a : Operator X) (x y : Y) :
    matrixEntry (componentOperator ι hι a) x y = matrixEntry a (ι x) (ι y) := by
  rw [matrixEntry_eq_inner]
  simp only [componentOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, LinearIsometry.coe_toContinuousLinearMap,
    coordinateEmbedding_delta, ← matrixEntry_eq_inner]

/-- Restriction to a coordinate subspace is contractive. -/
theorem norm_componentOperator_le {X Y : Type*} (ι : Y → X)
    (hι : Function.Injective ι) (a : Operator X) :
    ‖componentOperator ι hι a‖ ≤ ‖a‖ := by
  unfold componentOperator
  grw [ContinuousLinearMap.opNorm_comp_le, ContinuousLinearMap.opNorm_comp_le,
    LinearIsometryEquiv.norm_map, LinearIsometry.norm_toContinuousLinearMap_le,
    LinearIsometry.norm_toContinuousLinearMap_le]
  simp

/-- Compression in a component agrees with restriction of ambient compression. -/
theorem componentOperator_compression {X Y : Type*} (ι : Y → X)
    (hι : Function.Injective ι) (a : Operator X) (A B : Set Y) :
    componentOperator ι hι (coordinateProjection (ι '' A) * a * coordinateProjection (ι '' B)) =
      coordinateProjection A * componentOperator ι hι a * coordinateProjection B := by
  apply operator_ext
  intro x y
  simp [matrixEntry_compression, Set.mem_image, hι.eq_iff]

/-- Isometric coordinate restriction does not increase the quasi-locality modulus. -/
theorem quasiLocalModulus_componentOperator_le {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] (ι : Y → X) (hι : Function.Injective ι) (hd : Isometry ι)
    (a : Operator X) (r : ℝ) :
    quasiLocalModulus (componentOperator ι hι a) r ≤ quasiLocalModulus a r := by
  apply (quasiLocalModulus_le_iff _ _ _).mpr
  intro A B hAB
  rw [← componentOperator_compression]
  apply (norm_componentOperator_le ι hι _).trans
  apply (quasiLocalModulus_le_iff a r _).mp le_rfl
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  simpa only [hd.dist_eq] using hAB x hx y hy

/-- The adjoint of the coordinate inclusion recovers vectors from the component. -/
theorem coordinateEmbedding_adjoint_apply {X Y : Type*} (ι : Y → X)
    (hι : Function.Injective ι) (v : HilbertSpace Y) :
    (coordinateEmbedding ι hι).toContinuousLinearMap.adjoint
      (coordinateEmbedding ι hι v) = v := by
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (coordinateEmbedding ι hι).inner_map_map w v

/-- Extend a component operator by zero to the ambient coordinate space. -/
def liftComponentOperator {X Y : Type*} (ι : Y → X) (hι : Function.Injective ι)
    (a : Operator Y) : Operator X :=
  (coordinateEmbedding ι hι).toContinuousLinearMap.comp
    (a.comp (coordinateEmbedding ι hι).toContinuousLinearMap.adjoint)

/-- Extension by zero is contractive. -/
theorem norm_liftComponentOperator_le {X Y : Type*} (ι : Y → X)
    (hι : Function.Injective ι) (a : Operator Y) :
    ‖liftComponentOperator ι hι a‖ ≤ ‖a‖ := by
  unfold liftComponentOperator
  grw [ContinuousLinearMap.opNorm_comp_le, ContinuousLinearMap.opNorm_comp_le,
    LinearIsometryEquiv.norm_map, LinearIsometry.norm_toContinuousLinearMap_le,
    LinearIsometry.norm_toContinuousLinearMap_le]
  simp

@[simp] theorem matrixEntry_liftComponentOperator_image {X Y : Type*} (ι : Y → X)
    (hι : Function.Injective ι) (a : Operator Y) (x y : Y) :
    matrixEntry (liftComponentOperator ι hι a) (ι x) (ι y) = matrixEntry a x y := by
  rw [matrixEntry_eq_inner, ← coordinateEmbedding_delta ι hι x,
    ← coordinateEmbedding_delta ι hι y]
  simp only [liftComponentOperator, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, coordinateEmbedding_adjoint_apply,
    LinearIsometry.inner_map_map, ← matrixEntry_eq_inner]

end DynamicalCStarAlgebras
