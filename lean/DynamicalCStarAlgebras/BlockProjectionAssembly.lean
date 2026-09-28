import DynamicalCStarAlgebras.CoordinateLiftAlgebra

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

lemma blockDiagonal_commute_projection {X I : Type*} (π : X → I) (a : Operator X)
    (ha : ∀ x y, π x ≠ π y → matrixEntry a x y = 0) (i : I) :
    Commute (coordinateProjection {x | π x = i}) a := by
  apply operator_ext
  intro x y
  change coordinateProjection {x | π x = i} (a (delta y)) x =
    a (coordinateProjection {x | π x = i} (delta y)) x
  rw [coordinateProjection_apply_ite]
  simp only [Set.mem_ofPred_eq]
  by_cases hx : π x = i <;> by_cases hy : π y = i
  · rw [if_pos hx, coordinateProjection_delta_of_mem (show y ∈ {x | π x = i} from hy)]
  · rw [if_pos hx, coordinateProjection_delta_of_not_mem (show y ∉ {x | π x = i} from hy), map_zero]
    exact ha x y (fun he => hy (he.symm.trans hx))
  · rw [if_neg hx, coordinateProjection_delta_of_mem (show y ∈ {x | π x = i} from hy)]
    exact (ha x y (fun he => hx (he.trans hy))).symm
  · rw [if_neg hx, coordinateProjection_delta_of_not_mem (show y ∉ {x | π x = i} from hy), map_zero]
    rfl

lemma blockDiagonal_of_commute_projection {X I : Type*} (π : X → I) (a : Operator X)
    (ha : ∀ i, Commute (coordinateProjection {x | π x = i}) a) :
    ∀ x y, π x ≠ π y → matrixEntry a x y = 0 := by
  intro x y hxy
  have h := congrArg (fun b : Operator X => b (delta y) x) (ha (π y)).eq
  change coordinateProjection {x | π x = π y} (a (delta y)) x =
    a (coordinateProjection {x | π x = π y} (delta y)) x at h
  rw [coordinateProjection_apply_of_not_mem _ _ (show x ∉ {x | π x = π y} from hxy),
    coordinateProjection_delta_of_mem (show y ∈ {x | π x = π y} from rfl)] at h
  exact h.symm

lemma blockDiagonal_mul {X I : Type*} (π : X → I) (a b : Operator X)
    (ha : ∀ x y, π x ≠ π y → matrixEntry a x y = 0)
    (hb : ∀ x y, π x ≠ π y → matrixEntry b x y = 0) :
    ∀ x y, π x ≠ π y → matrixEntry (a * b) x y = 0 :=
  blockDiagonal_of_commute_projection π (a * b) fun i =>
    (blockDiagonal_commute_projection π a ha i).mul_right (blockDiagonal_commute_projection π b hb i)

/-- Every uniformly bounded family of coordinate-fiber operators has an ambient diagonal assembly. -/
theorem exists_assembled_components {X I : Type*} (π : X → I)
    (a : ∀ i, Operator {x : X // π x = i}) {M : ℝ} (hM : 0 ≤ M) (ha : ∀ i, ‖a i‖ ≤ M) :
    ∃ b : Operator X, ‖b‖ ≤ M ∧
      (∀ x y, π x ≠ π y → matrixEntry b x y = 0) ∧
      ∀ i, componentOperator (fun x : {x : X // π x = i} => (x : X)) Subtype.val_injective b = a i := by
  let c (i : I) : Operator X := liftComponentOperator
    (fun x : {x : X // π x = i} => (x : X)) Subtype.val_injective (a i)
  obtain ⟨b, hb, he⟩ := exists_fiber_operator π c hM
    (fun i => (compression_norm_le _ _ _).trans ((norm_liftComponentOperator_le _ _ _).trans (ha i)))
  refine ⟨b, hb, fun x y hxy => by rw [he, if_neg hxy], ?_⟩
  intro i
  apply operator_ext
  intro x y
  rw [matrixEntry_componentOperator, he, if_pos (x.property.trans y.property.symm), x.property]
  exact matrixEntry_liftComponentOperator_image _ _ (a i) x y

lemma componentOperator_mul_of_blockDiagonal {X I : Type*} (π : X → I)
    (a b : Operator X) (hb : ∀ x y, π x ≠ π y → matrixEntry b x y = 0) (i : I) :
    componentOperator (fun x : {x : X // π x = i} => (x : X)) Subtype.val_injective (a * b) =
      componentOperator (fun x : {x : X // π x = i} => (x : X)) Subtype.val_injective a *
      componentOperator (fun x : {x : X // π x = i} => (x : X)) Subtype.val_injective b := by
  let J := (coordinateEmbedding (fun x : {x : X // π x = i} => (x : X))
    Subtype.val_injective).toContinuousLinearMap
  have hrange : Set.range (fun x : {x : X // π x = i} => (x : X)) = {x | π x = i} := by
    ext x
    simp
  have hP : J.comp J.adjoint = coordinateProjection {x | π x = i} := by
    simpa only [hrange] using coordinateEmbedding_mul_adjoint
      (fun x : {x : X // π x = i} => (x : X)) Subtype.val_injective
  have hfix (v : HilbertSpace {x : X // π x = i}) : J (J.adjoint (b (J v))) = b (J v) := by
    have hc := congrArg (fun c : Operator X => c (J v)) (blockDiagonal_commute_projection π b hb i).eq
    have hPv : coordinateProjection {x | π x = i} (J v) = J v := by
      rw [← hP]
      exact congrArg J (coordinateEmbedding_adjoint_apply _ _ v)
    calc
      _ = coordinateProjection {x | π x = i} (b (J v)) := congrArg (fun c : Operator X => c (b (J v))) hP
      _ = b (coordinateProjection {x | π x = i} (J v)) := hc
      _ = _ := congrArg b hPv
  apply ContinuousLinearMap.ext
  intro v
  change J.adjoint (a (b (J v))) = J.adjoint (a (J (J.adjoint (b (J v)))))
  rw [hfix]

lemma blockDiagonal_ext {X I : Type*} (π : X → I) (a b : Operator X)
    (ha : ∀ x y, π x ≠ π y → matrixEntry a x y = 0)
    (hb : ∀ x y, π x ≠ π y → matrixEntry b x y = 0)
    (he : ∀ i, componentOperator (fun x : {x : X // π x = i} => (x : X)) Subtype.val_injective a =
      componentOperator (fun x : {x : X // π x = i} => (x : X)) Subtype.val_injective b) : a = b := by
  apply operator_ext
  intro x y
  by_cases hxy : π x = π y
  · simpa only [matrixEntry_componentOperator] using congrArg
      (fun c => matrixEntry c ⟨x, rfl⟩ ⟨y, hxy.symm⟩) (he (π x))
  · rw [ha x y hxy, hb x y hxy]

/-- The diagonal assembly of orthogonal projections is an orthogonal projection. -/
theorem exists_assembled_projection {X I : Type*} (π : X → I)
    (p : ∀ i, Operator {x : X // π x = i}) (hp : ∀ i, IsStarProjection (p i)) :
    ∃ a : Operator X, IsStarProjection a ∧
      (∀ x y, π x ≠ π y → matrixEntry a x y = 0) ∧
      ∀ i, componentOperator (fun x : {x : X // π x = i} => (x : X)) Subtype.val_injective a = p i := by
  obtain ⟨a, _, hb, he⟩ := exists_assembled_components π p zero_le_one (fun i => (hp i).norm_le)
  refine ⟨a, ⟨?_, ?_⟩, hb, he⟩
  · apply blockDiagonal_ext π (a * a) a (blockDiagonal_mul π a a hb hb) hb
    intro i
    rw [componentOperator_mul_of_blockDiagonal π a a hb i, he i]
    exact (hp i).isIdempotentElem.eq
  · apply operator_ext
    intro x y
    rw [matrixEntry_star]
    by_cases hxy : π x = π y
    · have hh := congrArg (fun c => matrixEntry c ⟨y, hxy.symm⟩ ⟨x, rfl⟩) (he (π x))
      have hh' := congrArg (fun c => matrixEntry c ⟨x, rfl⟩ ⟨y, hxy.symm⟩) (he (π x))
      simp only [matrixEntry_componentOperator] at hh hh'
      rw [hh, ← matrixEntry_star, (hp (π x)).isSelfAdjoint.star_eq, ← hh']
    · rw [hb x y hxy, hb y x (Ne.symm hxy), star_zero]

end DynamicalCStarAlgebras
