import DynamicalCStarAlgebras.OperatorSupport

/-! Coordinate projections and the entourage definition of quasi-locality. -/

noncomputable section

namespace DynamicalCStarAlgebras

universe u

/-- The closed subspace of complex l2 families supported on A. -/
def coordinateSubspace {X : Type u} (A : Set X) : ClosedSubmodule ℂ (HilbertSpace X) :=
  ⨅ x : {x // x ∉ A}, (⊥ : ClosedSubmodule ℂ ℂ).comap
    (lp.evalCLM ℂ (fun _ : X => ℂ) 2 x.1)

/-- This is exactly l2(A) embedded in l2(X), described by vanishing off A. -/
theorem mem_coordinateSubspace {X : Type u} (A : Set X) (v : HilbertSpace X) :
    v ∈ coordinateSubspace A ↔ ∀ x ∉ A, v x = 0 := by
  simp [coordinateSubspace, lp.evalCLM, lp.evalₗ]
  rfl

/-- The orthogonal projection chi_A of the manuscript. -/
def coordinateProjection {X : Type u} (A : Set X) : Operator X :=
  (coordinateSubspace A).toSubmodule.starProjection

/-- The range of chi_A consists exactly of the vectors vanishing outside A. -/
theorem coordinateProjection_eq_self_iff {X : Type u} (A : Set X)
    (v : HilbertSpace X) :
    coordinateProjection A v = v ↔ ∀ x ∉ A, v x = 0 :=
  (coordinateSubspace A).toSubmodule.starProjection_eq_self_iff.trans
    (mem_coordinateSubspace A v)

theorem coordinateProjection_norm_le {X : Type u} (A : Set X) :
    ‖coordinateProjection A‖ ≤ 1 :=
  (coordinateSubspace A).toSubmodule.starProjection_norm_le

/-- Compression by two coordinate projections cannot increase operator norm. -/
theorem compression_norm_le {X : Type u} (a : Operator X) (A B : Set X) :
    ‖coordinateProjection A * a * coordinateProjection B‖ ≤ ‖a‖ :=
  (norm_mul_le _ _).trans
    ((mul_le_of_le_one_right (norm_nonneg _) (coordinateProjection_norm_le B)).trans
      ((norm_mul_le _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) (coordinateProjection_norm_le A))))

/-- Section 2.2: (epsilon,E)-quasi-locality. -/
def IsQuasiLocalAt {X : Type u} (a : Operator X) (ε : ℝ) (E : Set (X × X)) : Prop :=
  ∀ A B : Set X, Disjoint (A ×ˢ B) E →
    ‖coordinateProjection A * a * coordinateProjection B‖ ≤ ε

/-- Section 2.2: quasi-locality for an arbitrary coarse space. -/
def IsQuasiLocal {X : Type u} (C : CoarseStructure X) (a : Operator X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ E ∈ C.controlled, IsQuasiLocalAt a ε E

/-- The underlying set of the quasi-local algebra; algebra properties are separate obligations. -/
def quasiLocal {X : Type u} (C : CoarseStructure X) : Set (Operator X) :=
  {a | IsQuasiLocal C a}

/-- A norm perturbation changes each off-diagonal compression by at most that norm. -/
theorem compression_sub_norm_le {X : Type u} (a b : Operator X) (A B : Set X) :
    ‖coordinateProjection A * a * coordinateProjection B -
      coordinateProjection A * b * coordinateProjection B‖ ≤ ‖a - b‖ := by
  simpa only [mul_sub, sub_mul] using compression_norm_le (a - b) A B

/-- Stability of a fixed quasi-locality estimate under an operator-norm perturbation. -/
theorem IsQuasiLocalAt.perturb {X : Type u} {a b : Operator X} {ε : ℝ}
    {E : Set (X × X)} (hb : IsQuasiLocalAt b ε E) :
    IsQuasiLocalAt a (ε + ‖a - b‖) E :=
  fun A B hAB => (norm_le_norm_add_norm_sub' _ _).trans
    (add_le_add (hb A B hAB) (compression_sub_norm_le a b A B))

/-- The norm-closedness assertion in the definition of the quasi-local algebra. -/
theorem isClosed_quasiLocal {X : Type u} (C : CoarseStructure X) :
    IsClosed (quasiLocal C) := by
  refine isClosed_of_closure_subset ?_
  intro a ha ε hε
  obtain ⟨b, hb, hab⟩ := Metric.mem_closure_iff.mp ha (ε / 2) (half_pos hε)
  obtain ⟨E, hE, hbE⟩ := hb (ε / 2) (half_pos hε)
  refine ⟨E, hE, fun A B hAB => (hbE.perturb (a := a) A B hAB).trans ?_⟩
  linarith [show ‖a - b‖ < ε / 2 from (dist_eq_norm a b) ▸ hab]

end DynamicalCStarAlgebras
