import DynamicalCStarAlgebras.Duhamel

noncomputable section

namespace DynamicalCStarAlgebras

universe u

theorem coordinateProjection_star {X : Type u} (A : Set X) :
    star (coordinateProjection A) = coordinateProjection A :=
  isSelfAdjoint_starProjection (coordinateSubspace A).toSubmodule

theorem coordinateProjection_add_compl {X : Type u} (A : Set X) :
    coordinateProjection A + coordinateProjection Aᶜ = 1 := by
  refine ContinuousLinearMap.ext fun v => lp.ext (funext fun x => ?_)
  change coordinateProjection A v x + coordinateProjection Aᶜ v x = v x
  by_cases hx : x ∈ A
  · rw [coordinateProjection_apply_of_mem A v hx,
      coordinateProjection_apply_of_not_mem Aᶜ v (Set.notMem_compl_iff.mpr hx), add_zero]
  · rw [coordinateProjection_apply_of_not_mem A v hx,
      coordinateProjection_apply_of_mem Aᶜ v hx, zero_add]

theorem compression_mul_split {X : Type u} (a b : Operator X) (A B C : Set X) :
    coordinateProjection A * (a * b) * coordinateProjection B =
      (coordinateProjection A * a * coordinateProjection C) * (b * coordinateProjection B) +
      (coordinateProjection A * a) * (coordinateProjection Cᶜ * b * coordinateProjection B) := by
  calc
    _ = (coordinateProjection A * a) *
        (coordinateProjection C + coordinateProjection Cᶜ) * (b * coordinateProjection B) := by
      simp only [coordinateProjection_add_compl, mul_one, mul_assoc]
    _ = _ := by simp only [mul_add, add_mul, mul_assoc]

theorem compression_mul_norm_le_split {X : Type u} (a b : Operator X) (A B C : Set X) :
    ‖coordinateProjection A * (a * b) * coordinateProjection B‖ ≤
      ‖coordinateProjection A * a * coordinateProjection C‖ * ‖b‖ +
        ‖a‖ * ‖coordinateProjection Cᶜ * b * coordinateProjection B‖ := by
  rw [compression_mul_split a b A B C]
  refine (norm_add_le _ _).trans (add_le_add ((norm_mul_le _ _).trans ?_)
    ((norm_mul_le _ _).trans ?_))
  · exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg b) (coordinateProjection_norm_le B))) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg a) (coordinateProjection_norm_le A))) (norm_nonneg _)

/-- The product modulus estimate, with independently chosen separation radii. -/
theorem quasiLocalModulus_mul_le {X : Type u} [PseudoMetricSpace X]
    (a b : Operator X) (r s : ℝ) :
    quasiLocalModulus (a * b) (r + s) ≤
      quasiLocalModulus a r * ‖b‖ + ‖a‖ * quasiLocalModulus b s := by
  refine (quasiLocalModulus_le_iff _ _ _).mpr fun A B hAB => ?_
  let C : Set X := {z | ∃ y ∈ B, dist z y < s}
  have hCB : ∀ z ∈ Cᶜ, ∀ y ∈ B, s ≤ dist z y :=
    fun z hz y hy => le_of_not_gt fun hzy => hz ⟨y, hy, hzy⟩
  have hAC : ∀ x ∈ A, ∀ z ∈ C, r ≤ dist x z := by
    intro x hx z hz
    obtain ⟨y, hy, hzy⟩ := hz
    linarith [hAB x hx y hy, dist_triangle x z y]
  exact (compression_mul_norm_le_split a b A B C).trans (add_le_add
    (mul_le_mul_of_nonneg_right ((quasiLocalModulus_le_iff a r _).mp le_rfl A C hAC)
      (norm_nonneg b))
    (mul_le_mul_of_nonneg_left ((quasiLocalModulus_le_iff b s _).mp le_rfl Cᶜ B hCB)
      (norm_nonneg a)))

theorem quasiLocalModulus_add_le {X : Type u} [PseudoMetricSpace X]
    (a b : Operator X) (r : ℝ) :
    quasiLocalModulus (a + b) r ≤ quasiLocalModulus a r + quasiLocalModulus b r := by
  refine (quasiLocalModulus_le_iff _ _ _).mpr fun A B hAB => ?_
  rw [mul_add, add_mul]
  exact (norm_add_le _ _).trans (add_le_add
    ((quasiLocalModulus_le_iff a r _).mp le_rfl A B hAB)
    ((quasiLocalModulus_le_iff b r _).mp le_rfl A B hAB))

theorem compression_star_norm {X : Type u} (a : Operator X) (A B : Set X) :
    ‖coordinateProjection A * star a * coordinateProjection B‖ =
      ‖coordinateProjection B * a * coordinateProjection A‖ := by
  simpa only [star_mul, coordinateProjection_star, mul_assoc] using
    norm_star (coordinateProjection B * a * coordinateProjection A)

theorem quasiLocalModulus_star_le {X : Type u} [PseudoMetricSpace X]
    (a : Operator X) (r : ℝ) : quasiLocalModulus (star a) r ≤ quasiLocalModulus a r :=
  (quasiLocalModulus_le_iff _ _ _).mpr fun A B hAB =>
    (compression_star_norm a A B).trans_le
      ((quasiLocalModulus_le_iff a r _).mp le_rfl B A
        (fun y hy x hx => (hAB x hx y hy).trans_eq (dist_comm x y)))

theorem quasiLocalModulus_star {X : Type u} [PseudoMetricSpace X]
    (a : Operator X) (r : ℝ) : quasiLocalModulus (star a) r = quasiLocalModulus a r := by
  refine le_antisymm (quasiLocalModulus_star_le a r) ?_
  simpa only [star_star] using quasiLocalModulus_star_le (star a) r

/-- The three modulus identities preceding the decay-algebra inclusion chain in Section 5. -/
theorem quasiLocalModulus_algebra {X : Type u} [PseudoMetricSpace X]
    (a b : Operator X) (r : ℝ) :
    quasiLocalModulus (star a) r = quasiLocalModulus a r ∧
      quasiLocalModulus (a + b) r ≤ quasiLocalModulus a r + quasiLocalModulus b r ∧
      quasiLocalModulus (a * b) (2 * r) ≤
        quasiLocalModulus a r * ‖b‖ + quasiLocalModulus b r * ‖a‖ := by
  refine ⟨quasiLocalModulus_star a r, quasiLocalModulus_add_le a b r, ?_⟩
  simpa only [two_mul, mul_comm ‖a‖] using quasiLocalModulus_mul_le a b r r

end DynamicalCStarAlgebras
