import DynamicalCStarAlgebras.EntirePropagation

noncomputable section

namespace DynamicalCStarAlgebras

universe u

theorem IsEntireExtension.add {X : Type u} {h : X → ℝ} {a b : Operator X}
    {F G : ℂ → Operator X} (hF : IsEntireExtension h a F) (hG : IsEntireExtension h b G) :
    IsEntireExtension h (a + b) (fun z => F z + G z) where
  differentiable := hF.differentiable.add hG.differentiable
  on_real t := by simp only [hF.on_real, hG.on_real, ← diagonalFlowEquiv_apply, map_add]

theorem IsEntireExtension.mul {X : Type u} {h : X → ℝ} {a b : Operator X}
    {F G : ℂ → Operator X} (hF : IsEntireExtension h a F) (hG : IsEntireExtension h b G) :
    IsEntireExtension h (a * b) (fun z => F z * G z) where
  differentiable := hF.differentiable.mul hG.differentiable
  on_real t := by simp only [hF.on_real, hG.on_real, ← diagonalFlowEquiv_apply, map_mul]

theorem IsEntireExtension.starExtension {X : Type u} {h : X → ℝ} {a : Operator X}
    {F : ℂ → Operator X} (hF : IsEntireExtension h a F) :
    IsEntireExtension h (star a) (fun z => star (F (star z))) where
  differentiable z := by simpa only [star_star, Function.comp_apply] using!
    (hF.differentiable (star z)).star_star
  on_real t := by simp only [Complex.star_def, Complex.conj_ofReal, hF.on_real,
    ← diagonalFlowEquiv_apply, map_star]

theorem IsEntireExponentialType.star {X : Type u} {h : X → ℝ} {a : Operator X}
    (ha : IsEntireExponentialType h a) : IsEntireExponentialType h (star a) := by
  obtain ⟨F, hF, C, hC, K, hK, hbound⟩ := ha
  exact ⟨fun z => Star.star (F (Star.star z)), hF.starExtension, C, hC, K, hK, fun z =>
    (norm_star (F (Star.star z))).trans_le (by
      simpa only [Complex.star_def, Complex.conj_im, abs_neg] using hbound (Star.star z))⟩

theorem IsEntireExponentialType.add {X : Type u} {h : X → ℝ} {a b : Operator X}
    (ha : IsEntireExponentialType h a) (hb : IsEntireExponentialType h b) :
    IsEntireExponentialType h (a + b) := by
  rcases And.intro ha hb with ⟨⟨F, hF, C, hC, K, hK, hFb⟩, ⟨G, hG, D, hD, L, hL, hGb⟩⟩
  refine ⟨fun z => F z + G z, hF.add hG, C + D, add_pos hC hD,
    K + L, add_pos hK hL, fun z => ?_⟩
  exact ((norm_add_le _ _).trans (add_le_add
    ((hFb z).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hL.le) (abs_nonneg _))) hC.le))
    ((hGb z).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK.le) (abs_nonneg _))) hD.le)))).trans_eq
    (add_mul C D _).symm

theorem IsEntireExponentialType.mul {X : Type u} {h : X → ℝ} {a b : Operator X}
    (ha : IsEntireExponentialType h a) (hb : IsEntireExponentialType h b) :
    IsEntireExponentialType h (a * b) := by
  rcases And.intro ha hb with ⟨⟨F, hF, C, hC, K, hK, hFb⟩, ⟨G, hG, D, hD, L, hL, hGb⟩⟩
  refine ⟨fun z => F z * G z, hF.mul hG, C * D, mul_pos hC hD,
    K + L, add_pos hK hL, fun z => ?_⟩
  simpa only [add_mul, mul_add, Real.exp_add, mul_assoc, mul_comm, mul_left_comm] using
    (norm_mul_le (F z) (G z)).trans
      (mul_le_mul (hFb z) (hGb z) (norm_nonneg _) (mul_pos hC (Real.exp_pos _)).le)

theorem isEntireExponentialType_algebraMap {X : Type u} (h : X → ℝ) (c : ℂ) :
    IsEntireExponentialType h (algebraMap ℂ (Operator X) c) := by
  have he : IsEntireExtension h (algebraMap ℂ (Operator X) c)
      (fun _ => algebraMap ℂ (Operator X) c) :=
    ⟨differentiable_const _, fun t =>
      ((diagonalFlowEquiv h t).toAlgEquiv.commutes c).symm.trans (diagonalFlowEquiv_apply h t _)⟩
  refine ⟨_, he, ‖algebraMap ℂ (Operator X) c‖ + 1, by positivity, 1, zero_lt_one, fun z => ?_⟩
  simpa only [mul_one] using mul_le_mul
    (le_add_of_nonneg_right (a := ‖algebraMap ℂ (Operator X) c‖) zero_le_one)
    (Real.one_le_exp (by positivity : 0 ≤ 1 * |z.im|)) zero_le_one (by positivity)

/-- Entire exponential-type points common to all coarse real maps form a star-subalgebra. -/
def coarseEntireExponentialStarSubalgebra {X : Type u} (C : CoarseStructure X) :
    StarSubalgebra ℂ (Operator X) where
  carrier := {a | ∀ h : X → ℝ, IsCoarseReal C h → IsEntireExponentialType h a}
  zero_mem' h _ := by simpa only [map_zero] using! isEntireExponentialType_algebraMap h 0
  one_mem' h _ := by simpa only [map_one] using! isEntireExponentialType_algebraMap h 1
  add_mem' ha hb h hh := (ha h hh).add (hb h hh)
  mul_mem' ha hb h hh := (ha h hh).mul (hb h hh)
  star_mem' ha h hh := (ha h hh).star
  algebraMap_mem' c h _ := isEntireExponentialType_algebraMap h c

/-- Definition Def.AP.algebra.defi: norm closure after intersecting over coarse maps. -/
def exponentialAnalyticPoints {X : Type u} (C : CoarseStructure X) : Set (Operator X) :=
  closure {a | ∀ h : X → ℝ, IsCoarseReal C h → IsEntireExponentialType h a}

def exponentialAnalyticPointsStarSubalgebra {X : Type u} (C : CoarseStructure X) :
    StarSubalgebra ℂ (Operator X) := (coarseEntireExponentialStarSubalgebra C).topologicalClosure

/-- The closed unital complex star-subalgebra claim following Definition Def.AP.algebra.defi. -/
theorem exponentialAnalyticPoints_algebra {X : Type u} (C : CoarseStructure X) :
    (exponentialAnalyticPointsStarSubalgebra C : Set (Operator X)) = exponentialAnalyticPoints C ∧
      IsClosed (exponentialAnalyticPointsStarSubalgebra C : Set (Operator X)) :=
  ⟨rfl, (coarseEntireExponentialStarSubalgebra C).isClosed_topologicalClosure⟩

end DynamicalCStarAlgebras
