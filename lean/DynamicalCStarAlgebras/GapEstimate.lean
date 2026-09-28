import DynamicalCStarAlgebras.StripStructure
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

/-- An exponential supported on a set on which its exponent has an upper bound. -/
def restrictedExponential {X : Type*} (f : X → ℝ) (A : Set X) (C : ℝ)
    (hf : ∀ x ∈ A, f x ≤ C) : BoundedDiagonal X :=
  boundedRealDiagonal (fun x => if x ∈ A then Real.exp (f x) else 0) (Real.exp C)
    (fun x => by
      by_cases hx : x ∈ A
      · simpa only [if_pos hx, abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr (hf x hx)
      · simp only [if_neg hx, abs_zero]; exact Real.exp_nonneg C)

theorem restrictedExponential_apply {X : Type*} (f : X → ℝ) (A : Set X) (C : ℝ)
    (hf : ∀ x ∈ A, f x ≤ C) (x : X) :
    restrictedExponential f A C hf x = if x ∈ A then (Real.exp (f x) : ℂ) else 0 := by
  by_cases hx : x ∈ A <;> simp [restrictedExponential, boundedRealDiagonal_apply, hx]

theorem restrictedExponential_norm_le {X : Type*} (f : X → ℝ) (A : Set X) (C : ℝ)
    (hf : ∀ x ∈ A, f x ≤ C) : ‖restrictedExponential f A C hf‖ ≤ Real.exp C := by
  refine lp.norm_le_of_forall_le (Real.exp_nonneg C) fun x => ?_
  by_cases hx : x ∈ A
  · simpa only [restrictedExponential_apply, if_pos hx, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr (hf x hx)
  · simpa only [restrictedExponential_apply, if_neg hx, norm_zero] using Real.exp_nonneg C

theorem matrixEntry_diagonal_sandwich {X : Type*} (f g : BoundedDiagonal X)
    (a : Operator X) (x y : X) :
    matrixEntry (diagonalMultiplier f * a * diagonalMultiplier g) x y =
      f x * matrixEntry a x y * g y := by
  simp only [matrixEntry, mul_apply_eq_comp, diagonalMultiplier_delta, map_smul,
    diagonalMultiplier_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- The gap estimate with any finite lower and upper height bounds. -/
theorem gapEstimate_of_bounds {X : Type*} (h : X → ℝ) {θ : ℝ} (hθ : 0 ≤ θ)
    (a b : Operator X)
    (hb : ∀ x y, matrixEntry b x y = (Real.exp (θ * (h x - h y)) : ℂ) * matrixEntry a x y)
    (A B : Set X) (α β : ℝ) (hA : ∀ x ∈ A, α ≤ h x) (hB : ∀ y ∈ B, h y ≤ β) :
    ‖coordinateProjection A * a * coordinateProjection B‖ ≤
      Real.exp (-θ * (α - β)) * ‖b‖ := by
  let f := restrictedExponential (fun x => -θ * h x) A (-θ * α)
    (fun x hx => mul_le_mul_of_nonpos_left (hA x hx) (neg_nonpos.mpr hθ))
  let g := restrictedExponential (fun y => θ * h y) B (θ * β)
    (fun y hy => mul_le_mul_of_nonneg_left (hB y hy) hθ)
  have he : coordinateProjection A * a * coordinateProjection B =
      diagonalMultiplier f * b * diagonalMultiplier g := by
    refine operator_ext fun x y => ?_
    rw [matrixEntry_compression, matrixEntry_diagonal_sandwich, hb]
    simp only [f, g, restrictedExponential_apply]
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ B
    · simp only [hx, hy, and_self, if_true]
      have hc : Real.exp (-θ * h x) * Real.exp (θ * (h x - h y)) * Real.exp (θ * h y) = 1 := by
        rw [← Real.exp_add, ← Real.exp_add, show -θ * h x + θ * (h x - h y) + θ * h y = 0 by ring, Real.exp_zero]
      have hc' : (Real.exp (-θ * h x) : ℂ) * Real.exp (θ * (h x - h y)) * Real.exp (θ * h y) = 1 := by exact_mod_cast hc
      calc
        _ = 1 * matrixEntry a x y := (one_mul _).symm
        _ = _ := by rw [← hc']; ring
    all_goals simp [hx, hy]
  have hf : ‖diagonalMultiplier f‖ ≤ Real.exp (-θ * α) :=
    (diagonalMultiplier_norm f).trans_le (restrictedExponential_norm_le _ _ _ _)
  have hg : ‖diagonalMultiplier g‖ ≤ Real.exp (θ * β) :=
    (diagonalMultiplier_norm g).trans_le (restrictedExponential_norm_le _ _ _ _)
  rw [he]
  calc
    _ ≤ (Real.exp (-θ * α) * ‖b‖) * Real.exp (θ * β) :=
      (norm_mul_le _ _).trans (mul_le_mul
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hf (norm_nonneg b)))
        hg (norm_nonneg _) (by positivity))
    _ = _ := by
      rw [mul_right_comm, ← Real.exp_add]
      congr 2
      ring

/-- Extended-real gap bound. An unbounded lower or upper height bound gives an
infinite right-hand side, as specified by the author, including when `M = 0`. -/
def extendedGapBound (θ : ℝ) (α β : EReal) (M : ℝ) : ENNReal :=
  if α = ⊥ ∨ β = ⊤ then ⊤ else EReal.exp (-(θ : EReal) * (α - β)) * ENNReal.ofReal M

theorem extendedGapBound_coe (θ α β M : ℝ) :
    extendedGapBound θ α β M = ENNReal.ofReal (Real.exp (-θ * (α - β)) * M) := by
  simp only [extendedGapBound, EReal.coe_ne_bot, EReal.coe_ne_top, or_self, if_false,
    ← EReal.coe_neg, ← EReal.coe_sub, ← EReal.coe_mul, EReal.exp_coe,
    ENNReal.ofReal_mul (Real.exp_nonneg _)]

/-- Lemma GapEstimate with extended-real infimum and supremum, including unbounded sets. -/
theorem gapEstimate {X : Type*} (h : X → ℝ) {θ : ℝ} (hθ : 0 < θ)
    (a b : Operator X)
    (hb : ∀ x y, matrixEntry b x y = (Real.exp (θ * (h x - h y)) : ℂ) * matrixEntry a x y)
    (A B : Set X) (hA : A.Nonempty) (hB : B.Nonempty) :
    ENNReal.ofReal ‖coordinateProjection A * a * coordinateProjection B‖ ≤
      extendedGapBound θ (sInf ((fun x => (h x : EReal)) '' A))
        (sSup ((fun x => (h x : EReal)) '' B)) ‖b‖ := by
  let α := sInf ((fun x => (h x : EReal)) '' A)
  let β := sSup ((fun x => (h x : EReal)) '' B)
  change _ ≤ extendedGapBound θ α β ‖b‖
  by_cases hinf : α = ⊥ ∨ β = ⊤
  · simp only [extendedGapBound, if_pos hinf, le_top]
  · have hαtop : α ≠ ⊤ := by
      obtain ⟨x, hx⟩ := hA
      exact ne_top_of_le_ne_top (EReal.coe_ne_top (h x))
        (sInf_le (Set.mem_image_of_mem _ hx))
    have hβbot : β ≠ ⊥ := by
      obtain ⟨y, hy⟩ := hB
      exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot (h y))
        (le_sSup (Set.mem_image_of_mem _ hy))
    have hα := EReal.coe_toReal hαtop (not_or.mp hinf).1
    have hβ := EReal.coe_toReal (not_or.mp hinf).2 hβbot
    have hlow : ∀ x ∈ A, α.toReal ≤ h x := by
      intro x hx
      apply EReal.coe_le_coe_iff.mp
      rw [hα]
      exact sInf_le (Set.mem_image_of_mem _ hx)
    have hupp : ∀ y ∈ B, h y ≤ β.toReal := by
      intro y hy
      apply EReal.coe_le_coe_iff.mp
      rw [hβ]
      exact le_sSup (Set.mem_image_of_mem _ hy)
    rw [← hα, ← hβ, extendedGapBound_coe]
    exact ENNReal.ofReal_le_ofReal (gapEstimate_of_bounds h hθ.le a b hb A B _ _ hlow hupp)

end DynamicalCStarAlgebras
