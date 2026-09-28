import DynamicalCStarAlgebras.RoeQuasiLocal

noncomputable section

namespace DynamicalCStarAlgebras

universe u

/-- The diagonal phase at time t. No boundedness assumption on h is needed. -/
def diagonalPhase {X : Type u} (h : X → ℝ) (t : ℝ) (x : X) : ℂ :=
  Complex.exp (((t * h x : ℝ) : ℂ) * Complex.I)

theorem diagonalPhase_norm {X : Type u} (h : X → ℝ) (t : ℝ) (x : X) :
    ‖diagonalPhase h t x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I (t * h x)

theorem diagonalPhase_add {X : Type u} (h : X → ℝ) (s t : ℝ) (x : X) :
    diagonalPhase h (s + t) x = diagonalPhase h s x * diagonalPhase h t x := by
  simp [diagonalPhase, add_mul, Complex.ofReal_add, Complex.exp_add]

theorem diagonalPhase_zero {X : Type u} (h : X → ℝ) (x : X) :
    diagonalPhase h 0 x = 1 := by
  simp [diagonalPhase]

theorem diagonalScalar_norm_le {X : Type u} (h : X → ℝ) (t : ℝ) (x : X) :
    ‖diagonalPhase h t x • ContinuousLinearMap.id ℂ ℂ‖ ≤ 1 := by
  simp [norm_smul, diagonalPhase_norm]

/-- Multiplication by the bounded diagonal function exp(i t h). -/
def diagonalUnitary {X : Type u} (h : X → ℝ) (t : ℝ) : Operator X :=
  lp.mapCLM 2 (fun x => diagonalPhase h t x • ContinuousLinearMap.id ℂ ℂ)
    zero_le_one (diagonalScalar_norm_le h t)

theorem diagonalUnitary_apply {X : Type u} (h : X → ℝ) (t : ℝ)
    (v : HilbertSpace X) (x : X) :
    diagonalUnitary h t v x = diagonalPhase h t x * v x := rfl

theorem diagonalUnitary_norm_le {X : Type u} (h : X → ℝ) (t : ℝ) :
    ‖diagonalUnitary h t‖ ≤ 1 :=
  lp.norm_mapCLM_le 2 _ zero_le_one (diagonalScalar_norm_le h t)

theorem diagonalUnitary_add {X : Type u} (h : X → ℝ) (s t : ℝ) :
    diagonalUnitary h (s + t) = diagonalUnitary h s * diagonalUnitary h t := by
  refine ContinuousLinearMap.ext fun v => lp.ext (funext fun x => ?_)
  simp only [mul_apply_eq_comp, diagonalUnitary_apply, diagonalPhase_add, mul_assoc]

theorem diagonalUnitary_zero {X : Type u} (h : X → ℝ) : diagonalUnitary h 0 = 1 := by
  refine ContinuousLinearMap.ext fun v => lp.ext (funext fun x => ?_)
  simp [diagonalUnitary_apply, diagonalPhase_zero]

/-- The diagonal conjugation map sigma_(h,t) from the introduction. -/
def diagonalFlow {X : Type u} (h : X → ℝ) (t : ℝ) (a : Operator X) : Operator X :=
  diagonalUnitary h t * a * diagonalUnitary h (-t)

theorem diagonalFlow_zero {X : Type u} (h : X → ℝ) (a : Operator X) :
    diagonalFlow h 0 a = a := by
  simp [diagonalFlow, diagonalUnitary_zero]

theorem diagonalFlow_add {X : Type u} (h : X → ℝ) (s t : ℝ) (a : Operator X) :
    diagonalFlow h (s + t) a = diagonalFlow h s (diagonalFlow h t a) := by
  simp only [diagonalFlow, neg_add_rev, diagonalUnitary_add, mul_assoc]

theorem diagonalFlow_norm_le {X : Type u} (h : X → ℝ) (t : ℝ) (a : Operator X) :
    ‖diagonalFlow h t a‖ ≤ ‖a‖ :=
  (norm_mul_le _ _).trans
    ((mul_le_of_le_one_right (norm_nonneg _) (diagonalUnitary_norm_le h (-t))).trans
      ((norm_mul_le _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) (diagonalUnitary_norm_le h t))))

/-- Each conjugation preserves operator norm, without assuming continuity of the orbit. -/
theorem diagonalFlow_norm {X : Type u} (h : X → ℝ) (t : ℝ) (a : Operator X) :
    ‖diagonalFlow h t a‖ = ‖a‖ := by
  refine le_antisymm (diagonalFlow_norm_le h t a) ?_
  simpa only [← diagonalFlow_add, neg_add_cancel, diagonalFlow_zero] using
    diagonalFlow_norm_le h (-t) (diagonalFlow h t a)

theorem diagonalUnitary_delta {X : Type u} (h : X → ℝ) (t : ℝ) (y : X) :
    diagonalUnitary h t (delta y) = diagonalPhase h t y • delta y := by
  classical
  refine lp.ext (funext fun x => ?_)
  by_cases hxy : x = y
  · simp [diagonalUnitary_apply, delta, hxy, lp.coeFn_smul]
  · simp [diagonalUnitary_apply, delta, hxy, lp.coeFn_smul]

theorem matrixEntry_diagonalFlow_phases {X : Type u} (h : X → ℝ) (t : ℝ)
    (a : Operator X) (x y : X) : matrixEntry (diagonalFlow h t a) x y =
      diagonalPhase h t x * diagonalPhase h (-t) y * matrixEntry a x y := by
  simp [matrixEntry, diagonalFlow, mul_apply_eq_comp, diagonalUnitary_delta,
    diagonalUnitary_apply, lp.coeFn_smul, mul_left_comm, mul_assoc]

theorem diagonalPhase_mul_neg {X : Type u} (h : X → ℝ) (t : ℝ) (x y : X) :
    diagonalPhase h t x * diagonalPhase h (-t) y =
      Complex.exp (((t * (h x - h y) : ℝ) : ℂ) * Complex.I) := by
  rw [diagonalPhase, diagonalPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The entrywise formula for diagonal conjugation, used throughout the paper. -/
theorem matrixEntry_diagonalFlow {X : Type u} (h : X → ℝ) (t : ℝ)
    (a : Operator X) (x y : X) : matrixEntry (diagonalFlow h t a) x y =
      Complex.exp (((t * (h x - h y) : ℝ) : ℂ) * Complex.I) * matrixEntry a x y := by
  rw [matrixEntry_diagonalFlow_phases, diagonalPhase_mul_neg]

/-- Diagonal conjugation does not change which matrix coefficients vanish. -/
theorem operatorSupport_diagonalFlow {X : Type u} (h : X → ℝ) (t : ℝ)
    (a : Operator X) : operatorSupport (diagonalFlow h t a) = operatorSupport a := by
  ext p
  simp [operatorSupport, matrixEntry_diagonalFlow, Complex.exp_ne_zero]

theorem continuous_diagonalFlow {X : Type u} (h : X → ℝ) (t : ℝ) :
    Continuous (diagonalFlow h t) :=
  (continuous_const.mul continuous_id).mul continuous_const

/-- The diagonal pre-flow preserves the uniform Roe set for every h, coarse or not. -/
theorem diagonalFlow_mem_uniformRoe {X : Type u} (C : CoarseStructure X)
    (h : X → ℝ) (t : ℝ) {a : Operator X} (ha : a ∈ uniformRoe C) :
    diagonalFlow h t a ∈ uniformRoe C := by
  refine Set.MapsTo.closure (s := {b | HasControlledPropagation C b})
    (t := {b | HasControlledPropagation C b}) ?_ (continuous_diagonalFlow h t) ha
  exact fun b hb => show operatorSupport (diagonalFlow h t b) ∈ C.controlled from
    (operatorSupport_diagonalFlow h t b).symm ▸ hb

end DynamicalCStarAlgebras
