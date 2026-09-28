import DynamicalCStarAlgebras.FiniteMatrixForms

noncomputable section

namespace DynamicalCStarAlgebras

universe u

theorem finiteOrbitForm_uniform_bound {X : Type u} (h : X → ℝ) (a : Operator X) {M : ℝ}
    (hprop : ∀ x y, M < |h x - h y| → matrixEntry a x y = 0) (z : ℂ) (v w : X →₀ ℂ) :
    ‖finiteOrbitForm h a z v w‖ ≤
      (‖a‖ * Real.exp (M * |z.im|)) * ‖finiteVector v‖ * ‖finiteVector w‖ := by
  simpa only [mul_assoc, mul_comm, mul_left_comm] using finiteOrbitForm_norm_le h a hprop z v w

/-- The bounded operator with the prescribed complex-time matrix entries. -/
def finitePropagationExtension {X : Type u} (h : X → ℝ) (a : Operator X) {M : ℝ}
    (hprop : ∀ x y, M < |h x - h y| → matrixEntry a x y = 0) (z : ℂ) : Operator X :=
  operatorOfFiniteForm (finiteOrbitForm h a z) (finiteOrbitForm_uniform_bound h a hprop z)

/-- Equation Eq.19.Aug.26.tarde.3, the sharp norm bound for the constructed extension. -/
theorem norm_finitePropagationExtension_le {X : Type u} (h : X → ℝ) (a : Operator X) {M : ℝ}
    (hprop : ∀ x y, M < |h x - h y| → matrixEntry a x y = 0) (z : ℂ) :
    ‖finitePropagationExtension h a hprop z‖ ≤ ‖a‖ * Real.exp (M * |z.im|) :=
  norm_operatorOfFiniteForm_le _ (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) _

/-- The construction realizes exactly the required complex-time coefficients. -/
theorem matrixEntry_finitePropagationExtension {X : Type u} (h : X → ℝ) (a : Operator X) {M : ℝ}
    (hprop : ∀ x y, M < |h x - h y| → matrixEntry a x y = 0) (z : ℂ) (x y : X) :
    matrixEntry (finitePropagationExtension h a hprop z) x y =
      Complex.exp (Complex.I * z * ((h x - h y : ℝ) : ℂ)) * matrixEntry a x y :=
  (matrixEntry_operatorOfFiniteForm _ (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    (finiteOrbitForm_uniform_bound h a hprop z) x y).trans (finiteMatrixForm_single_one _ x y)

/-- The bounded complex-time construction extends the original real orbit. -/
theorem finitePropagationExtension_real {X : Type u} (h : X → ℝ) (a : Operator X) {M : ℝ}
    (hprop : ∀ x y, M < |h x - h y| → matrixEntry a x y = 0) (t : ℝ) :
    finitePropagationExtension h a hprop t = diagonalFlow h t a :=
  operator_ext fun x y => by
    simp only [matrixEntry_finitePropagationExtension, matrixEntry_diagonalFlow,
      Complex.ofReal_mul, mul_assoc, mul_comm]

end DynamicalCStarAlgebras
