import DynamicalCStarAlgebras.DiagonalFlow

namespace DynamicalCStarAlgebras

universe u

theorem matrixEntry_star {X : Type u} (a : Operator X) (x y : X) :
    matrixEntry (star a) x y = star (matrixEntry a y x) := by
  simp only [matrixEntry_eq_inner, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm (a (delta x)) (delta y)]
  rfl

theorem diagonalPhase_star {X : Type u} (h : X → ℝ) (t : ℝ) (x : X) :
    star (diagonalPhase h t x) = diagonalPhase h (-t) x := by
  simp [diagonalPhase, ← Complex.exp_conj, neg_mul]

theorem diagonalUnitary_star {X : Type u} (h : X → ℝ) (t : ℝ) :
    star (diagonalUnitary h t) = diagonalUnitary h (-t) := by
  classical
  refine operator_ext fun x y => ?_
  rw [matrixEntry_star]
  by_cases hxy : x = y
  · simp [matrixEntry, diagonalUnitary_apply, delta, hxy, diagonalPhase_star]
  · simp [matrixEntry, diagonalUnitary_apply, delta, hxy, Ne.symm hxy]

/-- The diagonal multipliers are unitaries in the complex operator C*-algebra. -/
theorem diagonalUnitary_mem_unitary {X : Type u} (h : X → ℝ) (t : ℝ) :
    diagonalUnitary h t ∈ unitary (Operator X) := by
  simp only [Unitary.mem_iff, diagonalUnitary_star, ← diagonalUnitary_add,
    neg_add_cancel, add_neg_cancel, diagonalUnitary_zero, and_self]

/-- Each diagonal conjugation is a complex star-algebra automorphism. -/
noncomputable def diagonalFlowEquiv {X : Type u} (h : X → ℝ) (t : ℝ) :
    Operator X ≃⋆ₐ[ℂ] Operator X :=
  Unitary.conjStarAlgAut ℂ (Operator X)
    ⟨diagonalUnitary h t, diagonalUnitary_mem_unitary h t⟩

theorem diagonalFlowEquiv_apply {X : Type u} (h : X → ℝ) (t : ℝ) (a : Operator X) :
    diagonalFlowEquiv h t a = diagonalFlow h t a := by
  change diagonalUnitary h t * a * star (diagonalUnitary h t) =
    diagonalUnitary h t * a * diagonalUnitary h (-t)
  rw [diagonalUnitary_star]

end DynamicalCStarAlgebras
