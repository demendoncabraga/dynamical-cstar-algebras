import DynamicalCStarAlgebras.BoundedCommutators

namespace DynamicalCStarAlgebras

/-- A bounded operator realizing the manuscript's possibly unbounded diagonal
commutator matrix. This predicate does not assert that such an operator exists. -/
def IsIteratedCommutator {X : Type*} (h : X → ℝ) (a : Operator X)
    (k : ℕ) (b : Operator X) : Prop :=
  ∀ x y, matrixEntry b x y = ((h x - h y : ℝ) : ℂ) ^ k * matrixEntry a x y

/-- The entrywise definition determines a unique bounded operator whenever it
exists; order zero is the original operator, and successive orders satisfy
Equation Eq.defi.adk.inductive, also for unbounded height functions. -/
theorem iteratedCommutator_characterization {X : Type*} (h : X → ℝ) (a : Operator X) :
    (∀ b, IsIteratedCommutator h a 0 b ↔ b = a) ∧
    (∀ k b c, IsIteratedCommutator h a k b → IsIteratedCommutator h a k c → b = c) ∧
    ∀ k b c, IsIteratedCommutator h a k b →
      (IsIteratedCommutator h a (k + 1) c ↔ IsIteratedCommutator h b 1 c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b
    constructor
    · intro hb
      apply operator_ext
      intro x y
      simpa only [pow_zero, one_mul] using hb x y
    · rintro rfl
      intro x y
      simp only [pow_zero, one_mul]
  · intro k b c hb hc
    exact operator_ext fun x y => (hb x y).trans (hc x y).symm
  · intro k b c hb
    unfold IsIteratedCommutator at hb ⊢
    simp only [pow_succ', pow_zero, one_mul, hb, mul_assoc]

end DynamicalCStarAlgebras
