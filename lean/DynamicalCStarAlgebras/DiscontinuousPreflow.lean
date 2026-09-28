import DynamicalCStarAlgebras.CoarseFlowCharacterization

noncomputable section
namespace DynamicalCStarAlgebras

/-- The unilateral shift and the quadratic height give a diagonal pre-flow
which is not an operator-norm continuous flow. -/
theorem exists_discontinuous_diagonal_preflow :
    ∃ (h : ℕ → ℝ) (a : Operator ℕ), ¬ Continuous (fun t : ℝ => diagonalFlow h t a) := by
  let E : Set (ℕ × ℕ) := {p | p.1 = p.2 + 1}
  have hE : IsPartialBijection E := by
    constructor <;> intro p q he <;> apply Subtype.ext <;> apply Prod.ext
    all_goals
      have hp : p.val.1 = p.val.2 + 1 := p.property
      have hq : q.val.1 = q.val.2 + 1 := q.property
      dsimp only at he
      omega
  refine ⟨fun n => (n : ℝ) ^ 2, partialTranslationOperator E hE, ?_⟩
  intro ha
  obtain ⟨R, hR⟩ := boundedVariation_of_partialTranslation_continuous _ E hE ha
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hb := hR (n + 1, n) (show (n + 1, n) ∈ E from rfl)
  change dist (((n + 1 : ℕ) : ℝ) ^ 2) ((n : ℝ) ^ 2) ≤ R at hb
  rw [Real.dist_eq, Nat.cast_add, Nat.cast_one] at hb
  have hh := (le_abs_self (((n : ℝ) + 1) ^ 2 - (n : ℝ) ^ 2)).trans hb
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

end DynamicalCStarAlgebras
