import DynamicalCStarAlgebras.FiniteHeightSlicing
import DynamicalCStarAlgebras.RoeAlgebra
import Mathlib.Data.Set.Countable

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- For an infinite index set, a diagonal projection stays at distance at least
one half from each operator in any prescribed sequence. -/
lemma exists_diagonal_separated_from_sequence {X : Type*} [Infinite X]
    (C : CoarseStructure X) (a : ℕ → Operator X) :
    ∃ b ∈ uniformRoe C, ∀ n, (1 / 2 : ℝ) ≤ ‖b - a n‖ := by
  let e := Infinite.natEmbedding X
  let A : Set X := {x | ∃ n, e n = x ∧ ‖matrixEntry (a n) (e n) (e n)‖ ≤ 1 / 2}
  let f : X → ℝ := fun x => if x ∈ A then 1 else 0
  have hf (x : X) : |f x| ≤ 1 := by dsimp [f]; split_ifs <;> norm_num
  let b := diagonalMultiplier (boundedRealDiagonal f 1 hf)
  refine ⟨b, diagonalMultiplier_mem_uniformRoe C _, ?_⟩
  intro n
  have hA : e n ∈ A ↔ ‖matrixEntry (a n) (e n) (e n)‖ ≤ 1 / 2 := by
    constructor
    · rintro ⟨m, hm, hma⟩
      have hmn : m = n := e.injective hm
      simpa [hmn] using hma
    · intro hn
      exact ⟨n, rfl, hn⟩
  have hentry : matrixEntry (b - a n) (e n) (e n) =
      (f (e n) : ℂ) - matrixEntry (a n) (e n) (e n) := by
    change (matrixEntryCLM (e n) (e n)) (_ - _) = _
    rw [map_sub]
    simp only [b, matrixEntryCLM_apply, matrixEntry_diagonalMultiplier, if_true,
      boundedRealDiagonal_apply]
  have hb := norm_matrixEntry_le (b - a n) (e n) (e n)
  rw [hentry] at hb
  by_cases hn : ‖matrixEntry (a n) (e n) (e n)‖ ≤ 1 / 2
  · have he : f (e n) = 1 := if_pos (hA.mpr hn)
    rw [he, Complex.ofReal_one] at hb
    have hnorm := norm_sub_le (1 - matrixEntry (a n) (e n) (e n))
      (-matrixEntry (a n) (e n) (e n))
    simp only [sub_neg_eq_add, sub_add_cancel, norm_one, norm_neg] at hnorm
    linarith
  · have he : f (e n) = 0 := if_neg (fun h => hn (hA.mp h))
    rw [he, Complex.ofReal_zero, zero_sub, norm_neg] at hb
    exact (le_of_lt (not_le.mp hn)).trans hb

/-- No fixed countable family of operators supplies norm approximants for the
uniform Roe algebra of an infinite set, even allowing arbitrary operators in that family. -/
theorem uniformRoe_not_subset_closure_countable {X : Type*} [Infinite X]
    (C : CoarseStructure X) (S : Set (Operator X)) (hS : S.Countable) :
    ¬ uniformRoe C ⊆ closure S := by
  obtain ⟨a, ha⟩ := Set.countable_iff_exists_subset_range.mp hS
  obtain ⟨b, hb, hsep⟩ := exists_diagonal_separated_from_sequence C a
  intro h
  obtain ⟨c, hc, hbc⟩ := Metric.mem_closure_iff.mp (h hb) (1 / 2) (by norm_num)
  obtain ⟨n, rfl⟩ := ha hc
  rw [dist_eq_norm] at hbc
  exact (not_lt_of_ge (hsep n)) hbc

end DynamicalCStarAlgebras
