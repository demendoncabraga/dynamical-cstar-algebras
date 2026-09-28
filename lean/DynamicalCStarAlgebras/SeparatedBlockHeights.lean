import DynamicalCStarAlgebras.CompressionDiscontinuity

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

/-- Extend compatible constant values on a family of subsets to a real 1-Lipschitz map. -/
theorem exists_lipschitz_prescribed_on_sets {X ι : Type*} [PseudoMetricSpace X]
    (A : ι → Set X) (v : ι → ℝ)
    (hA : ∀ i j, ∀ x ∈ A i, ∀ y ∈ A j, dist (v i) (v j) ≤ dist x y) :
    ∃ h : X → ℝ, LipschitzWith 1 h ∧ ∀ i, ∀ x ∈ A i, h x = v i := by
  let f : X → ℝ := fun x => if hx : ∃ i, x ∈ A i then v hx.choose else 0
  have hf : ∀ i, ∀ x ∈ A i, f x = v i := by
    intro i x hx
    have he : ∃ j, x ∈ A j := ⟨i, hx⟩
    dsimp only [f]
    rw [dif_pos he]
    exact dist_le_zero.mp (by simpa only [dist_self] using hA he.choose i x he.choose_spec x hx)
  have hl : LipschitzOnWith 1 f (⋃ i, A i) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    simpa only [hf i x hi, hf j y hj, NNReal.coe_one, one_mul] using hA i j x hi y hj
  obtain ⟨h, hh, he⟩ := hl.extend_real
  exact ⟨h, hh, fun i x hx => (he (Set.mem_iUnion.mpr ⟨i, hx⟩)).symm.trans (hf i x hx)⟩

/-- Separated blocks admit the heights used in the proof of the non-quasi-local proposition. -/
theorem exists_lipschitz_block_heights {X : Type*} [PseudoMetricSpace X]
    (A B : ℕ → Set X)
    (hAA : ∀ n m, ∀ x ∈ A n, ∀ y ∈ A m, |(n : ℝ) - m| ≤ dist x y)
    (hAB : ∀ n m, ∀ x ∈ A n, ∀ y ∈ B m, (n : ℝ) + 1 ≤ dist x y) :
    ∃ h : X → ℝ, LipschitzWith 1 h ∧
      (∀ n, ∀ x ∈ A n, h x = (n : ℝ) + 1) ∧ (∀ n, ∀ x ∈ B n, h x = 0) := by
  have hc : ∀ i j : ℕ ⊕ ℕ, ∀ x ∈ Sum.elim A B i, ∀ y ∈ Sum.elim A B j,
      dist (Sum.elim (fun n : ℕ => (n : ℝ) + 1) (fun _ : ℕ => (0 : ℝ)) i)
        (Sum.elim (fun n : ℕ => (n : ℝ) + 1) (fun _ : ℕ => (0 : ℝ)) j) ≤ dist x y := by
    rintro (n | n) (m | m) x hx y hy
    · simpa only [Sum.elim_inl, Real.dist_eq, add_sub_add_right_eq_sub] using hAA n m x hx y hy
    · simpa only [Sum.elim_inl, Sum.elim_inr, Real.dist_eq, sub_zero,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)] using hAB n m x hx y hy
    · simpa only [Sum.elim_inl, Sum.elim_inr, dist_comm, Real.dist_eq, sub_zero, zero_sub, abs_neg,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ m + 1)] using hAB m n y hy x hx
    · simpa only [Sum.elim_inr, dist_self] using dist_nonneg (x := x) (y := y)
  obtain ⟨h, hh, he⟩ := exists_lipschitz_prescribed_on_sets _ _ hc
  exact ⟨h, hh, fun n => he (.inl n), fun n => he (.inr n)⟩

/-- The separated-block construction in the second half of the non-quasi-local detection proof.
The existence of such blocks for a non-quasi-local operator is a separate step. -/
theorem separated_blocks_detect_discontinuity {X : Type*} [PseudoMetricSpace X]
    (a : Operator X) (A B : ℕ → Set X) {ε : ℝ} (hε : 0 < ε)
    (hnorm : ∀ n, ε ≤ ‖coordinateProjection (A n) * a * coordinateProjection (B n)‖)
    (hself : ∀ n, ∀ x ∈ A n, ∀ y ∈ B n, (n : ℝ) + 1 ≤ dist x y)
    (hsep : ∀ n m, n ≠ m → ∀ x ∈ A n ∪ B n, ∀ y ∈ A m ∪ B m,
      (n : ℝ) + m + 2 ≤ dist x y) :
    ∃ h : X → ℝ, LipschitzWith 1 h ∧
      IsCoarseReal (CoarseStructure.ofPseudoMetric X) h ∧ a ∉ continuityPoints h := by
  have hAA : ∀ n m, ∀ x ∈ A n, ∀ y ∈ A m, |(n : ℝ) - m| ≤ dist x y := by
    intro n m x hx y hy
    by_cases hnm : n = m
    · simp only [hnm, sub_self, abs_zero]; exact dist_nonneg
    · have hb := hsep n m hnm x (Or.inl hx) y (Or.inl hy)
      exact abs_le.mpr ⟨by linarith [Nat.cast_nonneg (α := ℝ) n], by linarith [Nat.cast_nonneg (α := ℝ) m]⟩
  have hAB : ∀ n m, ∀ x ∈ A n, ∀ y ∈ B m, (n : ℝ) + 1 ≤ dist x y := by
    intro n m x hx y hy
    by_cases hnm : n = m
    · exact hnm ▸ hself m x (hnm ▸ hx) y hy
    · have hb := hsep n m hnm x (Or.inl hx) y (Or.inr hy)
      linarith [Nat.cast_nonneg (α := ℝ) m]
  obtain ⟨h, hh, hA, hB⟩ := exists_lipschitz_block_heights A B hAA hAB
  refine ⟨h, hh, lipschitz_isCoarseReal hh, not_continuityPoint_of_compression_gaps h a hε ?_⟩
  exact fun n => ⟨A n, B n, hnorm n, fun x hx y hy => by rw [hA n x hx, hB n y hy, sub_zero]⟩

end DynamicalCStarAlgebras
