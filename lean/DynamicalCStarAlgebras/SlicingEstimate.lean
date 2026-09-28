import DynamicalCStarAlgebras.RoundedSlicing

noncomputable section

namespace DynamicalCStarAlgebras

/-- Combine rounded heights and bounded remainders with the exact binomial constant. -/
theorem norm_iterate_sliced_height_le {X : Type*} [PseudoMetricSpace X]
    (hdisc : ∀ x y : X, ∃ n : ℕ, dist x y = n) {h : X → ℝ} {L : NNReal}
    (hL : 0 < L) (hh : LipschitzWith L h) (f g : BoundedDiagonal X)
    (hf : ∀ x, f x = (L : ℂ) * (⌊h x / (L : ℝ)⌋ : ℂ)) (hg : ‖g‖ ≤ (L : ℝ))
    (s t : Finset ℤ) (hs : ∀ x, ⌊h x / (L : ℝ)⌋ ∈ s)
    (ht : ∀ x y, ⌊h x / (L : ℝ)⌋ - ⌊h y / (L : ℝ)⌋ ∈ t)
    (a : Operator X) (k : ℕ)
    (hsum : Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ k * quasiLocalModulus a (n + 2))) :
    ‖(diagonalCommutator (f + g))^[k] a‖ ≤
      2 * (3 * (L : ℝ)) ^ k *
        (‖a‖ + ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ k * quasiLocalModulus a (n + 2)) := by
  let M := ‖a‖ + ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ k * quasiLocalModulus a (n + 2)
  have hM : ‖a‖ ≤ M := le_add_of_nonneg_right (tsum_nonneg
    (fun n => mul_nonneg (by positivity) (quasiLocalModulus_nonneg _ _)))
  have hterm (j : ℕ) (hjk : j ≤ k) :
      ‖(diagonalCommutator f)^[j] ((diagonalCommutator g)^[k - j] a)‖ ≤
        2 * (L : ℝ) ^ j * (2 * (L : ℝ)) ^ (k - j) * M := by
    obtain ⟨hsc, hc⟩ := remainder_moment_bounds g a hg j k hjk hsum
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [Function.iterate_zero, id_eq, pow_zero, mul_one, Nat.sub_zero]
      have hb := (iterate_diagonalCommutator_bounds g a hg k 0).1
      have hle := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ (2 * (L : ℝ)) ^ k)
      nlinarith [mul_nonneg (pow_nonneg (by positivity : 0 ≤ 2 * (L : ℝ)) k)
        ((norm_nonneg a).trans hM)]
    · have hr := norm_iterate_rounded_height_le hdisc hL hh f hf s t hs ht
        ((diagonalCommutator g)^[k - j] a) j hj hsc
      exact hr.trans (by simpa only [M, mul_assoc] using
        mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2 * (L : ℝ) ^ j))
  have hbin : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
      (2 * (L : ℝ) ^ j * (2 * (L : ℝ)) ^ (k - j) * M)) = 2 * (3 * (L : ℝ)) ^ k * M := by
    calc
      _ = 2 * (∑ j ∈ Finset.range (k + 1), (L : ℝ) ^ j *
          (2 * (L : ℝ)) ^ (k - j) * (k.choose j : ℝ)) * M := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = _ := by rw [← add_pow]; congr 2; ring
  rw [iterate_diagonalCommutator_add]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j hj => ?_).trans_eq hbin)
  rw [norm_smul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (hterm j (by simpa using Finset.mem_range.mp hj))
    (by positivity)

end DynamicalCStarAlgebras
