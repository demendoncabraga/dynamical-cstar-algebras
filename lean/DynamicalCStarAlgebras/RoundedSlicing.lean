import DynamicalCStarAlgebras.IntegerBandSums

noncomputable section

namespace DynamicalCStarAlgebras

/-- The rounded-height part of the slicing estimate, with its exact factor of two. -/
theorem norm_iterate_rounded_height_le {X : Type*} [PseudoMetricSpace X]
    (hdisc : ∀ x y : X, ∃ n : ℕ, dist x y = n) {h : X → ℝ} {L : NNReal}
    (hL : 0 < L) (hh : LipschitzWith L h) (f : BoundedDiagonal X)
    (hf : ∀ x, f x = (L : ℂ) * (⌊h x / (L : ℝ)⌋ : ℂ))
    (s t : Finset ℤ) (hs : ∀ x, ⌊h x / (L : ℝ)⌋ ∈ s)
    (ht : ∀ x y, ⌊h x / (L : ℝ)⌋ - ⌊h y / (L : ℝ)⌋ ∈ t)
    (a : Operator X) (k : ℕ) (hk : 0 < k)
    (hsum : Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ k * quasiLocalModulus a (n + 2))) :
    ‖(diagonalCommutator f)^[k] a‖ ≤
      2 * (L : ℝ) ^ k * (‖a‖ + ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ k * quasiLocalModulus a (n + 2)) := by
  rw [iterate_diagonalCommutator_eq_sum_integerBand f _ s t a L hf hs ht k]
  simp only [mul_pow, mul_smul, ← Finset.smul_sum, norm_smul, norm_pow]
  rw [show ‖(L : ℂ)‖ = (L : ℝ) by simp]
  have hb (m : ℤ) : ‖integerBand (fun x => ⌊h x / (L : ℝ)⌋) s a m‖ ≤ ‖a‖ :=
    norm_integerBand_le _ s a m (norm_nonneg _) (fun _ _ => compression_norm_le _ _ _)
  have hfar (m : ℤ) (_ : 2 ≤ m.natAbs) :
      ‖integerBand (fun x => ⌊h x / (L : ℝ)⌋) s a m‖ ≤ quasiLocalModulus a (m.natAbs : ℝ) := by
    simpa only [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast] using
      norm_integer_floor_band_le_modulus hdisc hL hh s a m
  have hhbound := norm_sum_pow_integer_bands_le _ t (fun n => quasiLocalModulus a n)
    (norm_nonneg a) (fun n => quasiLocalModulus_nonneg a n) hb hfar k hk
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hsum)
  simpa only [Nat.cast_add, Nat.cast_ofNat, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left hhbound (pow_nonneg L.coe_nonneg k)

/-- Lower moments of bounded-remainder commutators are controlled by the original higher moment. -/
theorem remainder_moment_bounds {X : Type*} [PseudoMetricSpace X]
    (g : BoundedDiagonal X) (a : Operator X) {L : ℝ} (hg : ‖g‖ ≤ L)
    (j k : ℕ) (hjk : j ≤ k)
    (hsum : Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ k * quasiLocalModulus a (n + 2))) :
    Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ j *
      quasiLocalModulus ((diagonalCommutator g)^[k - j] a) (n + 2)) ∧
    ‖(diagonalCommutator g)^[k - j] a‖ +
      (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ j *
        quasiLocalModulus ((diagonalCommutator g)^[k - j] a) (n + 2)) ≤
      (2 * L) ^ (k - j) *
        (‖a‖ + ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ k * quasiLocalModulus a (n + 2)) := by
  have hL : 0 ≤ L := (norm_nonneg g).trans hg
  have hmajor (n : ℕ) : ((n + 2 : ℕ) : ℝ) ^ j *
      quasiLocalModulus ((diagonalCommutator g)^[k - j] a) (n + 2) ≤
      (2 * L) ^ (k - j) * (((n + 2 : ℕ) : ℝ) ^ k * quasiLocalModulus a (n + 2)) := by
    have hp : ((n + 2 : ℕ) : ℝ) ^ j ≤ ((n + 2 : ℕ) : ℝ) ^ k :=
      pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ n + 2 by omega)) hjk
    have hb := (iterate_diagonalCommutator_bounds g a hg (k - j) (n + 2)).2
    calc
      _ ≤ ((n + 2 : ℕ) : ℝ) ^ k * ((2 * L) ^ (k - j) * quasiLocalModulus a (n + 2)) :=
        mul_le_mul hp hb (quasiLocalModulus_nonneg _ _) (by positivity)
      _ = _ := by ring
  have hnonneg (n : ℕ) : 0 ≤ ((n + 2 : ℕ) : ℝ) ^ j *
      quasiLocalModulus ((diagonalCommutator g)^[k - j] a) (n + 2) :=
    mul_nonneg (by positivity) (quasiLocalModulus_nonneg _ _)
  have hs := (hsum.mul_left ((2 * L) ^ (k - j))).of_nonneg_of_le hnonneg hmajor
  refine ⟨hs, ?_⟩
  simpa only [tsum_mul_left, mul_add] using add_le_add
    (iterate_diagonalCommutator_bounds g a hg (k - j) 0).1
    (hs.tsum_le_tsum hmajor (hsum.mul_left ((2 * L) ^ (k - j))))

end DynamicalCStarAlgebras
