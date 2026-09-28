import DynamicalCStarAlgebras.GraphSlicing
import Mathlib.Analysis.SumIntegralExpDecay

noncomputable section

namespace DynamicalCStarAlgebras

/-- The exact exponential-series bound used after the slicing estimate. -/
theorem exponential_moment_sum_bound {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ k * Real.exp (-c * (n + 2))) ∧
    (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ k * Real.exp (-c * (n + 2))) ≤
      Real.exp c * k.factorial / c ^ (k + 1) := by
  have hn (n : ℕ) : 0 ≤ (n : ℝ) ^ k * Real.exp (-(c * n)) := by positivity
  have hb (N : ℕ) : (∑ n ∈ Finset.range N, (n : ℝ) ^ k * Real.exp (-(c * n))) ≤
      Real.exp c * k.factorial / c ^ (k + 1) := by
    simpa only [Finset.range_eq_Ico] using sum_Ico_pow_mul_exp_neg_le (k := k) (M := N) hc
  have hs := summable_of_sum_range_le hn hb
  have ht := (summable_nat_add_iff 2).mpr hs
  have he := hs.sum_add_tsum_nat_add 2
  have hsum := Real.tsum_le_of_sum_range_le hn hb
  have htail : (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ k * Real.exp (-(c * (n + 2)))) ≤
      Real.exp c * k.factorial / c ^ (k + 1) := by
    have hnonneg : 0 ≤ ∑ n ∈ Finset.range 2, (n : ℝ) ^ k * Real.exp (-(c * n)) :=
      Finset.sum_nonneg (fun n _ => hn n)
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (le_add_of_nonneg_left hnonneg).trans (he.trans_le hsum)
  simpa only [neg_mul, Nat.cast_add, Nat.cast_ofNat] using And.intro ht htail

/-- Exponential quasi-locality bounds every polynomial moment with the source factorial constant. -/
theorem quasiLocal_exponential_moment_bound {X : Type*} [PseudoMetricSpace X]
    (a : Operator X) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (ha : ∀ r : ℝ, 0 < r → quasiLocalModulus a r ≤ C * Real.exp (-c * r)) (k : ℕ) :
    Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ k * quasiLocalModulus a (n + 2)) ∧
    (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ k * quasiLocalModulus a (n + 2)) ≤
      C * Real.exp c * k.factorial / c ^ (k + 1) := by
  obtain ⟨hs, hb⟩ := exponential_moment_sum_bound hc k
  have hmajor (n : ℕ) : ((n + 2 : ℕ) : ℝ) ^ k * quasiLocalModulus a (n + 2) ≤
      C * (((n + 2 : ℕ) : ℝ) ^ k * Real.exp (-c * (n + 2))) := by
    simpa only [mul_left_comm] using
      mul_le_mul_of_nonneg_left (ha (n + 2) (by positivity))
        (by positivity : 0 ≤ ((n + 2 : ℕ) : ℝ) ^ k)
  have hsc := (hs.mul_left C).of_nonneg_of_le
    (fun n => mul_nonneg (by positivity) (quasiLocalModulus_nonneg _ _)) hmajor
  refine ⟨hsc, ?_⟩
  have ht := hsc.tsum_le_tsum hmajor (hs.mul_left C)
  rw [tsum_mul_left] at ht
  exact ht.trans (by simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_left hb hC)

/-- Convert the two moment terms to a single factorial growth rate without changing constants. -/
theorem factorial_moment_rescale {c q : ℝ} (hc : 0 < c) (hq : 0 ≤ q) (k : ℕ) :
    1 + q * ((k.factorial : ℝ) / c ^ k) ≤
      (1 + q) * ((k.factorial : ℝ) / (min 1 c) ^ k) := by
  have hd : 0 < min 1 c := lt_min zero_lt_one hc
  have hf : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hd1 : (min 1 c) ^ k ≤ 1 := pow_le_one₀ hd.le (min_le_left _ _)
  have hdc : (min 1 c) ^ k ≤ c ^ k := pow_le_pow_left₀ hd.le (min_le_right _ _) k
  have hfirst : 1 ≤ (k.factorial : ℝ) / (min 1 c) ^ k :=
    (le_div_iff₀ (pow_pos hd k)).mpr (by simpa using hd1.trans hf)
  have hsecond : (k.factorial : ℝ) / c ^ k ≤ (k.factorial : ℝ) / (min 1 c) ^ k :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos hd k) hdc
  nlinarith

/-- The exact factorial commutator bound obtained from slicing an exponentially decaying contraction. -/
theorem finite_integer_factorial_commutator_bound {X : Type*} [PseudoMetricSpace X] [Fintype X]
    (hdisc : ∀ x y : X, ∃ n : ℕ, dist x y = n) (h : X → ℝ) {L : NNReal}
    (hL : 0 < L) (hh : LipschitzWith L h) (a : Operator X) (ha : ‖a‖ ≤ 1)
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hdecay : ∀ r : ℝ, 0 < r → quasiLocalModulus a r ≤ C * Real.exp (-c * r)) (k : ℕ) :
    ‖(diagonalCommutator (finiteRealDiagonal h))^[k] a‖ ≤
      (2 * (1 + C * Real.exp c / c)) * (3 * (L : ℝ) / min 1 c) ^ k * k.factorial := by
  have hm := (quasiLocal_exponential_moment_bound a hc hC hdecay k).2
  have hs := finite_integer_slicing_estimate_pos hdisc h hL hh a k
  have hb : ‖(diagonalCommutator (finiteRealDiagonal h))^[k] a‖ ≤
      2 * (3 * (L : ℝ)) ^ k * (1 + C * Real.exp c * k.factorial / c ^ (k + 1)) :=
    hs.trans (mul_le_mul_of_nonneg_left (add_le_add ha hm) (by positivity))
  have hr := factorial_moment_rescale hc
    (show 0 ≤ C * Real.exp c / c by positivity) k
  have he : 1 + C * Real.exp c * k.factorial / c ^ (k + 1) =
      1 + (C * Real.exp c / c) * ((k.factorial : ℝ) / c ^ k) := by
    rw [pow_succ]
    field_simp
  rw [he] at hb
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2 * (3 * (L : ℝ)) ^ k))
  simpa only [div_pow, div_eq_mul_inv, mul_pow, inv_pow, mul_assoc, mul_left_comm, mul_comm] using! hb'

end DynamicalCStarAlgebras
