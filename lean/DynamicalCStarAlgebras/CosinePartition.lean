import DynamicalCStarAlgebras.QuasiLocalCommutator

noncomputable section

namespace DynamicalCStarAlgebras

/-- The compactly supported cosine functions in the smoothing lemma. Clipping
the argument at `π/2` implements the zero extension continuously. -/
def cosinePartition (L : ℝ) (k : ℤ) (t : ℝ) : ℝ :=
  Real.cos (Real.pi / 2 * min 1 |t / L - k|)

lemma cosinePartition_mem_unitInterval (L : ℝ) (k : ℤ) (t : ℝ) :
    0 ≤ cosinePartition L k t ∧ cosinePartition L k t ≤ 1 := by
  constructor
  · apply Real.cos_nonneg_of_mem_Icc
    constructor
    · have hp : 0 ≤ Real.pi / 2 * min 1 |t / L - k| :=
        mul_nonneg (by positivity) (le_min zero_le_one (abs_nonneg _))
      linarith [Real.pi_pos]
    · have hp := mul_le_mul_of_nonneg_left (min_le_left 1 |t / L - k|)
        (by positivity : 0 ≤ Real.pi / 2)
      simpa only [mul_one] using hp
  · exact Real.cos_le_one _

lemma cosinePartition_eq_zero_of_one_le {L t : ℝ} {k : ℤ}
    (hk : 1 ≤ |t / L - k|) : cosinePartition L k t = 0 := by
  simp only [cosinePartition, min_eq_left hk, mul_one, Real.cos_pi_div_two]

lemma cosinePartition_eq_zero_of_index_ne {L t : ℝ} {k : ℤ}
    (hk₀ : k ≠ ⌊t / L⌋) (hk₁ : k ≠ ⌊t / L⌋ + 1) : cosinePartition L k t = 0 := by
  apply cosinePartition_eq_zero_of_one_le
  by_cases hk : k < ⌊t / L⌋
  · have hkR : (k : ℝ) + 1 ≤ ⌊t / L⌋ := by exact_mod_cast hk
    exact (le_abs_self _).trans' (by linarith [Int.floor_le (t / L)])
  · have hkR : (⌊t / L⌋ : ℝ) + 2 ≤ k := by
      exact_mod_cast (show ⌊t / L⌋ + 2 ≤ k by omega)
    exact (neg_le_abs _).trans' (by linarith [Int.lt_floor_add_one (t / L)])

lemma cosinePartition_floor_pair_sq (L t : ℝ) :
    cosinePartition L ⌊t / L⌋ t ^ 2 + cosinePartition L (⌊t / L⌋ + 1) t ^ 2 = 1 := by
  have hu₀ : 0 ≤ t / L - ⌊t / L⌋ := sub_nonneg.mpr (Int.floor_le (t / L))
  have hu₁ : t / L - ⌊t / L⌋ ≤ 1 := by linarith [Int.lt_floor_add_one (t / L)]
  have he₀ : cosinePartition L ⌊t / L⌋ t =
      Real.cos (Real.pi / 2 * (t / L - ⌊t / L⌋)) := by
    simp only [cosinePartition, abs_of_nonneg hu₀, min_eq_right hu₁]
  have he₁ : cosinePartition L (⌊t / L⌋ + 1) t =
      Real.sin (Real.pi / 2 * (t / L - ⌊t / L⌋)) := by
    unfold cosinePartition
    rw [Int.cast_add, Int.cast_one, abs_of_nonpos (by linarith : t / L - (⌊t / L⌋ + 1) ≤ 0),
      min_eq_right (by linarith : -(t / L - ((⌊t / L⌋ : ℝ) + 1)) ≤ 1)]
    rw [show Real.pi / 2 * -(t / L - ((⌊t / L⌋ : ℝ) + 1)) =
      Real.pi / 2 - Real.pi / 2 * (t / L - ⌊t / L⌋) by ring, Real.cos_pi_div_two_sub]
  rw [he₀, he₁, Real.cos_sq_add_sin_sq]

lemma cosinePartition_sum_sq (L t : ℝ) : ∑' k : ℤ, cosinePartition L k t ^ 2 = 1 := by
  classical
  calc
    _ = ∑ k ∈ {⌊t / L⌋, ⌊t / L⌋ + 1}, cosinePartition L k t ^ 2 := by
      apply tsum_eq_sum
      intro k hk
      have hk' : k ≠ ⌊t / L⌋ ∧ k ≠ ⌊t / L⌋ + 1 := by simpa using hk
      rw [cosinePartition_eq_zero_of_index_ne hk'.1 hk'.2, zero_pow (by decide : 2 ≠ 0)]
    _ = _ := by
      have hn : ⌊t / L⌋ ≠ ⌊t / L⌋ + 1 := by omega
      simpa only [Finset.sum_insert, Finset.mem_singleton, hn, not_false_eq_true,
        Finset.sum_singleton] using cosinePartition_floor_pair_sq L t

lemma cosinePartition_sub_bound {L t u : ℝ} (hL : 0 < L) (k : ℤ) :
    |cosinePartition L k t - cosinePartition L k u| ≤
      Real.pi / (2 * L) * |t - u| := by
  have hmin := abs_min_sub_min_le_max (1 : ℝ) |t / L - k| 1 |u / L - k|
  simp only [sub_self, abs_zero,
    max_eq_right (show (0 : ℝ) ≤ |(|t / L - k|) - (|u / L - k|)| from abs_nonneg _)] at hmin
  have hab := abs_abs_sub_abs_le_abs_sub (t / L - k) (u / L - k)
  have he : |t / L - k - (u / L - k)| = |t - u| / L := by
    rw [show t / L - k - (u / L - k) = (t - u) / L by ring,
      abs_div, abs_of_pos hL]
  calc
    _ ≤ |Real.pi / 2 * (min 1 |t / L - k|) - Real.pi / 2 * (min 1 |u / L - k|)| :=
      Real.abs_cos_sub_cos_le _ _
    _ = Real.pi / 2 * |(min 1 |t / L - k|) - (min 1 |u / L - k|)| := by
      rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < Real.pi / 2)]
    _ ≤ Real.pi / 2 * (|t - u| / L) :=
      mul_le_mul_of_nonneg_left ((hmin.trans hab).trans_eq he) (by positivity)
    _ = _ := by ring

lemma cosinePartition_eq_zero_of_abs_le {L t : ℝ} (hL : 0 < L) (k : ℤ)
    (ht : L ≤ |t - k * L|) : cosinePartition L k t = 0 := by
  apply cosinePartition_eq_zero_of_one_le
  rw [show t / L - k = (t - k * L) / L by field_simp,
    abs_div, abs_of_pos hL]
  exact (one_le_div hL).mpr ht

/-- The positive, locally finite, Lipschitz square-partition used in `lem:smoothing`. -/
theorem cosinePartition_spec {L : ℝ} (hL : 0 < L) :
    (∀ (k : ℤ) (t : ℝ), 0 ≤ cosinePartition L k t ∧ cosinePartition L k t ≤ 1) ∧
    (∀ (k : ℤ) (t u : ℝ), |cosinePartition L k t - cosinePartition L k u| ≤
      Real.pi / (2 * L) * |t - u|) ∧
    (∀ (k : ℤ) (t : ℝ), L ≤ |t - k * L| → cosinePartition L k t = 0) ∧
    (∀ t k, k ≠ ⌊t / L⌋ → k ≠ ⌊t / L⌋ + 1 → cosinePartition L k t = 0) ∧
    (∀ t, ∑' k : ℤ, cosinePartition L k t ^ 2 = 1) :=
  ⟨cosinePartition_mem_unitInterval L,
    fun k _ _ => cosinePartition_sub_bound hL k,
    fun k _ => cosinePartition_eq_zero_of_abs_le hL k,
    fun _ _ => cosinePartition_eq_zero_of_index_ne, cosinePartition_sum_sq L⟩

end DynamicalCStarAlgebras
