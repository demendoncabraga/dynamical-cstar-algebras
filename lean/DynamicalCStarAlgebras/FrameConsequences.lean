import DynamicalCStarAlgebras.ExpanderNumerics
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section

namespace DynamicalCStarAlgebras

/-- The rank chosen for the first appendix corollary is admissible, and its square
is bounded by four times the ambient dimension. -/
lemma ceil_quarter_rank_bounds {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ ⌈(n : ℝ) ^ (1 / 4 : ℝ)⌉₊ ∧
      ⌈(n : ℝ) ^ (1 / 4 : ℝ)⌉₊ ≤ n ∧
      (⌈(n : ℝ) ^ (1 / 4 : ℝ)⌉₊ : ℝ) ^ 2 ≤ 4 * n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : 1 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hnR (by norm_num)
  have hk : (⌈(n : ℝ) ^ (1 / 4 : ℝ)⌉₊ : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 4 : ℝ) :=
    Nat.ceil_le_two_mul (by linarith)
  have hsq : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 ≤ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)]
    exact Real.rpow_le_self_of_one_le hnR (by norm_num)
  refine ⟨?_, Nat.ceil_le.mpr (Real.rpow_le_self_of_one_le hnR (by norm_num)), ?_⟩
  · exact_mod_cast hq.trans (Nat.le_ceil _)
  · nlinarith [sq_nonneg ((⌈(n : ℝ) ^ (1 / 4 : ℝ)⌉₊ : ℝ) -
      2 * (n : ℝ) ^ (1 / 4 : ℝ))]

/-- The scalar estimate in the appendix passage from the frame bound to the
quarter-power bound. -/
lemma frame_entropy_le_nine {n k a δ : ℝ} (hn : 0 < n) (hk : 0 < k)
    (hksq : k ^ 2 ≤ 4 * n) (hδ : 1 / k ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (ha : 0 < a) (hacard : a ≤ n * δ) :
    k / n + a / n * Real.log (Real.exp 1 * n / a) ≤
      9 * (δ * Real.log (1 / δ)) := by
  have hδpos : 0 < δ := (one_div_pos.mpr hk).trans_le hδ
  have hkδ : 1 ≤ δ * k := (div_le_iff₀ hk).mp hδ
  have hkmajor : k / n ≤ 4 * δ := by
    apply (div_le_iff₀ hn).mpr
    nlinarith [mul_le_mul_of_nonneg_right hkδ hk.le,
      mul_le_mul_of_nonneg_right hksq hδpos.le]
  have haδ : a / n ≤ δ := (div_le_iff₀ hn).mpr (by nlinarith)
  have he := entropy_mass_mono (div_pos ha hn) haδ (by linarith : δ ≤ 1)
  rw [div_div_eq_mul_div] at he
  have hlog : (5 / 8 : ℝ) ≤ Real.log (1 / δ) := by
    have hi : (2 : ℝ) ≤ 1 / δ := (le_div_iff₀ hδpos).mpr (by linarith)
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hi
    linarith [Real.log_two_gt_d9]
  have heq : Real.log (Real.exp 1 / δ) = 1 + Real.log (1 / δ) := by
    rw [Real.log_div (Real.exp_ne_zero _) hδpos.ne', Real.log_exp,
      Real.log_div one_ne_zero hδpos.ne', Real.log_one]
    ring
  rw [heq] at he
  nlinarith [mul_le_mul_of_nonneg_left hlog hδpos.le]

/-- The appendix proves this implication for an operator satisfying the frame
bound. Existence of such a projection is the separate frame-subspace lemma. -/
theorem quarter_power_compression_of_frame_bound {X : Type*} [Fintype X]
    (p : Operator X) {C : ℝ} (hC : 0 ≤ C)
    (hframe : ∀ A : Finset X, A.Nonempty →
      ‖coordinateProjection (A : Set X) * p‖ ≤ C * Real.sqrt
        ((⌈(Fintype.card X : ℝ) ^ (1 / 4 : ℝ)⌉₊ : ℝ) / Fintype.card X +
          (A.card : ℝ) / Fintype.card X *
            Real.log (Real.exp 1 * Fintype.card X / A.card)))
    {δ : ℝ} (hδ : 1 / (⌈(Fintype.card X : ℝ) ^ (1 / 4 : ℝ)⌉₊ : ℝ) ≤ δ)
    (hδhalf : δ ≤ 1 / 2) (A : Finset X) (hcard : (A.card : ℝ) ≤ Fintype.card X * δ) :
    ‖coordinateProjection (A : Set X) * p‖ ≤
      3 * C * Real.sqrt (δ * Real.log (1 / δ)) := by
  classical
  by_cases hA : A.Nonempty
  · have hn : 1 ≤ Fintype.card X := hA.card_pos.trans_le (Finset.card_le_univ A)
    obtain ⟨hk, _, hksq⟩ := ceil_quarter_rank_bounds hn
    have hnR : (0 : ℝ) < Fintype.card X := by exact_mod_cast hn
    have hkR : (0 : ℝ) < ⌈(Fintype.card X : ℝ) ^ (1 / 4 : ℝ)⌉₊ := by
      exact_mod_cast hk
    have haR : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    have he := frame_entropy_le_nine hnR hkR hksq hδ hδhalf haR hcard
    calc
      _ ≤ C * Real.sqrt ((⌈(Fintype.card X : ℝ) ^ (1 / 4 : ℝ)⌉₊ : ℝ) /
          Fintype.card X + (A.card : ℝ) / Fintype.card X *
          Real.log (Real.exp 1 * Fintype.card X / A.card)) := hframe A hA
      _ ≤ C * Real.sqrt (9 * (δ * Real.log (1 / δ))) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he) hC
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)]; norm_num; ring
  · have hAzero : coordinateProjection (A : Set X) = 0 := by
      ext v x
      simp [Finset.not_nonempty_iff_eq_empty.mp hA, coordinateProjection_apply_ite]
    rw [hAzero, zero_mul, norm_zero]
    positivity

/-- Admissibility and relative size of the rank in the large-dimension appendix
corollary; apply this with `q = (log n) ^ α`. -/
lemma floor_ratio_rank_bounds {n : ℕ} {q : ℝ} (hq : 1 ≤ q) (hqn : q < n) :
    1 ≤ ⌊(n : ℝ) / q⌋₊ ∧ ⌊(n : ℝ) / q⌋₊ ≤ n ∧
      (⌊(n : ℝ) / q⌋₊ : ℝ) / n ≤ 1 / q := by
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hnpos : (0 : ℝ) < n := hqpos.trans hqn
  have hfloor := Nat.floor_le (div_nonneg hnpos.le hqpos.le)
  refine ⟨(Nat.one_le_floor_iff _).mpr ((one_le_div hqpos).mpr hqn.le),
    Nat.floor_le_of_le (div_le_self hnpos.le hq), ?_⟩
  calc
    _ ≤ ((n : ℝ) / q) / n := div_le_div_of_nonneg_right hfloor hnpos.le
    _ = 1 / q := by field_simp

/-- The appendix large-dimension estimate, assuming the actual frame bound for
the selected operator. No subspace-existence assertion is assumed implicitly. -/
theorem logarithmic_rank_compression_of_frame_bound {X : Type*} [Fintype X]
    (p : Operator X) {C α : ℝ} (hC : 0 ≤ C)
    (hq : 1 ≤ Real.log (Fintype.card X) ^ α)
    (hqn : Real.log (Fintype.card X) ^ α < Fintype.card X)
    (hframe : ∀ A : Finset X, A.Nonempty →
      ‖coordinateProjection (A : Set X) * p‖ ≤ C * Real.sqrt
        ((⌊(Fintype.card X : ℝ) / Real.log (Fintype.card X) ^ α⌋₊ : ℝ) /
          Fintype.card X + (A.card : ℝ) / Fintype.card X *
            Real.log (Real.exp 1 * Fintype.card X / A.card)))
    (A : Finset X) (hA : A.Nonempty) :
    ‖coordinateProjection (A : Set X) * p‖ ≤ C * Real.sqrt
      (1 / Real.log (Fintype.card X) ^ α + (A.card : ℝ) / Fintype.card X *
        Real.log (Real.exp 1 * Fintype.card X / A.card)) := by
  exact (hframe A hA).trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (add_le_add (floor_ratio_rank_bounds hq hqn).2.2 le_rfl)) hC)

end DynamicalCStarAlgebras
