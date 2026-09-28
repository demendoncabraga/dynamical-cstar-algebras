import DynamicalCStarAlgebras.IteratedBands

noncomputable section

namespace DynamicalCStarAlgebras

/-- Summing both signs of an integer band costs exactly a factor of two. -/
theorem norm_sum_integer_bands_le {X : Type*} (b : ℤ → Operator X) (s : Finset ℤ)
    (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n) (hzero : v 0 = 0)
    (hs : Summable (fun n => v (n + 1))) (hb : ∀ m, ‖b m‖ ≤ v m.natAbs) :
    ‖∑ m ∈ s, b m‖ ≤ 2 * ∑' n, v (n + 1) := by
  have hp : Summable (fun n : ℕ => v (Int.natAbs ((n : ℤ) + 1))) := by
    simpa only [← Int.natCast_succ, Int.natAbs_natCast] using hs
  have hn : Summable (fun n : ℕ => v (Int.natAbs (-((n : ℤ) + 1)))) := by
    simpa only [Int.natAbs_neg, ← Int.natCast_succ, Int.natAbs_natCast] using hs
  have hi : Summable (fun m : ℤ => v m.natAbs) := Summable.of_add_one_of_neg_add_one (f := fun m : ℤ => v m.natAbs) hp hn
  have ht := tsum_of_add_one_of_neg_add_one (f := fun m : ℤ => v m.natAbs) hp hn
  have he : (∑' m : ℤ, v m.natAbs) = 2 * ∑' n, v (n + 1) := by
    simpa only [Int.natAbs_neg, ← Int.natCast_succ, Int.natAbs_natCast,
      Int.natAbs_zero, hzero, add_zero, two_mul] using ht
  exact ((norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => hb m)).trans
    ((Summable.sum_le_tsum s (fun m _ => hv _) hi).trans_eq he)

/-- Separate the adjacent bands from the higher integer moments, without losing constants. -/
theorem norm_sum_pow_integer_bands_le {X : Type*} (b : ℤ → Operator X) (s : Finset ℤ)
    (q : ℕ → ℝ) {M : ℝ} (hM : 0 ≤ M) (hq : ∀ n, 0 ≤ q n)
    (hb : ∀ m, ‖b m‖ ≤ M) (hfar : ∀ m, 2 ≤ m.natAbs → ‖b m‖ ≤ q m.natAbs)
    (k : ℕ) (hk : 0 < k)
    (hs : Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ k * q (n + 2))) :
    ‖∑ m ∈ s, ((m : ℂ) ^ k) • b m‖ ≤
      2 * (M + ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ k * q (n + 2)) := by
  let v : ℕ → ℝ := fun n => if n = 0 then 0 else if n = 1 then M else (n : ℝ) ^ k * q n
  have hv : ∀ n, 0 ≤ v n := by
    intro n
    have hqn := hq n
    dsimp [v]
    split_ifs <;> positivity
  have hv0 : v 0 = 0 := by simp [v]
  have hv1 : v 1 = M := by simp [v]
  have hv2 (n : ℕ) : v (n + 2) = ((n + 2 : ℕ) : ℝ) ^ k * q (n + 2) := by
    simp [v]
  have hvs : Summable (fun n => v (n + 1)) :=
    (summable_nat_add_iff 1).mp (by simpa only [Nat.add_assoc, hv2] using hs)
  have hsum : (∑' n, v (n + 1)) = M + ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ k * q (n + 2) := by
    simpa only [Nat.zero_add, Nat.add_assoc, hv1, hv2] using hvs.tsum_eq_zero_add
  rw [← hsum]
  refine norm_sum_integer_bands_le _ s v hv hv0 hvs fun m => ?_
  rw [norm_smul, norm_pow, Complex.norm_intCast, ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  by_cases hm0 : m.natAbs = 0
  · simp only [hm0, Nat.cast_zero, zero_pow hk.ne', zero_mul, hv0, le_refl]
  · by_cases hm1 : m.natAbs = 1
    · simpa only [hm1, Nat.cast_one, one_pow, one_mul, hv1] using hb m
    · simpa only [v, if_neg hm0, if_neg hm1] using
        mul_le_mul_of_nonneg_left (hfar m (by omega)) (by positivity : 0 ≤ (m.natAbs : ℝ) ^ k)

end DynamicalCStarAlgebras
