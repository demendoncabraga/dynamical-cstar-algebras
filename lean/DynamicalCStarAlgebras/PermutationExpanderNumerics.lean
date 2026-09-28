import Mathlib
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.Complex.Exponential

/-!
Adapted from the checked finite counting construction in
the same-author sibling paper-formalization project, specifically
`propertyH_lean/lean/PropertyH/ExpanderNumerics.lean`. The proofs below are included in full and checked with this repository's
Lean/Mathlib pins; no declaration from the sibling project is imported.
-/

noncomputable section
namespace DynamicalCStarAlgebras.PermutationExpanders

/-- A convenient coarse binomial bound for the expander union estimate. -/
theorem choose_le_three_mul_div_pow (n a : ℕ) (ha : 0 < a) :
    (n.choose a : ℝ) ≤ (3 * n / a)^a := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hchoose := Nat.choose_le_pow_div (α := ℝ) a n
  have hfac := Real.pow_div_factorial_le_exp (a : ℝ) haR.le a
  have hexp : Real.exp (a : ℝ) ≤ (3 : ℝ)^a := by
    rw [← mul_one (a : ℝ), Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) a
  rw [div_pow]
  apply (le_div_iff₀ (pow_pos haR a)).mpr
  calc
    _ ≤ ((n : ℝ)^a / a.factorial) * (a : ℝ)^a :=
      mul_le_mul_of_nonneg_right hchoose (pow_nonneg haR.le _)
    _ = (n : ℝ)^a * ((a : ℝ)^a / a.factorial) := by ring
    _ ≤ (n : ℝ)^a * (3 : ℝ)^a :=
      mul_le_mul_of_nonneg_left (hfac.trans hexp) (by positivity)
    _ = _ := by ring

/-- Numerical decay for 32 independent permutations. -/
theorem permutation_union_base_bound (x : ℝ) (hx : 0 < x) (hxhalf : x ≤ 1/2) :
    2 * (3/x)^2 * (3*x/2)^32 ≤ (1/4 : ℝ) := by
  have heq : 2 * (3/x)^2 * (3*x/2)^32 = (18 * (3/2 : ℝ)^32) * x^30 := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ (18 * (3/2 : ℝ)^32) * (1/2 : ℝ)^30 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.le hxhalf 30) (by positivity)
    _ ≤ _ := by norm_num

/-- Total bad-cut probability at a given nonzero cardinality is geometrically small. -/
theorem permutation_union_cardinality_bound (n a : ℕ) (ha : 0 < a) (han : 2*a ≤ n) :
    ((a : ℝ)+1) * (n.choose a : ℝ)^2 * (3*(a : ℝ)/(2*n))^(32*a) ≤ (1/4 : ℝ)^a := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx : 0 < (a : ℝ)/n := div_pos haR hnR
  have hhalf : (a : ℝ)/n ≤ 1/2 := by
    apply (div_le_iff₀ hnR).mpr
    have hn : (2 : ℝ)*a ≤ n := by exact_mod_cast han
    linarith
  have hc : (n.choose a : ℝ) ≤ (3 / ((a : ℝ)/n))^a := by
    convert choose_le_three_mul_div_pow n a ha using 1
    field_simp
  have ha2 : (a : ℝ)+1 ≤ (2 : ℝ)^a := by exact_mod_cast Nat.lt_two_pow_self (n := a)
  have hy : 3*(a : ℝ)/(2*n) = 3*((a : ℝ)/n)/2 := by ring
  rw [hy, pow_mul]
  calc
    _ ≤ (2 : ℝ)^a * ((3 / ((a : ℝ)/n))^a)^2 * ((3*((a : ℝ)/n)/2)^32)^a := by
      gcongr
    _ = (2 * (3/((a : ℝ)/n))^2 * (3*((a : ℝ)/n)/2)^32)^a := by
      simp only [mul_pow, ← pow_mul, Nat.mul_comm a 2]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (permutation_union_base_bound _ hx hhalf) _

/-- Summing the union estimates leaves strictly positive probability of success. -/
theorem permutation_union_total_lt_one (n : ℕ) :
    (∑ a ∈ Finset.Icc 1 (n/2), ((a : ℝ)+1) * (n.choose a : ℝ)^2 *
      (3*(a : ℝ)/(2*n))^(32*a)) < 1 := by
  have hs : (∑ a ∈ Finset.Icc 1 (n/2), ((a : ℝ)+1) * (n.choose a : ℝ)^2 *
      (3*(a : ℝ)/(2*n))^(32*a)) ≤ ∑ a ∈ Finset.Icc 1 (n/2), (1/4 : ℝ)^a := by
    apply Finset.sum_le_sum
    intro a ha
    have hmem := Finset.mem_Icc.mp ha
    exact permutation_union_cardinality_bound n a (by omega) (by omega)
  apply hs.trans_lt
  have hi : Finset.Icc 1 (n/2) = Finset.Ico 1 (n/2+1) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hi, geom_sum_Ico (by norm_num : (1/4 : ℝ) ≠ 1) (by omega)]
  have hpos : 0 < (1/4 : ℝ)^(n/2+1) := by positivity
  norm_num
  linarith
end DynamicalCStarAlgebras.PermutationExpanders
