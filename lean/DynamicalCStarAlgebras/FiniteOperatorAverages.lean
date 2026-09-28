import DynamicalCStarAlgebras.CosineSmoothing
import Mathlib.Algebra.Order.BigOperators.Expect

noncomputable section
open Classical
open scoped BigOperators
namespace DynamicalCStarAlgebras

/-- A finite uniform average of operators, using the real scalar structure. -/
def operatorAverage {X Ω : Type*} [Fintype Ω] (K : Ω → Operator X) : Operator X :=
  (Fintype.card Ω : ℝ)⁻¹ • ∑ ω, K ω

lemma expect_norm_sq_diagonalMultiplier_le {X Ω : Type*} [Fintype Ω]
    (f : Ω → BoundedDiagonal X) {A : ℝ}
    (hf : ∀ x, (𝔼 ω, ‖f ω x‖ ^ 2) ≤ A ^ 2) (v : HilbertSpace X) :
    (𝔼 ω, ‖diagonalMultiplier (f ω) v‖ ^ 2) ≤ A ^ 2 * ‖v‖ ^ 2 := by
  have hn (w : HilbertSpace X) : HasSum (fun x => ‖w x‖ ^ 2) (‖w‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) w
  have hs := (hasSum_sum fun ω (_hω : ω ∈ (Finset.univ : Finset Ω)) =>
    hn (diagonalMultiplier (f ω) v)).div_const (Fintype.card Ω : ℝ)
  rw [Fintype.expect_eq_sum_div_card]
  refine hasSum_le ?_ hs ((hn v).mul_left (A ^ 2))
  intro x
  simp only [diagonalMultiplier_apply, norm_mul, mul_pow, ← Finset.sum_mul]
  rw [mul_div_right_comm]
  exact mul_le_mul_of_nonneg_right (by simpa only [Fintype.expect_eq_sum_div_card] using hf x)
    (sq_nonneg _)

lemma expect_mul_le_of_sq_bounds {Ω : Type*} [Fintype Ω]
    (f g : Ω → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : (𝔼 ω, f ω ^ 2) ≤ A ^ 2) (hg : (𝔼 ω, g ω ^ 2) ≤ B ^ 2) :
    (𝔼 ω, f ω * g ω) ≤ A * B := by
  have hs := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f g
  apply le_of_sq_le_sq ?_ (mul_nonneg hA hB)
  exact (hs.trans (mul_le_mul hf hg (Finset.expect_nonneg fun _ _ => sq_nonneg _)
    (sq_nonneg _))).trans_eq (mul_pow A B 2).symm

lemma matrixEntry_operatorAverage {X Ω : Type*} [Fintype Ω]
    (K : Ω → Operator X) (x y : X) :
    matrixEntry (operatorAverage K) x y = 𝔼 ω, matrixEntry (K ω) x y := by
  simp only [operatorAverage, matrixEntry, smul_apply,
    sum_apply, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sum,
    Finset.sum_apply, Fintype.expect_eq_sum_div_card]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv,
    mul_comm]

lemma inner_operatorAverage {X Ω : Type*} [Fintype Ω]
    (K : Ω → Operator X) (v w : HilbertSpace X) :
    inner ℂ v (operatorAverage K w) = 𝔼 ω, inner ℂ v (K ω w) := by
  simp only [operatorAverage, smul_apply, sum_apply, inner_smul_right_eq_smul, inner_sum,
    Fintype.expect_eq_sum_div_card, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_natCast, div_eq_mul_inv, mul_comm]

lemma norm_operatorAverage_mul_le {X Ω : Type*} [Fintype Ω]
    (L R : Ω → Operator X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL : ∀ v, (𝔼 ω, ‖L ω v‖ ^ 2) ≤ A ^ 2 * ‖v‖ ^ 2)
    (hR : ∀ v, (𝔼 ω, ‖R ω v‖ ^ 2) ≤ B ^ 2 * ‖v‖ ^ 2) :
    ‖operatorAverage (fun ω => star (L ω) * R ω)‖ ≤ A * B := by
  refine norm_le_of_finiteMatrixForm_bound _ (mul_nonneg hA hB) fun v w => ?_
  rw [finiteMatrixForm_matrixEntry, inner_operatorAverage]
  have hi (ω : Ω) :
      inner ℂ (finiteVector v) ((star (L ω) * R ω) (finiteVector w)) =
        inner ℂ (L ω (finiteVector v)) (R ω (finiteVector w)) := by
    rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
  simp_rw [hi]
  have hn : ‖𝔼 ω, inner ℂ (L ω (finiteVector v)) (R ω (finiteVector w))‖ ≤
      𝔼 ω, ‖inner ℂ (L ω (finiteVector v)) (R ω (finiteVector w))‖ := by
    exact RCLike.norm_expect_le (K := ℂ)
  refine hn.trans ((Finset.expect_le_expect fun ω _ => norm_inner_le_norm _ _).trans ?_)
  have hb := expect_mul_le_of_sq_bounds
    (fun ω => ‖L ω (finiteVector v)‖) (fun ω => ‖R ω (finiteVector w)‖)
    (mul_nonneg hA (norm_nonneg _)) (mul_nonneg hB (norm_nonneg _))
    (by simpa only [mul_pow] using hL (finiteVector v))
    (by simpa only [mul_pow] using hR (finiteVector w))
  exact hb.trans_eq (by ring)

lemma norm_expect_diagonal_sandwich_le {X Ω : Type*} [Fintype Ω]
    (f g : Ω → BoundedDiagonal X) (a : Operator X) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ x, (𝔼 ω, ‖f ω x‖ ^ 2) ≤ A ^ 2)
    (hg : ∀ x, (𝔼 ω, ‖g ω x‖ ^ 2) ≤ B ^ 2) :
    ‖operatorAverage (fun ω => star (diagonalMultiplier (f ω)) * a *
      diagonalMultiplier (g ω))‖ ≤ A * ‖a‖ * B := by
  have hb := norm_operatorAverage_mul_le
    (fun ω => diagonalMultiplier (f ω)) (fun ω => a * diagonalMultiplier (g ω))
    hA (mul_nonneg (norm_nonneg a) hB) (expect_norm_sq_diagonalMultiplier_le f hf) ?_
  · simpa only [mul_assoc] using hb
  intro v
  calc
    (𝔼 ω, ‖(a * diagonalMultiplier (g ω)) v‖ ^ 2) ≤
        𝔼 ω, ‖a‖ ^ 2 * ‖diagonalMultiplier (g ω) v‖ ^ 2 := by
      apply Finset.expect_le_expect
      intro ω _
      rw [mul_apply_eq_comp, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (a.le_opNorm _) 2
    _ = ‖a‖ ^ 2 * (𝔼 ω, ‖diagonalMultiplier (g ω) v‖ ^ 2) :=
      (Finset.mul_expect ..).symm
    _ ≤ ‖a‖ ^ 2 * (B ^ 2 * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (expect_norm_sq_diagonalMultiplier_le g hg v) (sq_nonneg _)
    _ = (‖a‖ * B) ^ 2 * ‖v‖ ^ 2 := by ring

lemma norm_expect_diagonal_mul_le {X Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → BoundedDiagonal X) (K : Ω → Operator X) {A M : ℝ}
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hf : ∀ x, (𝔼 ω, ‖f ω x‖ ^ 2) ≤ A ^ 2) (hK : ∀ ω, ‖K ω‖ ≤ M) :
    ‖operatorAverage (fun ω => star (diagonalMultiplier (f ω)) * K ω)‖ ≤ A * M := by
  apply norm_operatorAverage_mul_le _ _ hA hM (expect_norm_sq_diagonalMultiplier_le f hf)
  intro v
  calc
    (𝔼 ω, ‖K ω v‖ ^ 2) ≤ 𝔼 _ω : Ω, M ^ 2 * ‖v‖ ^ 2 := by
      apply Finset.expect_le_expect
      intro ω _
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (((K ω).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hK ω) (norm_nonneg _))) 2
    _ = M ^ 2 * ‖v‖ ^ 2 := Fintype.expect_const _

lemma operatorAverage_add {X Ω : Type*} [Fintype Ω] (K L : Ω → Operator X) :
    operatorAverage (fun ω => K ω + L ω) = operatorAverage K + operatorAverage L := by
  simp only [operatorAverage, Finset.sum_add_distrib, smul_add]

lemma operatorAverage_sub {X Ω : Type*} [Fintype Ω] (K L : Ω → Operator X) :
    operatorAverage (fun ω => K ω - L ω) = operatorAverage K - operatorAverage L := by
  simp only [operatorAverage, Finset.sum_sub_distrib, smul_sub]

lemma operatorAverage_mul_right {X Ω : Type*} [Fintype Ω]
    (K : Ω → Operator X) (a : Operator X) :
    operatorAverage (fun ω => K ω * a) = operatorAverage K * a := by
  simp only [operatorAverage, ← Finset.sum_mul, smul_mul_assoc]

end DynamicalCStarAlgebras
