import DynamicalCStarAlgebras.WeakIntegral

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- Real signs indexed by Booleans. -/
def boolSign (b : Bool) : ℝ := if b then 1 else -1

lemma boolSign_not (b : Bool) : boolSign (!b) = -boolSign b := by
  cases b <;> norm_num [boolSign]

/-- Flipping one coordinate permutes the finite set of all sign choices. -/
def flipSignEquiv {ι : Type*} (i : ι) : (ι → Bool) ≃ (ι → Bool) where
  toFun ε := Function.update ε i (!(ε i))
  invFun ε := Function.update ε i (!(ε i))
  left_inv ε := by
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [Function.update_of_ne h]
  right_inv ε := by
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [Function.update_of_ne h]

lemma sum_boolSign_mul {ι : Type*} [Fintype ι] (i j : ι) :
    ∑ ε : ι → Bool, boolSign (ε i) * boolSign (ε j) =
      if i = j then (Fintype.card (ι → Bool) : ℝ) else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    have hs (ε : ι → Bool) : boolSign (ε i) * boolSign (ε i) = 1 := by
      cases ε i <;> norm_num [boolSign]
    simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · rw [if_neg hij]
    have he := (flipSignEquiv i).sum_comp (fun ε : ι → Bool => boolSign (ε i) * boolSign (ε j))
    have hn : ∀ ε : ι → Bool,
        boolSign (flipSignEquiv i ε i) * boolSign (flipSignEquiv i ε j) =
          -(boolSign (ε i) * boolSign (ε j)) := by
      intro ε
      simp only [flipSignEquiv, Equiv.coe_fn_mk, Function.update_self,
        Function.update_of_ne (Ne.symm hij), boolSign_not, neg_mul]
    simp only [hn, Finset.sum_neg_distrib] at he
    linarith

/-- Finite sign orthogonality in a real Hilbert space; complex Hilbert spaces
also carry this real inner product. -/
theorem sum_signed_norm_sq {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (v : ι → H) :
    ∑ ε : ι → Bool, ‖∑ i, boolSign (ε i) • v i‖ ^ 2 =
      (Fintype.card (ι → Bool) : ℝ) * ∑ i, ‖v i‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc]
  have hsum (i : ι) :
      ∑ ε : ι → Bool, ∑ j : ι, boolSign (ε i) * boolSign (ε j) * inner ℝ (v j) (v i) =
        (Fintype.card (ι → Bool) : ℝ) * inner ℝ (v i) (v i) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, sum_boolSign_mul]
    simp
  simp only [hsum, Finset.mul_sum]

/-- A uniform bound for all signed sums bounds the sum of squared norms.
This is the finite-sign averaging step in the smoothing lemma. -/
theorem sum_norm_sq_le_of_signed_sum_bound {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (v : ι → H) {M : ℝ} (_hM : 0 ≤ M)
    (hv : ∀ ε : ι → Bool, ‖∑ i, boolSign (ε i) • v i‖ ≤ M) :
    ∑ i, ‖v i‖ ^ 2 ≤ M ^ 2 := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun ε _ =>
    pow_le_pow_left₀ (norm_nonneg _) (hv ε) 2)
  rw [sum_signed_norm_sq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  exact (mul_le_mul_iff_right₀ (by exact_mod_cast Fintype.card_pos :
    (0 : ℝ) < Fintype.card (ι → Bool))).mp hh

/-- The finite-subset form for complex Hilbert vectors and arbitrary real signs
of absolute value at most one. -/
theorem finset_sum_norm_sq_le_of_signed_sum_bound {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (s : Finset ι) (v : ι → H)
    {M : ℝ} (hM : 0 ≤ M)
    (hv : ∀ σ : ι → ℝ, (∀ i, |σ i| ≤ 1) →
      ‖∑ i ∈ s, (σ i : ℂ) • v i‖ ≤ M) : ∑ i ∈ s, ‖v i‖ ^ 2 ≤ M ^ 2 := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  rw [← Finset.sum_coe_sort s (fun i => ‖v i‖ ^ 2)]
  apply sum_norm_sq_le_of_signed_sum_bound (fun i : s => v i) hM
  intro ε
  let σ (i : ι) : ℝ := if hi : i ∈ s then boolSign (ε ⟨i, hi⟩) else 0
  have hσ (i : ι) : |σ i| ≤ 1 := by
    dsimp [σ]
    split_ifs with hi
    · cases ε ⟨i, hi⟩ <;> norm_num [boolSign]
    · norm_num
  have h := hv σ hσ
  have he : (∑ i : s, boolSign (ε i) • v i) = ∑ i ∈ s, (σ i : ℂ) • v i := by
    calc
      _ = ∑ i : s, (σ i : ℂ) • v i := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [σ, dif_pos i.property, RCLike.real_smul_eq_coe_smul (K := ℂ)]
        rfl
      _ = _ := by simpa only using! (Finset.sum_coe_sort s (fun i => (σ i : ℂ) • v i))
  rw [he]
  exact h

end DynamicalCStarAlgebras
