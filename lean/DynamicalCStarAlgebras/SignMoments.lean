import DynamicalCStarAlgebras.FiniteSigns

noncomputable section
open Classical
open scoped BigOperators
namespace DynamicalCStarAlgebras

lemma sum_sign_flipInvariant {ι : Type*} [Fintype ι] (i : ι)
    (f : (ι → Bool) → ℝ) (hf : ∀ σ, f (flipSignEquiv i σ) = f σ) :
    ∑ σ : ι → Bool, boolSign (σ i) * f σ = 0 := by
  have he := (flipSignEquiv i).sum_comp (fun σ => boolSign (σ i) * f σ)
  have hn (σ : ι → Bool) : boolSign (flipSignEquiv i σ i) * f (flipSignEquiv i σ) =
      -(boolSign (σ i) * f σ) := by
    rw [hf]
    simp only [flipSignEquiv, Equiv.coe_fn_mk, Function.update_self, boolSign_not, neg_mul]
  simp only [hn, Finset.sum_neg_distrib] at he
  linarith

lemma signed_finset_sum_flip {ι : Type*} [Fintype ι] (s : Finset ι) (a : ι → ℝ)
    {i : ι} (hi : i ∉ s) (σ : ι → Bool) :
    (∑ j ∈ s, boolSign (flipSignEquiv i σ j) * a j) = ∑ j ∈ s, boolSign (σ j) * a j := by
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := fun h => hi (h ▸ hj)
  simp only [flipSignEquiv, Equiv.coe_fn_mk, Function.update_of_ne hji]

/-- Exact second moment and universal fourth-moment bound for any finite signed sum. -/
theorem signed_finset_second_fourth_moments {ι : Type*} [Fintype ι]
    (s : Finset ι) (a : ι → ℝ) :
    (∑ σ : ι → Bool, (∑ i ∈ s, boolSign (σ i) * a i) ^ 2) =
      (Fintype.card (ι → Bool) : ℝ) * ∑ i ∈ s, a i ^ 2 ∧
    (∑ σ : ι → Bool, (∑ i ∈ s, boolSign (σ i) * a i) ^ 4) ≤
      3 * Fintype.card (ι → Bool) * (∑ i ∈ s, a i ^ 2) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    let S (σ : ι → Bool) := ∑ j ∈ s, boolSign (σ j) * a j
    have hz₁ : ∑ σ : ι → Bool, boolSign (σ i) * S σ = 0 :=
      sum_sign_flipInvariant i S (signed_finset_sum_flip s a hi)
    have hz₃ : ∑ σ : ι → Bool, boolSign (σ i) * S σ ^ 3 = 0 :=
      sum_sign_flipInvariant i (fun σ => S σ ^ 3)
        (fun σ => congrArg (fun t : ℝ => t ^ 3) (signed_finset_sum_flip s a hi σ))
    have htwo (σ : ι → Bool) : (boolSign (σ i) * a i + S σ) ^ 2 =
        a i ^ 2 + 2 * a i * (boolSign (σ i) * S σ) + S σ ^ 2 := by
      cases σ i <;> norm_num [boolSign] <;> ring
    have hfour (σ : ι → Bool) : (boolSign (σ i) * a i + S σ) ^ 4 =
        a i ^ 4 + 4 * a i ^ 3 * (boolSign (σ i) * S σ) +
          6 * a i ^ 2 * S σ ^ 2 + 4 * a i * (boolSign (σ i) * S σ ^ 3) + S σ ^ 4 := by
      cases σ i <;> norm_num [boolSign] <;> ring
    simp only [Finset.sum_insert hi]
    change (∑ σ, (boolSign (σ i) * a i + S σ) ^ 2) = _ ∧
      (∑ σ, (boolSign (σ i) * a i + S σ) ^ 4) ≤ _
    constructor
    · simp_rw [htwo, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hz₁]
      change _ + _ + (∑ σ : ι → Bool, (∑ j ∈ s, boolSign (σ j) * a j) ^ 2) = _
      rw [ih.1]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    · simp_rw [hfour, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hz₁, hz₃]
      change _ + _ + _ * (∑ σ : ι → Bool, (∑ j ∈ s, boolSign (σ j) * a j) ^ 2) + _ +
        (∑ σ : ι → Bool, (∑ j ∈ s, boolSign (σ j) * a j) ^ 4) ≤ _
      rw [ih.1]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_zero, add_zero]
      nlinarith [ih.2, mul_nonneg (Nat.cast_nonneg (Fintype.card (ι → Bool)))
        (sq_nonneg (a i ^ 2))]

/-- Normalized finite Rademacher second and fourth moments. -/
theorem expect_signed_finset_second_fourth_moments {ι : Type*} [Fintype ι]
    (s : Finset ι) (a : ι → ℝ) :
    (𝔼 σ : ι → Bool, (∑ i ∈ s, boolSign (σ i) * a i) ^ 2) = ∑ i ∈ s, a i ^ 2 ∧
    (𝔼 σ : ι → Bool, (∑ i ∈ s, boolSign (σ i) * a i) ^ 4) ≤
      3 * (∑ i ∈ s, a i ^ 2) ^ 2 := by
  have hc : (0 : ℝ) < Fintype.card (ι → Bool) := by exact_mod_cast Fintype.card_pos
  obtain ⟨h₂, h₄⟩ := signed_finset_second_fourth_moments s a
  constructor
  · rw [Fintype.expect_eq_sum_div_card, h₂]
    field_simp
  · rw [Fintype.expect_eq_sum_div_card]
    apply (div_le_iff₀ hc).mpr
    nlinarith [h₄]

end DynamicalCStarAlgebras
