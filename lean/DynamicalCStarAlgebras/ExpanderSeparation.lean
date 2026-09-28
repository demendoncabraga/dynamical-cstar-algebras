import DynamicalCStarAlgebras.GraphExpansion

noncomputable section

namespace DynamicalCStarAlgebras

/-- Rounding a quarter-radius costs at most a factor of two for bases between one and two. -/
theorem exp_quarter_radius_le {b r : ℝ} (hb : 1 < b) (hb2 : b ≤ 2) :
    Real.exp (Real.log b / 4 * r) ≤ 2 * b ^ ⌊r / 4⌋₊ := by
  have hlog : 0 ≤ Real.log b := (Real.log_pos hb).le
  have hn := (Nat.lt_floor_add_one (r / 4)).le
  have he : Real.log b / 4 * r ≤ (⌊r / 4⌋₊ : ℝ) * Real.log b + Real.log b := by
    nlinarith [mul_le_mul_of_nonneg_left hn hlog]
  calc
    _ ≤ Real.exp ((⌊r / 4⌋₊ : ℝ) * Real.log b + Real.log b) := Real.exp_le_exp.mpr he
    _ = b ^ ⌊r / 4⌋₊ * b := by rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by linarith)]
    _ ≤ 2 * b ^ ⌊r / 4⌋₊ := by nlinarith [pow_nonneg (by linarith : 0 ≤ b) ⌊r / 4⌋₊]

/-- Vertex expansion gives exponential separation of relative cardinalities at every positive radius. -/
theorem HasVertexExpansion.exponential_separation {X : Type*} [Fintype X]
    {G : SimpleGraph X} {γ : ℝ} (hG : HasVertexExpansion G γ) (hγ : 0 < γ)
    (A B : Finset X) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, r ≤ (G.dist a b : ℝ)) :
    min ((A.card : ℝ) / Fintype.card X) ((B.card : ℝ) / Fintype.card X) ≤
      Real.exp (-(Real.log (min (1 + γ) 2) / 4) * r) := by
  let b : ℝ := min (1 + γ) 2
  have hb : 1 < b := lt_min (by linarith) (by norm_num)
  let n : ℕ := ⌊r / 4⌋₊
  have hn : (n : ℝ) ≤ r / 4 := Nat.floor_le (by positivity)
  have hs : ∀ a ∈ A, ∀ z ∈ B, 2 * n < G.dist a z := by
    intro a ha z hz
    have hd := hsep a ha z hz
    have hn' : ((2 * n : ℕ) : ℝ) < (G.dist a z : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hn'
  have hg := hG.separated_card hγ.le A B n hs
  have hp : b ^ n ≤ (1 + γ) ^ n := pow_le_pow_left₀ (by linarith) (min_le_left _ _) n
  have hm : 0 ≤ min (A.card : ℝ) B.card := by positivity
  have hgeom := (mul_le_mul_of_nonneg_right hp hm).trans hg
  have hexp := exp_quarter_radius_le hb (min_le_right (1 + γ) 2) (r := r)
  have hbound : Real.exp (Real.log b / 4 * r) * min (A.card : ℝ) B.card ≤ Fintype.card X := by
    have he := mul_le_mul_of_nonneg_right hexp hm
    change Real.exp (Real.log b / 4 * r) * min (A.card : ℝ) B.card ≤ 2 * b ^ n * min (A.card : ℝ) B.card at he
    linarith
  by_cases hN : Fintype.card X = 0
  · simp only [hN, Nat.cast_zero, div_zero, min_self]
    positivity
  · have hNpos : (0 : ℝ) < Fintype.card X := by exact_mod_cast Nat.pos_of_ne_zero hN
    rw [min_div_div_right hNpos.le, div_le_iff₀ hNpos]
    rw [show -(Real.log (min (1 + γ) 2) / 4) * r = -(Real.log b / 4 * r) by ring, Real.exp_neg]
    exact (le_inv_mul_iff₀ (Real.exp_pos _)).mpr hbound

/-- One separation constant works for every finite graph with the same positive vertex expansion. -/
theorem vertex_expansion_uniform_separation {γ : ℝ} (hγ : 0 < γ) :
    ∃ κ : ℝ, 1 < κ ∧ ∀ {X : Type*} [Fintype X] (G : SimpleGraph X),
      HasVertexExpansion G γ → ∀ (A B : Finset X) (r : ℝ), 0 ≤ r →
      (∀ a ∈ A, ∀ b ∈ B, r ≤ (G.dist a b : ℝ)) →
      min ((A.card : ℝ) / Fintype.card X) ((B.card : ℝ) / Fintype.card X) ≤ κ ^ (-r / 2) := by
  let b : ℝ := min (1 + γ) 2
  have hb : 1 < b := lt_min (by linarith) (by norm_num)
  let κ := Real.exp (Real.log b / 2)
  have hκ : 1 < κ := Real.one_lt_exp_iff.mpr (half_pos (Real.log_pos hb))
  refine ⟨κ, hκ, ?_⟩
  intro X _ G hG A B r hr hsep
  by_cases hr0 : r = 0
  · subst r
    simp only [neg_zero, zero_div, Real.rpow_zero]
    apply (min_le_left _ _).trans
    by_cases hN : Fintype.card X = 0
    · simp [hN]
    · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hN : (0 : ℝ) < Fintype.card X)).mpr
      exact_mod_cast Finset.card_le_univ A
  · have he := hG.exponential_separation hγ A B (lt_of_le_of_ne hr (Ne.symm hr0)) hsep
    have hid : κ ^ (-r / 2) = Real.exp (-(Real.log b / 4) * r) := by
      rw [Real.rpow_def_of_pos (by positivity : 0 < κ), show Real.log κ = Real.log b / 2 from Real.log_exp _]
      congr 1
      ring
    rw [hid]
    exact he

end DynamicalCStarAlgebras
