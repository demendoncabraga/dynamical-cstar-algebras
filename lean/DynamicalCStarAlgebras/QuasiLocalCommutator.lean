import DynamicalCStarAlgebras.FiniteBands

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

/-- Norm of a real-weighted integer band coefficient. -/
theorem norm_real_mul_intCast (δ : ℝ) (k : ℤ) (hδ : 0 ≤ δ) :
    ‖(δ : ℂ) * (k : ℂ)‖ = δ * |(k : ℝ)| := by
  simp [ ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ]

/-- The two adjacent bands and the remaining finite bands have separate norm bounds. -/
theorem norm_weighted_integer_bands_le {X : Type*} (b : ℤ → Operator X) {N : ℕ}
    (hN : 0 < N) {δ A ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hδN : δ * N ≤ 1) (hb : ∀ k, ‖b k‖ ≤ A)
    (hfar : ∀ k, 1 < |k| → ‖b k‖ ≤ ε) :
    ‖∑ k ∈ Finset.Icc (-(N : ℤ)) N, ((δ : ℂ) * (k : ℂ)) • b k‖ ≤
      2 * δ * A + 2 * N * ε := by
  let s := (Finset.Icc (-(N : ℤ)) N).erase 0
  have he : (∑ k ∈ s, ((δ : ℂ) * (k : ℂ)) • b k) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N, ((δ : ℂ) * (k : ℂ)) • b k :=
    Finset.sum_erase _ (by simp)
  have hpoint : ∀ k ∈ s, ‖((δ : ℂ) * (k : ℂ)) • b k‖ ≤
      ε + (if k = -1 then δ * A else 0) + (if k = 1 then δ * A else 0) := by
    intro k hk
    rw [norm_smul, norm_real_mul_intCast δ k hδ]
    by_cases hm : k = -1
    · simpa [hm] using (mul_le_mul_of_nonneg_left (hb (-1)) hδ).trans
        (le_add_of_nonneg_left hε)
    · by_cases hp : k = 1
      · simpa [hp] using (mul_le_mul_of_nonneg_left (hb 1) hδ).trans
          (le_add_of_nonneg_left hε)
      · have habs : |(k : ℝ)| ≤ (N : ℝ) := by
          exact_mod_cast abs_le.mpr (Finset.mem_Icc.mp (Finset.mem_erase.mp hk).2)
        have hkfar : 1 < |k| := by
          have hk0 := (Finset.mem_erase.mp hk).1
          have h₁ := le_abs_self k
          have h₂ := neg_le_abs k
          omega
        simpa only [if_neg hm, if_neg hp, add_zero, one_mul] using
          mul_le_mul ((mul_le_mul_of_nonneg_left habs hδ).trans hδN)
            (hfar k hkfar) (norm_nonneg _) zero_le_one
  have hcard : s.card = 2 * N := by
    simp only [s, Finset.card_erase_of_mem (show (0 : ℤ) ∈ Finset.Icc (-↑N) ↑N by simp),
      Int.card_Icc]
    omega
  have hm : (-1 : ℤ) ∈ s := by simp only [s, Finset.mem_erase, Finset.mem_Icc]; omega
  have hp : (1 : ℤ) ∈ s := by simp only [s, Finset.mem_erase, Finset.mem_Icc]; omega
  refine he ▸ ((norm_sum_le _ _).trans (Finset.sum_le_sum hpoint)).trans_eq ?_
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_ite_eq',
    hm, hp, if_true, hcard, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- Package a uniformly bounded real function as a complex diagonal. -/
def boundedRealDiagonal {X : Type*} (f : X → ℝ) (M : ℝ) (hf : ∀ x, |f x| ≤ M) :
    BoundedDiagonal X :=
  ⟨fun x => (f x : ℂ), memℓp_infty ⟨M, fun _ ⟨x, hx⟩ => hx ▸ by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hf x⟩⟩

theorem boundedRealDiagonal_apply {X : Type*} (f : X → ℝ) (M : ℝ)
    (hf : ∀ x, |f x| ≤ M) (x : X) : boundedRealDiagonal f M hf x = (f x : ℂ) := rfl

/-- Rounding down to a positive mesh changes a nonnegative value by less than one mesh. -/
theorem real_step_bounds {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) :
    δ * (⌊r / δ⌋₊ : ℝ) ≤ r ∧ r < δ * ((⌊r / δ⌋₊ : ℝ) + 1) := by
  constructor
  · simpa only [mul_comm] using (le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg hr hδ.le))
  · simpa only [mul_comm] using (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (r / δ))

/-- Nearby values lie in the same or adjacent mesh intervals. -/
theorem floor_index_difference_le_one {r q δ : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q)
    (hδ : 0 < δ) (hrq : |r - q| ≤ δ) :
    |(⌊r / δ⌋₊ : ℤ) - (⌊q / δ⌋₊ : ℤ)| ≤ 1 := by
  have hb₁ := real_step_bounds hr hδ
  have hb₂ := real_step_bounds hq hδ
  have hp : (⌊r / δ⌋₊ : ℝ) - (⌊q / δ⌋₊ : ℝ) < 2 := by
    nlinarith [(abs_le.mp hrq).2]
  have hn : (⌊q / δ⌋₊ : ℝ) - (⌊r / δ⌋₊ : ℝ) < 2 := by
    nlinarith [(abs_le.mp hrq).1]
  have hp' : (⌊r / δ⌋₊ : ℤ) - (⌊q / δ⌋₊ : ℤ) < 2 := by exact_mod_cast hp
  have hn' : (⌊q / δ⌋₊ : ℤ) - (⌊r / δ⌋₊ : ℤ) < 2 := by exact_mod_cast hn
  exact abs_le.mpr ⟨by omega, by omega⟩

/-- Nonadjacent level blocks of a slowly varying function are small. -/
theorem norm_floor_band_le {X : Type*} (f : X → ℝ) (hf : ∀ x, 0 ≤ f x)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε) (a : Operator X) {E : Set (X × X)}
    (ha : IsQuasiLocalAt a ε E) (hvar : ∀ p ∈ E, |f p.1 - f p.2| ≤ δ)
    (s : Finset ℤ) (k : ℤ) (hk : 1 < |k|) :
    ‖integerBand (fun x => (⌊f x / δ⌋₊ : ℤ)) s a k‖ ≤ ε := by
  refine norm_integerBand_le _ s a k hε fun j _ => ha _ _ ?_
  refine Set.disjoint_left.mpr fun p hp hE => ?_
  have h := floor_index_difference_le_one (hf p.1) (hf p.2) hδ (hvar p hE)
  have hx : (⌊f p.1 / δ⌋₊ : ℤ) = j + k := hp.1
  have hy : (⌊f p.2 / δ⌋₊ : ℤ) = j := hp.2
  exact (not_le_of_gt hk) (by simpa only [hx, hy, add_sub_cancel_left] using h)

/-- The step-function commutator estimate, before controlling the rounding error. -/
theorem norm_step_commutator_le {X : Type*} (f : X → ℝ) (hf : ∀ x, 0 ≤ f x)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε) (a : Operator X) {E : Set (X × X)}
    (ha : IsQuasiLocalAt a ε E) (hvar : ∀ p ∈ E, |f p.1 - f p.2| ≤ δ)
    (g : BoundedDiagonal X) (hg : ∀ x, g x = (δ : ℂ) * (⌊f x / δ⌋₊ : ℂ))
    {N : ℕ} (hN : 0 < N) (hδN : δ * N ≤ 1) (hfloor : ∀ x, ⌊f x / δ⌋₊ ≤ N) :
    ‖diagonalCommutator g a‖ ≤ 2 * δ * ‖a‖ + 2 * N * ε := by
  rw [diagonalCommutator_eq_sum_integerBand g (fun x => (⌊f x / δ⌋₊ : ℤ))
    (Finset.Icc 0 N) (Finset.Icc (-(N : ℤ)) N) a δ (by simpa using hg)
    (fun x => Finset.mem_Icc.mpr ⟨by positivity, by exact_mod_cast hfloor x⟩)
    (fun x y => Finset.mem_Icc.mpr ⟨by have := hfloor y; omega,
      by have := hfloor x; omega⟩)]
  exact norm_weighted_integer_bands_le _ hN hδ.le hε hδN
    (fun k => norm_integerBand_le _ _ a k (norm_nonneg _)
      (fun j _ => compression_norm_le a _ _))
    (fun k hk => norm_floor_band_le f hf hδ hε a ha hvar _ k hk)

theorem diagonalCommutator_sub_left {X : Type*} (f g : BoundedDiagonal X) (a : Operator X) :
    diagonalCommutator (f - g) a = diagonalCommutator f a - diagonalCommutator g a := by
  refine operator_ext fun x y => ?_
  change _ = (matrixEntryCLM x y) (_ - _)
  simp only [map_sub, matrixEntryCLM_apply, matrixEntry_diagonalCommutator, lp.coeFn_sub, Pi.sub_apply]
  ring

theorem norm_diagonalCommutator_perturb {X : Type*} (f g : BoundedDiagonal X)
    (a : Operator X) :
    ‖diagonalCommutator f a‖ ≤ 2 * ‖f - g‖ * ‖a‖ + ‖diagonalCommutator g a‖ := by
  have h := norm_add_le (diagonalCommutator f a - diagonalCommutator g a)
    (diagonalCommutator g a)
  rw [sub_add_cancel, ← diagonalCommutator_sub_left] at h
  exact h.trans (add_le_add (diagonalCommutator_norm_le (f - g) a) le_rfl)

/-- The sharp quasi-local commutator estimate for real diagonals valued in `[0,1]`. -/
theorem quasiLocal_commutator_bound {X : Type*} (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (a : Operator X) {E : Set (X × X)} (ha : IsQuasiLocalAt a ε E)
    (hvar : ∀ p ∈ E, |f p.1 - f p.2| ≤ δ) :
    ‖diagonalCommutator (boundedRealDiagonal f 1
      (fun x => (abs_of_nonneg (hf x).1).trans_le (hf x).2)) a‖ ≤
      4 * δ * ‖a‖ + 2 * δ⁻¹ * ε := by
  let F := boundedRealDiagonal f 1 (fun x => (abs_of_nonneg (hf x).1).trans_le (hf x).2)
  have hF : ‖F‖ ≤ 1 := lp.norm_le_of_forall_le zero_le_one (fun x => by
    simpa only [F, boundedRealDiagonal_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hf x).1] using (hf x).2)
  by_cases hlarge : 1 ≤ δ
  · have h := diagonalCommutator_norm_le F a
    have hpos : 0 ≤ δ⁻¹ * ε := mul_nonneg (inv_nonneg.mpr hδ.le) hε
    change ‖diagonalCommutator F a‖ ≤ _
    nlinarith [norm_nonneg a]
  · let g : X → ℝ := fun x => δ * (⌊f x / δ⌋₊ : ℝ)
    have hg : ∀ x, 0 ≤ g x ∧ g x ≤ f x := fun x =>
      ⟨mul_nonneg hδ.le (Nat.cast_nonneg _), (real_step_bounds (hf x).1 hδ).1⟩
    let G := boundedRealDiagonal g 1 (fun x =>
      (abs_of_nonneg (hg x).1).trans_le ((hg x).2.trans (hf x).2))
    have hdiff : ‖F - G‖ ≤ δ := by
      refine lp.norm_le_of_forall_le hδ.le fun x => ?_
      change ‖((f x : ℂ) - (g x : ℂ))‖ ≤ δ
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (hg x).2)]
      have hb := (real_step_bounds (hf x).1 hδ).2
      dsimp [g]
      linarith
    have hN : 0 < ⌊δ⁻¹⌋₊ := Nat.floor_pos.mpr (by
      rw [one_le_inv₀ hδ]
      exact le_of_lt (lt_of_not_ge hlarge))
    have hbound : (⌊δ⁻¹⌋₊ : ℝ) ≤ δ⁻¹ := Nat.floor_le (inv_nonneg.mpr hδ.le)
    have hδN : δ * (⌊δ⁻¹⌋₊ : ℝ) ≤ 1 := by
      simpa only [mul_inv_cancel₀ hδ.ne'] using mul_le_mul_of_nonneg_left hbound hδ.le
    have hstep := norm_step_commutator_le f (fun x => (hf x).1) hδ hε a ha hvar G
      (fun x => by simp only [G, g, boundedRealDiagonal_apply, Complex.ofReal_mul, Complex.ofReal_natCast])
      hN hδN (fun x => Nat.floor_le_floor (by
        simpa only [one_div] using div_le_div_of_nonneg_right (hf x).2 hδ.le))
    have hp := norm_diagonalCommutator_perturb F G a
    change ‖diagonalCommutator F a‖ ≤ _
    nlinarith [mul_le_mul_of_nonneg_right hdiff (norm_nonneg a),
      mul_le_mul_of_nonneg_right hbound hε]

end DynamicalCStarAlgebras
