import DynamicalCStarAlgebras.CosinePartition

noncomputable section

namespace DynamicalCStarAlgebras

/-- The signed diagonal functions used in the smoothing argument. -/
def signedCosinePartition (L : ℝ) (σ : ℤ → ℝ) (t : ℝ) : ℝ :=
  ∑' k : ℤ, σ k * cosinePartition L k t

lemma signedCosinePartition_eq_sum (L : ℝ) (σ : ℤ → ℝ) (t : ℝ) (F : Finset ℤ)
    (hF : ⌊t / L⌋ ∈ F ∧ ⌊t / L⌋ + 1 ∈ F) :
    signedCosinePartition L σ t = ∑ k ∈ F, σ k * cosinePartition L k t := by
  apply tsum_eq_sum
  intro k hk
  have hk₀ : k ≠ ⌊t / L⌋ := fun he => hk (he ▸ hF.1)
  have hk₁ : k ≠ ⌊t / L⌋ + 1 := fun he => hk (he ▸ hF.2)
  rw [cosinePartition_eq_zero_of_index_ne hk₀ hk₁, mul_zero]

lemma signedCosinePartition_abs_le (L : ℝ) (σ : ℤ → ℝ) (hσ : ∀ k, |σ k| ≤ 1) (t : ℝ) :
    |signedCosinePartition L σ t| ≤ 2 := by
  classical
  have hq : ⌊t / L⌋ ≠ ⌊t / L⌋ + 1 := by omega
  rw [signedCosinePartition_eq_sum L σ t {⌊t / L⌋, ⌊t / L⌋ + 1} (by simp)]
  simp only [Finset.sum_insert, Finset.mem_singleton, hq, not_false_eq_true, Finset.sum_singleton]
  have hp (k : ℤ) : |σ k * cosinePartition L k t| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (cosinePartition_mem_unitInterval L k t).1]
    exact (mul_le_mul_of_nonneg_right (hσ k) (cosinePartition_mem_unitInterval L k t).1).trans
      (by simpa only [one_mul] using (cosinePartition_mem_unitInterval L k t).2)
  exact (abs_add_le _ _).trans (by linarith [hp ⌊t / L⌋, hp (⌊t / L⌋ + 1)])

/-- Each signed partition is uniformly Lipschitz, independently of its signs. -/
lemma signedCosinePartition_sub_bound {L : ℝ} (hL : 0 < L) (σ : ℤ → ℝ)
    (hσ : ∀ k, |σ k| ≤ 1) (t u : ℝ) :
    |signedCosinePartition L σ t - signedCosinePartition L σ u| ≤
      2 * Real.pi / L * |t - u| := by
  classical
  let F : Finset ℤ := {⌊t / L⌋, ⌊t / L⌋ + 1} ∪ {⌊u / L⌋, ⌊u / L⌋ + 1}
  rw [signedCosinePartition_eq_sum L σ t F (by simp [F]),
    signedCosinePartition_eq_sum L σ u F (by simp [F]), ← Finset.sum_sub_distrib]
  have hterm (k : ℤ) :
      |σ k * cosinePartition L k t - σ k * cosinePartition L k u| ≤
        Real.pi / (2 * L) * |t - u| := by
    rw [← mul_sub, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hσ k)).trans
      (cosinePartition_sub_bound hL k)
  have hcard : F.card ≤ 4 := by
    have := Finset.card_union_le {⌊t / L⌋, ⌊t / L⌋ + 1} {⌊u / L⌋, ⌊u / L⌋ + 1}
    have ht := Finset.card_insert_le ⌊t / L⌋ {⌊t / L⌋ + 1}
    have hu := Finset.card_insert_le ⌊u / L⌋ {⌊u / L⌋ + 1}
    simp only [Finset.card_singleton] at ht hu
    dsimp [F]
    omega
  calc
    _ ≤ ∑ k ∈ F, |σ k * cosinePartition L k t - σ k * cosinePartition L k u| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le F
        (fun k => σ k * cosinePartition L k t - σ k * cosinePartition L k u)
    _ ≤ ∑ _k ∈ F, Real.pi / (2 * L) * |t - u| := Finset.sum_le_sum fun k _ => hterm k
    _ = (F.card : ℝ) * (Real.pi / (2 * L) * |t - u|) := by simp
    _ ≤ 4 * (Real.pi / (2 * L) * |t - u|) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by ring

/-- Rescale the unit-interval commutator estimate to a real diagonal bounded by two. -/
lemma boundedRealDiagonal_commutator_bound_two {X : Type*} (f : X → ℝ)
    (hf : ∀ x, |f x| ≤ 2) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (a : Operator X) {E : Set (X × X)} (ha : IsQuasiLocalAt a ε E)
    (hvar : ∀ p ∈ E, |f p.1 - f p.2| ≤ 4 * δ) :
    ‖diagonalCommutator (boundedRealDiagonal f 2 hf) a‖ ≤
      16 * δ * ‖a‖ + 8 * δ⁻¹ * ε := by
  let g : X → ℝ := fun x => (f x + 2) / 4
  have hg (x : X) : 0 ≤ g x ∧ g x ≤ 1 := by
    have h := abs_le.mp (hf x)
    dsimp [g]
    constructor <;> linarith
  have hvg : ∀ p ∈ E, |g p.1 - g p.2| ≤ δ := by
    intro p hp
    rw [show g p.1 - g p.2 = (f p.1 - f p.2) / 4 by dsimp [g]; ring,
      abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr (by linarith [hvar p hp])
  let G := boundedRealDiagonal g 1
    (fun x => (abs_of_nonneg (hg x).1).trans_le (hg x).2)
  have he : diagonalCommutator (boundedRealDiagonal f 2 hf) a =
      (4 : ℂ) • diagonalCommutator G a := by
    refine operator_ext fun x y => ?_
    change _ = (matrixEntryCLM x y) ((4 : ℂ) • _)
    simp only [map_smul, matrixEntryCLM_apply, matrixEntry_diagonalCommutator,
      boundedRealDiagonal_apply, G, g, smul_eq_mul, Complex.ofReal_div,
      Complex.ofReal_add, Complex.ofReal_ofNat]
    ring
  have hbound := quasiLocal_commutator_bound g hg hδ hε a ha hvg
  rw [he, norm_smul]
  norm_num only [Complex.norm_ofNat]
  change ‖diagonalCommutator G a‖ ≤ _ at hbound
  linarith

/-- The source smoothing proof's signed commutator bound, with its exact constants. -/
theorem signedCosinePartition_commutator_bound {X : Type*} (h : X → ℝ)
    {ω δ ε : ℝ} (hω : 0 < ω) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (a : Operator X) {E : Set (X × X)} (ha : IsQuasiLocalAt a ε E)
    (hvar : ∀ p ∈ E, |h p.1 - h p.2| ≤ ω)
    (σ : ℤ → ℝ) (hσ : ∀ k, |σ k| ≤ 1) :
    ‖diagonalCommutator
      (boundedRealDiagonal (fun x => signedCosinePartition (Real.pi * ω / δ) σ (h x))
        2 (fun x => signedCosinePartition_abs_le _ σ hσ (h x))) a‖ ≤
      16 * δ * ‖a‖ + 8 * δ⁻¹ * ε := by
  apply boundedRealDiagonal_commutator_bound_two _ _ hδ hε a ha
  intro p hp
  have hL : 0 < Real.pi * ω / δ := by positivity
  calc
    _ ≤ 2 * Real.pi / (Real.pi * ω / δ) * |h p.1 - h p.2| :=
      signedCosinePartition_sub_bound hL σ hσ _ _
    _ ≤ 2 * Real.pi / (Real.pi * ω / δ) * ω :=
      mul_le_mul_of_nonneg_left (hvar p hp) (by positivity)
    _ = 2 * δ := by field_simp
    _ ≤ 4 * δ := by linarith

end DynamicalCStarAlgebras
