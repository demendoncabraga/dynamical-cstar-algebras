import DynamicalCStarAlgebras.CosineSmoothing
import DynamicalCStarAlgebras.FiniteSigns

noncomputable section
namespace DynamicalCStarAlgebras

lemma sum_smul_cosineCommutator_bound {X : Type*} (h : X → ℝ)
    {ω δ ε : ℝ} (hω : 0 < ω) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (a : Operator X) {E : Set (X × X)} (ha : IsQuasiLocalAt a ε E)
    (hvar : ∀ p ∈ E, |h p.1 - h p.2| ≤ ω)
    (s : Finset ℤ) (σ : ℤ → ℝ) (hσ : ∀ k, |σ k| ≤ 1) :
    ‖∑ k ∈ s, (σ k : ℂ) • diagonalCommutator (cosineDiagonal h (Real.pi * ω / δ) k) a‖ ≤
      16 * δ * ‖a‖ + 8 * δ⁻¹ * ε := by
  classical
  let L := Real.pi * ω / δ
  let τ : ℤ → ℝ := fun k => if k ∈ s then σ k else 0
  have hτ : ∀ k, |τ k| ≤ 1 := by
    intro k
    dsimp [τ]
    split_ifs <;> simp_all
  have ht (t : ℝ) : signedCosinePartition L τ t =
      ∑ k ∈ s, σ k * cosinePartition L k t := by
    unfold signedCosinePartition
    rw [tsum_eq_sum (s := s) (fun k hk => by simp [τ, hk])]
    exact Finset.sum_congr rfl fun k hk => by simp [τ, hk]
  have he : (∑ k ∈ s, (σ k : ℂ) • diagonalCommutator (cosineDiagonal h L k) a) =
      diagonalCommutator (boundedRealDiagonal (fun x => signedCosinePartition L τ (h x)) 2
        (fun x => signedCosinePartition_abs_le L τ hτ (h x))) a := by
    refine operator_ext fun x y => ?_
    change (matrixEntryCLM x y) (∑ k ∈ s, _) = _
    simp only [map_sum, map_smul, matrixEntryCLM_apply, matrixEntry_diagonalCommutator,
      cosineDiagonal_apply, boundedRealDiagonal_apply, smul_eq_mul, ht,
      Complex.ofReal_sum, Complex.ofReal_mul, ← Finset.sum_sub_distrib, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  change ‖∑ k ∈ s, (σ k : ℂ) • diagonalCommutator (cosineDiagonal h L k) a‖ ≤ _
  rw [he]
  exact signedCosinePartition_commutator_bound h hω hδ hε a ha hvar τ hτ

lemma cosineCommutator_sum_norm_sq_le {X : Type*} (h : X → ℝ) (L : ℝ) (a : Operator X)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ (s : Finset ℤ) (σ : ℤ → ℝ), (∀ k, |σ k| ≤ 1) →
      ‖∑ k ∈ s, (σ k : ℂ) • diagonalCommutator (cosineDiagonal h L k) a‖ ≤ C)
    (s : Finset ℤ) (w : HilbertSpace X) :
    ∑ k ∈ s, ‖diagonalCommutator (cosineDiagonal h L k) a w‖ ^ 2 ≤ (C * ‖w‖) ^ 2 := by
  apply finset_sum_norm_sq_le_of_signed_sum_bound s _ (mul_nonneg hC (norm_nonneg _))
  intro σ hσ
  have hv := (∑ k ∈ s, (σ k : ℂ) • diagonalCommutator (cosineDiagonal h L k) a).le_opNorm w
  simpa only [sum_apply, smul_apply] using hv.trans
    (mul_le_mul_of_nonneg_right (hb s σ hσ) (norm_nonneg _))

lemma cosineCommutator_row_bound {X : Type*} (h : X → ℝ) (L : ℝ) (a : Operator X)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ (s : Finset ℤ) (σ : ℤ → ℝ), (∀ k, |σ k| ≤ 1) →
      ‖∑ k ∈ s, (σ k : ℂ) • diagonalCommutator (cosineDiagonal h L k) a‖ ≤ C)
    (s : Finset ℤ) (v w : HilbertSpace X) :
    ‖∑ k ∈ s, inner ℂ (diagonalMultiplier (cosineDiagonal h L k) v)
      (diagonalCommutator (cosineDiagonal h L k) a w)‖ ≤ C * ‖v‖ * ‖w‖ := by
  have hrow := sum_norm_sq_diagonalMultiplier_le s (cosineDiagonal h L)
    (sum_norm_sq_cosineDiagonal_le h L s) v
  have hcol := cosineCommutator_sum_norm_sq_le h L a hC hb s w
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun k => ‖diagonalMultiplier (cosineDiagonal h L k) v‖)
    (fun k => ‖diagonalCommutator (cosineDiagonal h L k) a w‖)
  have hprod : (∑ k ∈ s, ‖diagonalMultiplier (cosineDiagonal h L k) v‖ *
      ‖diagonalCommutator (cosineDiagonal h L k) a w‖) ≤ C * ‖v‖ * ‖w‖ := by
    apply le_of_sq_le_sq _ (by positivity)
    exact (hcs.trans (mul_le_mul hrow hcol
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _))).trans_eq (by ring)
  exact ((norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_inner_le_norm _ _)).trans hprod

lemma matrixEntry_star_diagonal_mul {X : Type*} (f : BoundedDiagonal X)
    (a : Operator X) (x y : X) :
    matrixEntry (star (diagonalMultiplier f) * a) x y = star (f x) * matrixEntry a x y := by
  rw [← diagonalMultiplier_star]
  rfl

set_option maxHeartbeats 600000 in
lemma cosineSmoothing_error_bound_of_commutators {X : Type*} (h : X → ℝ) (L : ℝ) (a : Operator X)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ (s : Finset ℤ) (σ : ℤ → ℝ), (∀ k, |σ k| ≤ 1) →
      ‖∑ k ∈ s, (σ k : ℂ) • diagonalCommutator (cosineDiagonal h L k) a‖ ≤ C) :
    ‖a - cosineSmoothing h L a‖ ≤ C := by
  classical
  refine norm_le_of_finiteMatrixForm_bound _ hC fun v w => ?_
  let s : Finset ℤ := v.support.biUnion fun x => {⌊h x / L⌋, ⌊h x / L⌋ + 1}
  let b : Operator X := ∑ k ∈ s, star (diagonalMultiplier (cosineDiagonal h L k)) *
    diagonalCommutator (cosineDiagonal h L k) a
  have he : finiteMatrixForm (matrixEntry (a - cosineSmoothing h L a)) v w =
      finiteMatrixForm (matrixEntry b) v w := by
    simp only [finiteMatrixForm_apply]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y _hy => ?_
    congr 2
    have hs : ⌊h x / L⌋ ∈ s ∧ ⌊h x / L⌋ + 1 ∈ s := by
      constructor <;> exact Finset.mem_biUnion.mpr ⟨x, hx, by simp⟩
    have hsq : (∑ k ∈ s, cosinePartition L k (h x) ^ 2) = 1 := by
      rw [← cosinePartition_sum_sq L (h x)]
      symm
      apply tsum_eq_sum
      intro k hk
      have hk₀ : k ≠ ⌊h x / L⌋ := fun he => hk (he ▸ hs.1)
      have hk₁ : k ≠ ⌊h x / L⌋ + 1 := fun he => hk (he ▸ hs.2)
      rw [cosinePartition_eq_zero_of_index_ne hk₀ hk₁, zero_pow (by decide : 2 ≠ 0)]
    change (matrixEntryCLM x y) (_ - _) = (matrixEntryCLM x y) (∑ k ∈ s, _)
    simp only [map_sub, map_sum, matrixEntryCLM_apply, matrixEntry_star_diagonal_mul,
      matrixEntry_diagonalCommutator, cosineDiagonal_apply, Complex.star_def, Complex.conj_ofReal,
      matrixEntry_cosineSmoothing, cosineSmoothingMatrix_eq_sum h L a x y s hs]
    calc
      _ = (∑ k ∈ s, (cosinePartition L k (h x) : ℂ) ^ 2) * matrixEntry a x y -
        ∑ k ∈ s, (cosinePartition L k (h x) : ℂ) * matrixEntry a x y *
          (cosinePartition L k (h y) : ℂ) := by
        have hsqC : (∑ k ∈ s, (cosinePartition L k (h x) : ℂ) ^ 2) = 1 := by
          exact_mod_cast hsq
        rw [hsqC, one_mul]
      _ = _ := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
  rw [he, finiteMatrixForm_matrixEntry]
  dsimp only [b]
  simp only [sum_apply, inner_sum, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact cosineCommutator_row_bound h L a hC hb s (finiteVector v) (finiteVector w)

/-- The source smoothing operator satisfies the exact error estimate. -/
theorem cosineSmoothing_error_bound {X : Type*} (h : X → ℝ)
    {ω δ ε : ℝ} (hω : 0 < ω) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (a : Operator X) {E : Set (X × X)} (ha : IsQuasiLocalAt a ε E)
    (hvar : ∀ p ∈ E, |h p.1 - h p.2| ≤ ω) :
    ‖a - cosineSmoothing h (Real.pi * ω / δ) a‖ ≤
      16 * δ * ‖a‖ + 8 * δ⁻¹ * ε := by
  apply cosineSmoothing_error_bound_of_commutators h _ a (by positivity)
  exact fun s σ hσ => sum_smul_cosineCommutator_bound h hω hδ hε a ha hvar s σ hσ

end DynamicalCStarAlgebras
