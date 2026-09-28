import DynamicalCStarAlgebras.SignedCosinePartition

noncomputable section
namespace DynamicalCStarAlgebras
open scoped ComplexOrder

lemma sum_norm_sq_diagonalMultiplier_le {X ι : Type*} (s : Finset ι)
    (f : ι → BoundedDiagonal X)
    (hf : ∀ x, ∑ i ∈ s, ‖f i x‖ ^ 2 ≤ 1) (v : HilbertSpace X) :
    ∑ i ∈ s, ‖diagonalMultiplier (f i) v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  have hn (w : HilbertSpace X) : HasSum (fun x => ‖w x‖ ^ 2) (‖w‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) w
  have hs := hasSum_sum fun i (_hi : i ∈ s) => hn (diagonalMultiplier (f i) v)
  have hv := hn v
  refine hasSum_le ?_ hs hv
  intro x
  simp only [diagonalMultiplier_apply, norm_mul, mul_pow, ← Finset.sum_mul]
  exact (mul_le_mul_of_nonneg_right (hf x) (sq_nonneg _)).trans_eq (one_mul _)

lemma sum_diagonal_norm_mul_le {X ι : Type*} (s : Finset ι)
    (f : ι → BoundedDiagonal X)
    (hf : ∀ x, ∑ i ∈ s, ‖f i x‖ ^ 2 ≤ 1) (v w : HilbertSpace X) :
    ∑ i ∈ s, ‖diagonalMultiplier (f i) v‖ * ‖diagonalMultiplier (f i) w‖ ≤ ‖v‖ * ‖w‖ := by
  have hs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => ‖diagonalMultiplier (f i) v‖) (fun i => ‖diagonalMultiplier (f i) w‖)
  exact le_of_sq_le_sq ((hs.trans (mul_le_mul
    (sum_norm_sq_diagonalMultiplier_le s f hf v)
    (sum_norm_sq_diagonalMultiplier_le s f hf w)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _))).trans_eq (mul_pow _ _ 2).symm)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

lemma norm_sum_diagonal_sandwich_le {X ι : Type*} (s : Finset ι)
    (f : ι → BoundedDiagonal X)
    (hf : ∀ x, ∑ i ∈ s, ‖f i x‖ ^ 2 ≤ 1) (a : Operator X) :
    ‖∑ i ∈ s, star (diagonalMultiplier (f i)) * a * diagonalMultiplier (f i)‖ ≤ ‖a‖ := by
  refine norm_le_of_finiteMatrixForm_bound _ (norm_nonneg _) fun v w => ?_
  rw [finiteMatrixForm_matrixEntry, sum_apply, inner_sum]
  have hb : ∀ i ∈ s,
      ‖inner ℂ (finiteVector v)
        ((star (diagonalMultiplier (f i)) * a * diagonalMultiplier (f i)) (finiteVector w))‖ ≤
      ‖a‖ * (‖diagonalMultiplier (f i) (finiteVector v)‖ *
        ‖diagonalMultiplier (f i) (finiteVector w)‖) := by
    intro i _hi
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    exact (norm_inner_le_norm _ _).trans (by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left (a.le_opNorm (diagonalMultiplier (f i) (finiteVector w)))
          (norm_nonneg (diagonalMultiplier (f i) (finiteVector v))))
  exact ((norm_sum_le _ _).trans (Finset.sum_le_sum hb)).trans
    ((Finset.mul_sum ..).symm.trans_le ((mul_le_mul_of_nonneg_left
      (sum_diagonal_norm_mul_le s f hf (finiteVector v) (finiteVector w)) (norm_nonneg _)).trans_eq
        (mul_assoc _ _ _).symm))

/-- The partition functions regarded as bounded real diagonal operators. -/
def cosineDiagonal {X : Type*} (h : X → ℝ) (L : ℝ) (k : ℤ) : BoundedDiagonal X :=
  boundedRealDiagonal (fun x => cosinePartition L k (h x)) 1
    (fun x => (abs_of_nonneg (cosinePartition_mem_unitInterval L k (h x)).1).trans_le
      (cosinePartition_mem_unitInterval L k (h x)).2)

lemma cosineDiagonal_apply {X : Type*} (h : X → ℝ) (L : ℝ) (k : ℤ) (x : X) :
    cosineDiagonal h L k x = (cosinePartition L k (h x) : ℂ) := rfl

lemma sum_norm_sq_cosineDiagonal_le {X : Type*} (h : X → ℝ) (L : ℝ) (s : Finset ℤ) (x : X) :
    ∑ k ∈ s, ‖cosineDiagonal h L k x‖ ^ 2 ≤ 1 := by
  have hs : Summable (fun k : ℤ => cosinePartition L k (h x) ^ 2) := by
    classical
    apply summable_of_ne_finset_zero (s := {⌊h x / L⌋, ⌊h x / L⌋ + 1})
    intro k hk
    have hk' : k ≠ ⌊h x / L⌋ ∧ k ≠ ⌊h x / L⌋ + 1 := by simpa using hk
    rw [cosinePartition_eq_zero_of_index_ne hk'.1 hk'.2, zero_pow (by decide : 2 ≠ 0)]
  simpa only [cosineDiagonal_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    cosinePartition_sum_sq] using hs.sum_le_tsum s (fun _ _ => sq_nonneg _)

lemma matrixEntry_star_diagonal_sandwich {X : Type*} (f : BoundedDiagonal X)
    (a : Operator X) (x y : X) :
    matrixEntry (star (diagonalMultiplier f) * a * diagonalMultiplier f) x y =
      star (f x) * matrixEntry a x y * f y := by
  rw [← diagonalMultiplier_star]
  simp only [matrixEntry, mul_apply_eq_comp, diagonalMultiplier_apply, diagonalMultiplier_delta,
    map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.star_apply]
  ring

/-- The matrix of the partition smoothing; its defining sum has at most two nonzero terms. -/
def cosineSmoothingMatrix {X : Type*} (h : X → ℝ) (L : ℝ) (a : Operator X) (x y : X) : ℂ :=
  ∑' k : ℤ, (cosinePartition L k (h x) : ℂ) * matrixEntry a x y *
    (cosinePartition L k (h y) : ℂ)

lemma cosineSmoothingMatrix_eq_sum {X : Type*} (h : X → ℝ) (L : ℝ) (a : Operator X)
    (x y : X) (s : Finset ℤ) (hs : ⌊h x / L⌋ ∈ s ∧ ⌊h x / L⌋ + 1 ∈ s) :
    cosineSmoothingMatrix h L a x y =
      ∑ k ∈ s, (cosinePartition L k (h x) : ℂ) * matrixEntry a x y *
        (cosinePartition L k (h y) : ℂ) := by
  apply tsum_eq_sum
  intro k hk
  have hk₀ : k ≠ ⌊h x / L⌋ := fun he => hk (he ▸ hs.1)
  have hk₁ : k ≠ ⌊h x / L⌋ + 1 := fun he => hk (he ▸ hs.2)
  simp only [cosinePartition_eq_zero_of_index_ne hk₀ hk₁, Complex.ofReal_zero, zero_mul]

lemma cosineSmoothingMatrix_form_bound {X : Type*} (h : X → ℝ) (L : ℝ) (a : Operator X)
    (v w : X →₀ ℂ) :
    ‖finiteMatrixForm (cosineSmoothingMatrix h L a) v w‖ ≤
      ‖a‖ * ‖finiteVector v‖ * ‖finiteVector w‖ := by
  classical
  let s : Finset ℤ := v.support.biUnion fun x => {⌊h x / L⌋, ⌊h x / L⌋ + 1}
  let b : Operator X := ∑ k ∈ s, star (diagonalMultiplier (cosineDiagonal h L k)) * a *
    diagonalMultiplier (cosineDiagonal h L k)
  have he : finiteMatrixForm (cosineSmoothingMatrix h L a) v w =
      finiteMatrixForm (matrixEntry b) v w := by
    simp only [finiteMatrixForm_apply]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y _hy => ?_
    have hs : ⌊h x / L⌋ ∈ s ∧ ⌊h x / L⌋ + 1 ∈ s := by
      constructor <;> exact Finset.mem_biUnion.mpr ⟨x, hx, by simp⟩
    rw [cosineSmoothingMatrix_eq_sum h L a x y s hs]
    congr 2
    change _ = (matrixEntryCLM x y) (∑ k ∈ s, _)
    simp only [map_sum, matrixEntryCLM_apply, matrixEntry_star_diagonal_sandwich,
      cosineDiagonal_apply, Complex.star_def, Complex.conj_ofReal]
  have hb : ‖b‖ ≤ ‖a‖ := norm_sum_diagonal_sandwich_le s _
    (sum_norm_sq_cosineDiagonal_le h L s) a
  rw [he]
  exact (norm_finiteMatrixForm_matrixEntry_le b v w).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) (norm_nonneg _))

/-- The bounded operator defined by the source cosine-partition smoothing matrix. -/
def cosineSmoothing {X : Type*} (h : X → ℝ) (L : ℝ) (a : Operator X) : Operator X :=
  operatorOfFiniteForm (finiteMatrixForm (cosineSmoothingMatrix h L a))
    (cosineSmoothingMatrix_form_bound h L a)

lemma cosineSmoothing_norm_le {X : Type*} (h : X → ℝ) (L : ℝ) (a : Operator X) :
    ‖cosineSmoothing h L a‖ ≤ ‖a‖ :=
  norm_operatorOfFiniteForm_le _ (norm_nonneg _) (cosineSmoothingMatrix_form_bound h L a)

lemma matrixEntry_cosineSmoothing {X : Type*} (h : X → ℝ) (L : ℝ) (a : Operator X) (x y : X) :
    matrixEntry (cosineSmoothing h L a) x y = cosineSmoothingMatrix h L a x y :=
  (matrixEntry_operatorOfFiniteForm _ (norm_nonneg _) (cosineSmoothingMatrix_form_bound h L a) x y).trans
    (finiteMatrixForm_single_one _ x y)

lemma cosineSmoothing_propagation {X : Type*} (h : X → ℝ) {L : ℝ} (hL : 0 < L)
    (a : Operator X) (x y : X) (hxy : 2 * L < |h x - h y|) :
    matrixEntry (cosineSmoothing h L a) x y = 0 := by
  rw [matrixEntry_cosineSmoothing]
  unfold cosineSmoothingMatrix
  suffices hz : ∀ k : ℤ, (cosinePartition L k (h x) : ℂ) * matrixEntry a x y *
      (cosinePartition L k (h y) : ℂ) = 0 by simp only [hz, tsum_zero]
  intro k
  by_cases hx : L ≤ |h x - k * L|
  · simp only [(cosinePartition_spec hL).2.2.1 k (h x) hx, Complex.ofReal_zero, zero_mul]
  · have hy : L ≤ |h y - k * L| := by
      have ht : |h x - h y| ≤ |h x - k * L| + |h y - k * L| := by
        simpa only [abs_sub_comm (k * L) (h y)] using abs_sub_le (h x) (k * L) (h y)
      linarith
    simp only [(cosinePartition_spec hL).2.2.1 k (h y) hy, Complex.ofReal_zero, mul_zero]

/-- The actual bounded smoothing operator, with its matrix formula and finite propagation. -/
theorem cosineSmoothing_spec {X : Type*} (h : X → ℝ) {L : ℝ} (hL : 0 < L) (a : Operator X) :
    ‖cosineSmoothing h L a‖ ≤ ‖a‖ ∧
    (∀ x y, matrixEntry (cosineSmoothing h L a) x y =
      ∑' k : ℤ, (cosinePartition L k (h x) : ℂ) * matrixEntry a x y *
        (cosinePartition L k (h y) : ℂ)) ∧
    (∀ x y, 2 * L < |h x - h y| → matrixEntry (cosineSmoothing h L a) x y = 0) :=
  ⟨cosineSmoothing_norm_le h L a, matrixEntry_cosineSmoothing h L a,
    cosineSmoothing_propagation h hL a⟩

end DynamicalCStarAlgebras
