import DynamicalCStarAlgebras.EntireCoefficientDecay

noncomputable section

namespace DynamicalCStarAlgebras

set_option backward.isDefEq.respectTransparency false in
/-- Coordinates of the finite-vector embedding. -/
theorem finiteVector_apply {X : Type*} (v : X →₀ ℂ) (x : X) : finiteVector v x = v x := by
  simp [finiteVector, Finsupp.linearCombination_apply, Finsupp.sum, delta, lp.coeFn_smul, Finset.sum_apply, lp.single_apply, Pi.single_apply, eq_comm]

/-- Finite coordinate sums are bounded by the squared Hilbert norm. -/
theorem sum_sq_le_finiteVector_norm_sq {X : Type*} (v : X →₀ ℂ) (s : Finset X) :
    ∑ x ∈ s, ‖v x‖ ^ 2 ≤ ‖finiteVector v‖ ^ 2 := by
  simpa [finiteVector_apply, Real.rpow_two] using
    lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ENNReal).toReal) (finiteVector v) s

/-- Weighted Cauchy--Schwarz without square roots. -/
theorem weighted_sum_sq_le {ι : Type*} (s : Finset ι) (d u v : ι → ℝ)
    (hd : ∀ i ∈ s, 0 ≤ d i) :
    (∑ i ∈ s, d i * u i * v i) ^ 2 ≤
      (∑ i ∈ s, d i * u i ^ 2) * ∑ i ∈ s, d i * v i ^ 2 :=
  Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun i hi => mul_nonneg (hd i hi) (sq_nonneg _))
    (fun i hi => mul_nonneg (hd i hi) (sq_nonneg _))
    (fun i _ => le_of_eq (by ring))

/-- Row sums bound the weighted square sum. -/
theorem weighted_row_sum_le {X Y : Type*} (s : Finset X) (t : Finset Y)
    (d : X → Y → ℝ) (u : X → ℝ) {C : ℝ}
    (hrow : ∀ x ∈ s, ∑ y ∈ t, d x y ≤ C) :
    ∑ p ∈ s ×ˢ t, d p.1 p.2 * u p.1 ^ 2 ≤ C * ∑ x ∈ s, u x ^ 2 := by
  simp only [Finset.sum_product, ← Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_right (hrow x hx) (sq_nonneg _)

/-- The scalar finite Schur estimate from row and column bounds. -/
theorem finite_schur_bound {X Y : Type*} (s : Finset X) (t : Finset Y)
    (d : X → Y → ℝ) (u : X → ℝ) (v : Y → ℝ) {C U V : ℝ}
    (hC : 0 ≤ C) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hd : ∀ x ∈ s, ∀ y ∈ t, 0 ≤ d x y)
    (hrow : ∀ x ∈ s, ∑ y ∈ t, d x y ≤ C)
    (hcol : ∀ y ∈ t, ∑ x ∈ s, d x y ≤ C)
    (hu : ∑ x ∈ s, u x ^ 2 ≤ U ^ 2) (hv : ∑ y ∈ t, v y ^ 2 ≤ V ^ 2) :
    ∑ p ∈ s ×ˢ t, d p.1 p.2 * u p.1 * v p.2 ≤ C * U * V := by
  have hleft : ∑ p ∈ s ×ˢ t, d p.1 p.2 * u p.1 ^ 2 ≤ C * U ^ 2 :=
    (weighted_row_sum_le s t d u hrow).trans (mul_le_mul_of_nonneg_left hu hC)
  have hright : ∑ p ∈ s ×ˢ t, d p.1 p.2 * v p.2 ^ 2 ≤ C * V ^ 2 := by
    rw [Finset.sum_product, Finset.sum_comm]
    simpa only [Finset.sum_product] using
      (weighted_row_sum_le t s (fun y x => d x y) v hcol).trans
        (mul_le_mul_of_nonneg_left hv hC)
  have hs := weighted_sum_sq_le (s ×ˢ t) (fun p => d p.1 p.2)
    (fun p => u p.1) (fun p => v p.2)
    (fun p hp => hd p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2)
  exact le_of_sq_le_sq ((hs.trans (mul_le_mul hleft hright
    (Finset.sum_nonneg fun p hp => mul_nonneg
      (hd p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2) (sq_nonneg _))
    (mul_nonneg hC (sq_nonneg _)))).trans_eq (by ring))
    (mul_nonneg (mul_nonneg hC hU) hV)

/-- Entrywise absolute values bound a finite matrix pairing. -/
theorem norm_finiteMatrixForm_le_sum {X : Type*} (m : X → X → ℂ) (v w : X →₀ ℂ) :
    ‖finiteMatrixForm m v w‖ ≤
      ∑ p ∈ v.support ×ˢ w.support, ‖m p.1 p.2‖ * ‖v p.1‖ * ‖w p.2‖ := by
  rw [finiteMatrixForm_apply, ← Finset.sum_product v.support w.support
    (fun p => star (v p.1) * (w p.2 * m p.1 p.2))]
  simpa only [norm_mul, norm_star, mul_assoc, mul_comm, mul_left_comm] using
    norm_sum_le (v.support ×ˢ w.support) (fun p => star (v p.1) * (w p.2 * m p.1 p.2))

/-- A common bound for all finite absolute row and column sums. -/
def HasSchurBound {X : Type*} (m : X → X → ℂ) (C : ℝ) : Prop :=
  (∀ x (s : Finset X), ∑ y ∈ s, ‖m x y‖ ≤ C) ∧
    (∀ y (s : Finset X), ∑ x ∈ s, ‖m x y‖ ≤ C)

/-- Finite Schur bounds control the form on the dense finite-vector subspace. -/
theorem HasSchurBound.finiteForm_bound {X : Type*} {m : X → X → ℂ} {C : ℝ}
    (hm : HasSchurBound m C) (hC : 0 ≤ C) (v w : X →₀ ℂ) :
    ‖finiteMatrixForm m v w‖ ≤ C * ‖finiteVector v‖ * ‖finiteVector w‖ :=
  (norm_finiteMatrixForm_le_sum m v w).trans
    (finite_schur_bound v.support w.support (fun x y => ‖m x y‖)
      (fun x => ‖v x‖) (fun y => ‖w y‖) hC (norm_nonneg _) (norm_nonneg _)
      (fun _ _ _ _ => norm_nonneg _) (fun x _ => hm.1 x w.support)
      (fun y _ => hm.2 y v.support) (sum_sq_le_finiteVector_norm_sq _ _)
      (sum_sq_le_finiteVector_norm_sq _ _))

/-- A Schur-bounded matrix defines an operator on the full Hilbert space. -/
def operatorOfSchurMatrix {X : Type*} (m : X → X → ℂ) {C : ℝ}
    (hm : HasSchurBound m C) (hC : 0 ≤ C) : Operator X :=
  operatorOfFiniteForm (finiteMatrixForm m) (hm.finiteForm_bound hC)

theorem norm_operatorOfSchurMatrix_le {X : Type*} (m : X → X → ℂ) {C : ℝ}
    (hm : HasSchurBound m C) (hC : 0 ≤ C) : ‖operatorOfSchurMatrix m hm hC‖ ≤ C :=
  norm_operatorOfFiniteForm_le _ hC (hm.finiteForm_bound hC)

theorem matrixEntry_operatorOfSchurMatrix {X : Type*} (m : X → X → ℂ) {C : ℝ}
    (hm : HasSchurBound m C) (hC : 0 ≤ C) (x y : X) :
    matrixEntry (operatorOfSchurMatrix m hm hC) x y = m x y :=
  (matrixEntry_operatorOfFiniteForm _ hC (hm.finiteForm_bound hC) x y).trans
    (finiteMatrixForm_single_one m x y)

end DynamicalCStarAlgebras
