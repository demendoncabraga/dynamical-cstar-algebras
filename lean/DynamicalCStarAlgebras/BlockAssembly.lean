import DynamicalCStarAlgebras.GraphHeightBounds

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

/-- Matrix coefficients of a finite sum of diagonal fiber compressions. -/
theorem matrixEntry_sum_fiber_compressions {X I : Type*} (π : X → I)
    (a : I → Operator X) (s : Finset I) (x y : X) (hx : π x ∈ s) :
    matrixEntry (∑ i ∈ s, coordinateProjection {z | π z = i} * a i *
      coordinateProjection {z | π z = i}) x y =
      if π x = π y then matrixEntry (a (π x)) x y else 0 := by
  change (matrixEntryCLM x y) (∑ i ∈ s, _) = _
  simp only [map_sum, matrixEntryCLM_apply, matrixEntry_compression, Set.mem_ofPred_eq,
    ite_and, Finset.sum_ite_eq, hx, if_true]
  simp only [eq_comm]

/-- Uniform bounds on the compressed blocks give a bound on the assembled finite matrix form. -/
theorem fiber_matrix_form_bound {X I : Type*} (π : X → I) (a : I → Operator X)
    {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ i, ‖coordinateProjection {x | π x = i} * a i * coordinateProjection {x | π x = i}‖ ≤ M)
    (v w : X →₀ ℂ) :
    ‖finiteMatrixForm (fun x y => if π x = π y then matrixEntry (a (π x)) x y else 0) v w‖ ≤
      M * ‖finiteVector v‖ * ‖finiteVector w‖ := by
  let s := v.support.image π
  let b : Operator X := ∑ i ∈ s, coordinateProjection {x | π x = i} * a i *
    coordinateProjection {x | π x = i}
  have he : finiteMatrixForm (fun x y => if π x = π y then matrixEntry (a (π x)) x y else 0) v w =
      finiteMatrixForm (matrixEntry b) v w := by
    simp only [finiteMatrixForm_apply]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y _ => ?_
    rw [show matrixEntry b x y = _ from matrixEntry_sum_fiber_compressions π a s x y
      (Finset.mem_image.mpr ⟨x, hx, rfl⟩)]
  have hdisj : (s : Set I).PairwiseDisjoint (fun i => {x | π x = i}) :=
    fun i _ j _ hij => Set.disjoint_left.mpr fun x hxi hxj => hij (hxi.symm.trans hxj)
  have hb : ‖b‖ ≤ M := norm_sum_disjoint_compressions_le s _ _ a hdisj hdisj hM
    (fun i _ => ha i)
  rw [he]
  exact (norm_finiteMatrixForm_matrixEntry_le b v w).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) (norm_nonneg _))

/-- Assemble arbitrarily many uniformly bounded diagonal blocks. -/
theorem exists_fiber_operator {X I : Type*} (π : X → I) (a : I → Operator X)
    {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ i, ‖coordinateProjection {x | π x = i} * a i * coordinateProjection {x | π x = i}‖ ≤ M) :
    ∃ b : Operator X, ‖b‖ ≤ M ∧ ∀ x y,
      matrixEntry b x y = if π x = π y then matrixEntry (a (π x)) x y else 0 := by
  let K := fun x y => if π x = π y then matrixEntry (a (π x)) x y else 0
  have hb := fiber_matrix_form_bound π a hM ha
  exact ⟨operatorOfFiniteForm (finiteMatrixForm K) hb,
    norm_operatorOfFiniteForm_le _ hM hb,
    fun x y => (matrixEntry_operatorOfFiniteForm _ hM hb x y).trans
      (finiteMatrixForm_single_one K x y)⟩

/-- Uniform factorial bounds on diagonal blocks assemble into global analytic moments. -/
theorem stripExtension_of_fiber_moments {X I : Type*} (π : X → I) (h : X → ℝ)
    (a : Operator X) (b : I → ℕ → Operator X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 < B)
    (ha : ∀ x y, π x ≠ π y → matrixEntry a x y = 0)
    (hm : ∀ i k x y, π x = i → π y = i → matrixEntry (b i k) x y =
      ((h x - h y : ℝ) : ℂ) ^ k * matrixEntry a x y)
    (hb : ∀ i k, ‖coordinateProjection {x | π x = i} * b i k *
      coordinateProjection {x | π x = i}‖ ≤ A * B ^ k * k.factorial) :
    ∀ δ : ℝ, 0 < δ → δ < B⁻¹ → ∃ F, IsStripExtension h a δ F := by
  have hex (k : ℕ) := exists_fiber_operator π (fun i => b i k)
    (show 0 ≤ A * B ^ k * k.factorial by positivity) (fun i => hb i k)
  choose c hc hentry using hex
  have hmoment : IsDiagonalMomentSequence h a c := by
    intro k x y
    rw [hentry]
    by_cases he : π x = π y
    · rw [if_pos he]
      exact hm (π x) k x y rfl he.symm
    · rw [if_neg he, ha x y he, mul_zero]
  exact (stripExtension_of_factorial_moments hmoment hB hc).2

end DynamicalCStarAlgebras
