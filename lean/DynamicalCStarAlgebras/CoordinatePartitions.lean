import DynamicalCStarAlgebras.ExponentialGrowth

noncomputable section

namespace DynamicalCStarAlgebras
open Classical

/-- Coordinate projections act by the indicator of the projected set. -/
theorem coordinateProjection_apply_ite {X : Type*} (A : Set X)
    (v : HilbertSpace X) (x : X) :
    coordinateProjection A v x = if x ∈ A then v x else 0 := by
  classical
  split_ifs with hx
  · exact coordinateProjection_apply_of_mem A v hx
  · exact coordinateProjection_apply_of_not_mem A v hx

/-- Summing coordinate projections over disjoint sets gives the projection onto their union. -/
theorem sum_coordinateProjection {X ι : Type*} (s : Finset ι) (A : ι → Set X)
    (hA : (s : Set ι).PairwiseDisjoint A) :
    ∑ i ∈ s, coordinateProjection (A i) = coordinateProjection (⋃ i ∈ s, A i) := by
  refine ContinuousLinearMap.ext fun v => lp.ext (funext fun x => ?_)
  simpa only [sum_apply, lp.coeFn_sum, Finset.sum_apply, coordinateProjection_apply_ite,
    Set.indicator_apply] using (Finset.indicator_biUnion_apply s A (f := v) hA x).symm

theorem re_inner_coordinateProjection {X : Type*} (A : Set X) (v : HilbertSpace X) :
    RCLike.re (inner ℂ (coordinateProjection A v) v) = ‖coordinateProjection A v‖ ^ 2 := by
  simpa only [coordinateProjection, Submodule.starProjection_apply, Submodule.coe_norm] using
    (coordinateSubspace A).toSubmodule.re_inner_starProjection_eq_normSq v

/-- Disjoint coordinate projections split at most the squared norm of a vector. -/
theorem sum_norm_sq_coordinateProjection_le {X ι : Type*} (s : Finset ι) (A : ι → Set X)
    (hA : (s : Set ι).PairwiseDisjoint A) (v : HilbertSpace X) :
    ∑ i ∈ s, ‖coordinateProjection (A i) v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  have he : ∑ i ∈ s, ‖coordinateProjection (A i) v‖ ^ 2 =
      RCLike.re (inner ℂ ((∑ i ∈ s, coordinateProjection (A i)) v) v) := by
    change _ = (RCLike.reCLM : ℂ →L[ℝ] ℝ)
      (inner ℂ ((∑ i ∈ s, coordinateProjection (A i)) v) v)
    simp only [sum_apply, sum_inner, map_sum, RCLike.reCLM_apply, re_inner_coordinateProjection]
  rw [he, sum_coordinateProjection s A hA, re_inner_coordinateProjection]
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((coordinateSubspace _).toSubmodule.norm_starProjection_apply_le v) 2

/-- A coordinate projection can be moved across the Hilbert inner product. -/
theorem inner_coordinateProjection {X : Type*} (A : Set X) (v w : HilbertSpace X) :
    inner ℂ (coordinateProjection A v) w = inner ℂ v (coordinateProjection A w) :=
  (coordinateSubspace A).toSubmodule.inner_starProjection_left_eq_right v w

/-- A coordinate projection is idempotent. -/
theorem coordinateProjection_idempotent {X : Type*} (A : Set X) (v : HilbertSpace X) :
    coordinateProjection A (coordinateProjection A v) = coordinateProjection A v :=
  congrArg (fun a : Operator X => a v)
    (coordinateSubspace A).toSubmodule.isIdempotentElem_starProjection

/-- Cauchy--Schwarz for two finite disjoint coordinate decompositions. -/
theorem sum_projection_norm_mul_le {X ι : Type*} (s : Finset ι) (A B : ι → Set X)
    (hA : (s : Set ι).PairwiseDisjoint A) (hB : (s : Set ι).PairwiseDisjoint B)
    (v w : HilbertSpace X) :
    ∑ i ∈ s, ‖coordinateProjection (A i) v‖ * ‖coordinateProjection (B i) w‖ ≤ ‖v‖ * ‖w‖ := by
  have hs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => ‖coordinateProjection (A i) v‖) (fun i => ‖coordinateProjection (B i) w‖)
  exact le_of_sq_le_sq ((hs.trans (mul_le_mul
    (sum_norm_sq_coordinateProjection_le s A hA v)
    (sum_norm_sq_coordinateProjection_le s B hB w)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _))).trans_eq (mul_pow _ _ 2).symm)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Pairing a compressed operator only uses the projected vectors. -/
theorem inner_compression_projected {X : Type*} (A B : Set X) (a : Operator X)
    (v w : HilbertSpace X) :
    inner ℂ v ((coordinateProjection A * a * coordinateProjection B) w) =
      inner ℂ (coordinateProjection A v)
        ((coordinateProjection A * a * coordinateProjection B) (coordinateProjection B w)) := by
  simp only [mul_apply_eq_comp, coordinateProjection_idempotent, inner_coordinateProjection]

/-- Disjoint row and column blocks have norm bounded by a common block bound. -/
theorem norm_sum_disjoint_compressions_le {X ι : Type*} (s : Finset ι)
    (A B : ι → Set X) (a : ι → Operator X)
    (hA : (s : Set ι).PairwiseDisjoint A) (hB : (s : Set ι).PairwiseDisjoint B)
    {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ i ∈ s, ‖coordinateProjection (A i) * a i * coordinateProjection (B i)‖ ≤ C) :
    ‖∑ i ∈ s, coordinateProjection (A i) * a i * coordinateProjection (B i)‖ ≤ C := by
  refine norm_le_of_finiteMatrixForm_bound _ hC fun v w => ?_
  rw [finiteMatrixForm_matrixEntry, sum_apply, inner_sum]
  have hb : ∀ i ∈ s,
      ‖inner ℂ (finiteVector v) ((coordinateProjection (A i) * a i * coordinateProjection (B i))
        (finiteVector w))‖ ≤
      C * (‖coordinateProjection (A i) (finiteVector v)‖ *
        ‖coordinateProjection (B i) (finiteVector w)‖) := by
    intro i hi
    rw [inner_compression_projected]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      (norm_inner_le_norm (coordinateProjection (A i) (finiteVector v))
        ((coordinateProjection (A i) * a i * coordinateProjection (B i))
          (coordinateProjection (B i) (finiteVector w)))).trans
        (mul_le_mul_of_nonneg_left
          (((coordinateProjection (A i) * a i * coordinateProjection (B i)).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (ha i hi) (norm_nonneg _))) (norm_nonneg _))
  exact ((norm_sum_le _ _).trans (Finset.sum_le_sum hb)).trans
    ((Finset.mul_sum ..).symm.trans_le ((mul_le_mul_of_nonneg_left
      (sum_projection_norm_mul_le s A B hA hB (finiteVector v) (finiteVector w)) hC).trans_eq
        (mul_assoc _ _ _).symm))

end DynamicalCStarAlgebras
