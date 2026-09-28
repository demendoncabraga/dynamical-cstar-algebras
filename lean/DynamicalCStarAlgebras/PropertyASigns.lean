import DynamicalCStarAlgebras.PropertyAKernels
import DynamicalCStarAlgebras.SignMoments

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical
open scoped BigOperators
namespace DynamicalCStarAlgebras

/-- Clipping of a real scalar at a symmetric interval. -/
def realClip (C t : ℝ) : ℝ := max (-C) (min C t)

lemma realClip_abs_le {C : ℝ} (hC : 0 ≤ C) (t : ℝ) : |realClip C t| ≤ C := by
  unfold realClip
  exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma realClip_sub_le (C s t : ℝ) : |realClip C s - realClip C t| ≤ |s - t| := by
  have h := ((LipschitzWith.id.const_min C).const_max (-C)).dist_le_mul s t
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul, realClip, id_eq] using h

lemma realClip_error_sq {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (x - realClip t⁻¹ x) ^ 2 ≤ t ^ 2 * x ^ 4 := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hit : 0 < t⁻¹ := inv_pos.mpr ht
  by_cases hx : |x| ≤ t⁻¹
  · have he : realClip t⁻¹ x = x := by
      rw [realClip, min_eq_right (abs_le.mp hx).2, max_eq_right (abs_le.mp hx).1]
    rw [he, sub_self, zero_pow (by decide : 2 ≠ 0)]
    positivity
  · have htx : 1 ≤ t * |x| := by
      have h := mul_le_mul_of_nonneg_left (le_of_lt (not_le.mp hx)) ht.le
      simpa only [mul_inv_cancel₀ ht0] using h
    have hsq : 1 ≤ t ^ 2 * x ^ 2 := by nlinarith [sq_abs x]
    have hlarge : x ^ 2 ≤ t ^ 2 * x ^ 4 := by
      have h := mul_le_mul_of_nonneg_right hsq (sq_nonneg x)
      nlinarith
    apply le_trans _ hlarge
    by_cases hp : t⁻¹ ≤ x
    · rw [realClip, min_eq_left hp, max_eq_right (by linarith : -t⁻¹ ≤ t⁻¹)]
      nlinarith
    · have hn : x ≤ -t⁻¹ := by
        have habs := not_le.mp hx
        rcases le_total 0 x with hx0 | hx0
        · rw [abs_of_nonneg hx0] at habs
          exact False.elim (hp habs.le)
        · rw [abs_of_nonpos hx0] at habs
          linarith
      rw [realClip, min_eq_right (by linarith), max_eq_left hn]
      nlinarith

namespace FiniteSquarePartition
variable {X I : Type*} (P : FiniteSquarePartition X I)

/-- A finite Rademacher linear combination of partition functions. -/
def signed (s : Finset I) (σ : s → Bool) (x : X) : ℝ :=
  ∑ i : s, boolSign (σ i) * P.row x i

lemma expect_signed_sq (s : Finset I) (x : X) :
    (𝔼 σ : s → Bool, P.signed s σ x ^ 2) = ∑ i ∈ s, P.row x i ^ 2 := by
  have h := (expect_signed_finset_second_fourth_moments Finset.univ
    (fun i : s => P.row x i)).1
  rw [← Finset.sum_coe_sort s (fun i => P.row x i ^ 2)]
  unfold signed
  convert h using 1
  congr 3
  exact Subsingleton.elim _ _

lemma expect_signed_sq_le (s : Finset I) (x : X) :
    (𝔼 σ : s → Bool, P.signed s σ x ^ 2) ≤ 1 :=
  (P.expect_signed_sq s x).le.trans (P.sum_sq_le x s)

lemma expect_signed_fourth_le (s : Finset I) (x : X) :
    (𝔼 σ : s → Bool, P.signed s σ x ^ 4) ≤ 3 := by
  have h := (expect_signed_finset_second_fourth_moments Finset.univ
    (fun i : s => P.row x i)).2
  have hc := Finset.sum_coe_sort s (fun i => P.row x i ^ 2)
  have hc' : (∑ i : s, P.row x i ^ 2) = ∑ i ∈ s, P.row x i ^ 2 := by exact hc
  rw [hc'] at h
  have hs := P.sum_sq_le x s
  have hn : 0 ≤ ∑ i ∈ s, P.row x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : 3 * (∑ i ∈ s, P.row x i ^ 2) ^ 2 ≤ 3 := by nlinarith
  unfold signed
  convert h.trans hb using 1 <;> first | rfl | (congr 3; exact Subsingleton.elim _ _)

lemma expect_signed_sub_sq (s : Finset I) (x y : X) :
    (𝔼 σ : s → Bool, (P.signed s σ x - P.signed s σ y) ^ 2) =
      ∑ i ∈ s, (P.row x i - P.row y i) ^ 2 := by
  have h := (expect_signed_finset_second_fourth_moments Finset.univ
    (fun i : s => P.row x i - P.row y i)).1
  rw [← Finset.sum_coe_sort s (fun i => (P.row x i - P.row y i) ^ 2)]
  simp only [mul_sub, Finset.sum_sub_distrib] at h
  unfold signed
  convert h using 1
  congr 3
  exact Subsingleton.elim _ _

lemma signed_abs_le_card (s : Finset I) (σ : s → Bool) (x : X) :
    |P.signed s σ x| ≤ s.card := by
  calc
    _ ≤ ∑ i : s, |boolSign (σ i) * P.row x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : s, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hs : |boolSign (σ i)| = 1 := by cases σ i <;> norm_num [boolSign]
      rw [abs_mul, hs, one_mul]
      exact P.abs_row_le_one x i
    _ = _ := by simp

lemma expect_clip_error_sq {t : ℝ} (ht : 0 < t) (s : Finset I) (x : X) :
    (𝔼 σ : s → Bool, (P.signed s σ x - realClip t⁻¹ (P.signed s σ x)) ^ 2) ≤
      3 * t ^ 2 := by
  calc
    _ ≤ 𝔼 σ : s → Bool, t ^ 2 * P.signed s σ x ^ 4 :=
      Finset.expect_le_expect fun _ _ => realClip_error_sq ht _
    _ = t ^ 2 * (𝔼 σ : s → Bool, P.signed s σ x ^ 4) := (Finset.mul_expect ..).symm
    _ ≤ _ := by nlinarith [P.expect_signed_fourth_le s x, sq_nonneg t]

end FiniteSquarePartition
namespace FiniteProbabilityKernel
variable {X : Type*} (μ ν : FiniteProbabilityKernel X)

lemma sub_average_eq (f : X → ℝ) (x : X) :
    f x - μ.average f x = μ.average (fun z => f x - f z) x := by
  simp only [average, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, μ.sum_one, one_mul]

/-- The clipped signed partition after convolution with the first probability kernel. -/
def smoothedSign (s : Finset X) (t : ℝ) (σ : s → Bool) (x : X) : ℝ :=
  μ.average (fun z => realClip t⁻¹ (ν.squarePartition.signed s σ z)) x

lemma smoothedSign_abs_le {t : ℝ} (ht : 0 < t) (s : Finset X) (σ : s → Bool) (x : X) :
    |μ.smoothedSign ν s t σ x| ≤ t⁻¹ :=
  μ.average_abs_le _ (fun _ => realClip_abs_le (inv_nonneg.mpr ht.le) _) x

lemma smoothedSign_variation_le {t : ℝ} (ht : 0 < t) (s : Finset X) (σ : s → Bool)
    (x y : X) (hxy : μ.variation x y ≤ t ^ 2) :
    |μ.smoothedSign ν s t σ x - μ.smoothedSign ν s t σ y| ≤ t := by
  have h := μ.average_variation_le (fun z => realClip t⁻¹ (ν.squarePartition.signed s σ z))
    (fun _ => realClip_abs_le (inv_nonneg.mpr ht.le) _) x y
  exact h.trans ((mul_le_mul_of_nonneg_right hxy (inv_nonneg.mpr ht.le)).trans_eq
    (by field_simp))

lemma expect_clip_sub_smoothed_sq {t : ℝ} (_ht : 0 < t) (s : Finset X) (x : X)
    (hvar : ∀ z, μ.row x z ≠ 0 → ν.variation x z ≤ t ^ 2) :
    (𝔼 σ : s → Bool,
      (realClip t⁻¹ (ν.squarePartition.signed s σ x) - μ.smoothedSign ν s t σ x) ^ 2) ≤ t ^ 2 := by
  let g (σ : s → Bool) (z : X) := realClip t⁻¹ (ν.squarePartition.signed s σ z)
  have hpoint (z : X) (hz : z ∈ (μ.row x).support) :
      (𝔼 σ : s → Bool, (g σ x - g σ z) ^ 2) ≤ t ^ 2 := by
    calc
      _ ≤ 𝔼 σ : s → Bool,
          (ν.squarePartition.signed s σ x - ν.squarePartition.signed s σ z) ^ 2 := by
        apply Finset.expect_le_expect
        intro σ _
        have h := realClip_sub_le t⁻¹ (ν.squarePartition.signed s σ x)
          (ν.squarePartition.signed s σ z)
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
      _ ≤ ν.variation x z := by
        rw [ν.squarePartition.expect_signed_sub_sq]
        exact ν.squarePartition_variation_le x z s
      _ ≤ t ^ 2 := hvar z (Finsupp.mem_support_iff.mp hz)
  have hJ (σ : s → Bool) : (g σ x - μ.average (g σ) x) ^ 2 ≤
      μ.average (fun z => (g σ x - g σ z) ^ 2) x := by
    rw [μ.sub_average_eq]
    exact μ.average_sq_le _ x
  change (𝔼 σ : s → Bool, (g σ x - μ.average (g σ) x) ^ 2) ≤ _
  calc
    _ ≤ 𝔼 σ : s → Bool, μ.average (fun z => (g σ x - g σ z) ^ 2) x :=
      Finset.expect_le_expect (fun σ _ => hJ σ)
    _ = ∑ z ∈ (μ.row x).support, μ.row x z *
        (𝔼 σ : s → Bool, (g σ x - g σ z) ^ 2) := by
      unfold average
      rw [Finset.expect_sum_comm]
      exact Finset.sum_congr rfl fun z _ => (Finset.mul_expect ..).symm
    _ ≤ ∑ z ∈ (μ.row x).support, μ.row x z * t ^ 2 :=
      Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (hpoint z hz) (μ.nonneg x z)
    _ = t ^ 2 := by rw [← Finset.sum_mul, μ.sum_one, one_mul]

/-- The clipped convolution remains uniformly close in mean square to the signed partition. -/
lemma expect_signed_sub_smoothed_sq {t : ℝ} (ht : 0 < t) (s : Finset X) (x : X)
    (hvar : ∀ z, μ.row x z ≠ 0 → ν.variation x z ≤ t ^ 2) :
    (𝔼 σ : s → Bool, (ν.squarePartition.signed s σ x - μ.smoothedSign ν s t σ x) ^ 2) ≤
      (3 * t) ^ 2 := by
  have hpoint (σ : s → Bool) :
      (ν.squarePartition.signed s σ x - μ.smoothedSign ν s t σ x) ^ 2 ≤
      2 * (ν.squarePartition.signed s σ x - realClip t⁻¹ (ν.squarePartition.signed s σ x)) ^ 2 +
      2 * (realClip t⁻¹ (ν.squarePartition.signed s σ x) - μ.smoothedSign ν s t σ x) ^ 2 := by
    nlinarith [sq_nonneg (ν.squarePartition.signed s σ x -
      2 * realClip t⁻¹ (ν.squarePartition.signed s σ x) + μ.smoothedSign ν s t σ x)]
  have hb := Finset.expect_le_expect (fun σ (_ : σ ∈ (Finset.univ : Finset (s → Bool))) => hpoint σ)
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at hb
  nlinarith [ν.squarePartition.expect_clip_error_sq ht s x,
    μ.expect_clip_sub_smoothed_sq ν ht s x hvar, sq_nonneg t]

end FiniteProbabilityKernel
end DynamicalCStarAlgebras
