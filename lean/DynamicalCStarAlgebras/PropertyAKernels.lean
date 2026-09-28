import DynamicalCStarAlgebras.PropertyAPartition

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- A finitely supported probability measure at each point. In a ULF metric space,
any probability measure supported in one fixed-radius ball has this form. -/
structure FiniteProbabilityKernel (X : Type*) where
  row : X → X →₀ ℝ
  nonneg : ∀ x z, 0 ≤ row x z
  sum_one : ∀ x, ∑ z ∈ (row x).support, row x z = 1

namespace FiniteProbabilityKernel
variable {X : Type*} (μ : FiniteProbabilityKernel X)

/-- The exact l1 distance between two probability rows. -/
def variation (x y : X) : ℝ :=
  ∑ z ∈ (μ.row x - μ.row y).support, |μ.row x z - μ.row y z|

lemma variation_eq_sum (x y : X) (s : Finset X)
    (hx : (μ.row x).support ⊆ s) (hy : (μ.row y).support ⊆ s) :
    μ.variation x y = ∑ z ∈ s, |μ.row x z - μ.row y z| := by
  exact (μ.row x - μ.row y).sum_of_support_subset
    (Finsupp.support_sub.trans (Finset.union_subset hx hy)) (fun _ t => |t|) (by simp)

lemma sqrt_sub_sq_le_abs_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    have hp := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hab) (Real.sqrt_nonneg a)
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    have hp := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hba) (Real.sqrt_nonneg b)
    nlinarith

/-- Square roots of probability coordinates give the partition used in Ozawa Theorem5. -/
def squarePartition : FiniteSquarePartition X X where
  row x := (μ.row x).mapRange Real.sqrt Real.sqrt_zero
  sum_sq x := by
    change ((μ.row x).mapRange Real.sqrt Real.sqrt_zero).sum (fun _ t => t ^ 2) = 1
    rw [Finsupp.sum_mapRange_index (by simp)]
    simpa only [Finsupp.sum, Real.sq_sqrt (μ.nonneg x _)] using μ.sum_one x


lemma squarePartition_support (x : X) :
    (μ.squarePartition.row x).support ⊆ (μ.row x).support := Finsupp.support_mapRange (hf := Real.sqrt_zero)

lemma squarePartition_variation_le (x y : X) (s : Finset X) :
    ∑ z ∈ s, (μ.squarePartition.row x z - μ.squarePartition.row y z) ^ 2 ≤
      μ.variation x y := by
  let t := s ∪ ((μ.row x).support ∪ (μ.row y).support)
  have hx : (μ.row x).support ⊆ t := fun i hi => Finset.mem_union_right _ (Finset.mem_union_left _ hi)
  have hy : (μ.row y).support ⊆ t := fun i hi => Finset.mem_union_right _ (Finset.mem_union_right _ hi)
  rw [μ.variation_eq_sum x y t hx hy]
  exact (Finset.sum_le_sum (fun z _ => sqrt_sub_sq_le_abs_sub (μ.nonneg x z) (μ.nonneg y z))).trans
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun _ _ _ => abs_nonneg _))

/-- Integration of a real function against a probability row. -/
def average (f : X → ℝ) (x : X) : ℝ := ∑ z ∈ (μ.row x).support, μ.row x z * f z

lemma average_abs_le (f : X → ℝ) {C : ℝ} (hf : ∀ z, |f z| ≤ C) (x : X) :
    |μ.average f x| ≤ C := by
  calc
    _ ≤ ∑ z ∈ (μ.row x).support, |μ.row x z * f z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z ∈ (μ.row x).support, μ.row x z * C := by
      apply Finset.sum_le_sum
      intro z _
      rw [abs_mul, abs_of_nonneg (μ.nonneg x z)]
      exact mul_le_mul_of_nonneg_left (hf z) (μ.nonneg x z)
    _ = C := by rw [← Finset.sum_mul, μ.sum_one, one_mul]

lemma average_variation_le (f : X → ℝ) {C : ℝ} (hf : ∀ z, |f z| ≤ C) (x y : X) :
    |μ.average f x - μ.average f y| ≤ μ.variation x y * C := by
  let s := (μ.row x).support ∪ (μ.row y).support
  have hx : (μ.row x).support ⊆ s := Finset.subset_union_left
  have hy : (μ.row y).support ⊆ s := Finset.subset_union_right
  have he (z : X) (hz : (μ.row z).support ⊆ s) :
      μ.average f z = ∑ i ∈ s, μ.row z i * f i :=
    (μ.row z).sum_of_support_subset hz (fun i t => t * f i) (by simp)
  rw [he x hx, he y hy, ← Finset.sum_sub_distrib, μ.variation_eq_sum x y s hx hy,
    Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro z _
  rw [← sub_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hf z) (abs_nonneg _)

lemma average_sq_le (f : X → ℝ) (x : X) :
    μ.average f x ^ 2 ≤ μ.average (fun z => f z ^ 2) x := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (μ.row x).support
    (fun z _ => μ.nonneg x z)
    (fun z _ => mul_nonneg (μ.nonneg x z) (sq_nonneg (f z)))
    (fun z _ => show (μ.row x z * f z) ^ 2 ≤ μ.row x z * (μ.row x z * f z ^ 2) by nlinarith)
  simpa only [μ.sum_one, one_mul, average] using h

lemma squarePartition_propagation [PseudoMetricSpace X] {S : ℝ}
    (hs : ∀ x z, μ.row x z ≠ 0 → dist x z ≤ S)
    (a : Operator X) (x y : X) (hxy : 2 * S < dist x y) :
    matrixEntry (μ.squarePartition.smoothing a) x y = 0 := by
  apply μ.squarePartition.smoothing_propagation (S := 2 * S) ?_ a x y hxy
  intro x y z hx hy
  have hx' : μ.row x z ≠ 0 := Finsupp.mem_support_iff.mp
    (μ.squarePartition_support x (Finsupp.mem_support_iff.mpr hx))
  have hy' : μ.row y z ≠ 0 := Finsupp.mem_support_iff.mp
    (μ.squarePartition_support y (Finsupp.mem_support_iff.mpr hy))
  exact (dist_triangle x z y).trans (by rw [dist_comm z y]; linarith [hs x z hx', hs y z hy'])

end FiniteProbabilityKernel

/-- Yu's property A in finite probability-coordinate form. The support restriction
is finite automatically for the ULF spaces considered in the source assertion. -/
def HasPropertyA (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ δ > 0, ∀ R > 0, ∃ S > 0, ∃ μ : FiniteProbabilityKernel X,
    (∀ x z, μ.row x z ≠ 0 → dist x z ≤ S) ∧
    (∀ x y, dist x y ≤ R → μ.variation x y < δ)

end DynamicalCStarAlgebras
