import DynamicalCStarAlgebras.ExpanderPolynomialBound
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul

noncomputable section
open scoped ComplexConjugate
open Finset
namespace DynamicalCStarAlgebras
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

lemma symmetric_pow_repr (a : H →ₗ[ℂ] H) (ha : a.IsSymmetric)
    (x : H) (m : ℕ) (i : Fin (Module.finrank ℂ H)) :
    (ha.eigenvectorBasis rfl).repr ((a ^ m) x) i =
      (ha.eigenvalues rfl i : ℂ) ^ m * (ha.eigenvectorBasis rfl).repr x i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ha.eigenvectorBasis_apply_self_apply, ih, pow_succ']
    exact (mul_assoc _ _ _).symm
lemma symmetric_pow_norm_sq (a : H →ₗ[ℂ] H) (ha : a.IsSymmetric)
    (x : H) (m : ℕ) :
    ‖(a ^ m) x‖ ^ 2 = ∑ i : Fin (Module.finrank ℂ H),
      ‖(ha.eigenvectorBasis rfl).repr x i‖ ^ 2 * (ha.eigenvalues rfl i ^ 2) ^ m := by
  rw [← (ha.eigenvectorBasis rfl).repr.norm_map ((a ^ m) x), EuclideanSpace.norm_sq_eq]
  simp only [symmetric_pow_repr, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, ← pow_mul, Nat.mul_comm m 2, pow_mul, sq_abs]
  exact mul_comm _ _

/-- The finite spectral Jensen inequality used in the trace estimate. -/
lemma symmetric_norm_pow_le (a : H →ₗ[ℂ] H) (ha : a.IsSymmetric)
    (x : H) (hx : ‖x‖ = 1) (m : ℕ) :
    ‖a x‖ ^ (2 * m) ≤ ‖(a ^ m) x‖ ^ 2 := by
  have hw : ∑ i : Fin (Module.finrank ℂ H),
      ‖(ha.eigenvectorBasis rfl).repr x i‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, (ha.eigenvectorBasis rfl).repr.norm_map, hx, one_pow]
  have hj := (convexOn_pow (𝕜 := ℝ) m).map_sum_le
    (t := Finset.univ) (w := fun i => ‖(ha.eigenvectorBasis rfl).repr x i‖ ^ 2)
    (p := fun i => ha.eigenvalues rfl i ^ 2)
    (fun i _ => sq_nonneg _) hw (fun i _ => show 0 ≤ ha.eigenvalues rfl i ^ 2 from sq_nonneg _)
  rw [symmetric_pow_norm_sq a ha x m, pow_mul]
  have hn := symmetric_pow_norm_sq a ha x 1
  simp only [pow_one] at hn
  rw [hn]
  exact hj

lemma symmetric_trace_even (a : H →ₗ[ℂ] H) (ha : a.IsSymmetric) (m : ℕ) :
    (LinearMap.trace ℂ H (a ^ (2 * m))).re =
      ∑ i : Fin (Module.finrank ℂ H), (ha.eigenvalues rfl i ^ 2) ^ m := by
  rw [LinearMap.trace_eq_sum_inner _ (ha.eigenvectorBasis rfl), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : (a ^ (2 * m)) (ha.eigenvectorBasis rfl i) =
      (ha.eigenvalues rfl i : ℂ) ^ (2 * m) • ha.eigenvectorBasis rfl i :=
    (ha.hasEigenvector_eigenvectorBasis rfl i).pow_apply _
  rw [he, inner_smul_right, (ha.eigenvectorBasis rfl).inner_eq_one, mul_one]
  norm_cast
  rw [pow_mul]

lemma orthonormal_sum_norm_pow_le_trace {ι : Type*} [Fintype ι]
    (a : H →ₗ[ℂ] H) (ha : a.IsSymmetric) (v : ι → H)
    (hv : Orthonormal ℂ v) (m : ℕ) :
    ∑ j, ‖(a ^ m) (v j)‖ ^ 2 ≤ (LinearMap.trace ℂ H (a ^ (2 * m))).re := by
  simp_rw [symmetric_pow_norm_sq a ha]
  rw [Finset.sum_comm, symmetric_trace_even a ha m]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.sum_mul]
  have hb := hv.sum_inner_products_le (ha.eigenvectorBasis rfl i) (s := Finset.univ)
  simp only [(ha.eigenvectorBasis rfl).norm_eq_one, one_pow] at hb
  simp_rw [OrthonormalBasis.repr_apply_apply, norm_inner_symm]
  exact (mul_le_mul_of_nonneg_right hb (by positivity)).trans_eq (one_mul _)

/-- Manuscript Lemma `lem:trace`, with the real part of the (real) complex trace. -/
theorem trace_even_pow_ge_rank (a p : H →L[ℂ] H) (ha : IsSelfAdjoint a)
    (hp : IsStarProjection p) {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 1)
    (hap : ‖a - p‖ ≤ δ) (m : ℕ) :
    (Module.finrank ℂ (LinearMap.range p.toLinearMap) : ℝ) * (1 - δ) ^ (2 * m) ≤
      (LinearMap.trace ℂ H (a ^ (2 * m)).toLinearMap).re := by
  let V := LinearMap.range p.toLinearMap
  let b := stdOrthonormalBasis ℂ V
  let v : Fin (Module.finrank ℂ V) → H := fun i => (b i : H)
  have hv : Orthonormal ℂ v := b.orthonormal.comp_linearIsometry V.subtypeₗᵢ
  have hlow (i : Fin (Module.finrank ℂ V)) : 1 - δ ≤ ‖a (v i)‖ := by
    have hpv : p (v i) = v i := by
      obtain ⟨y, hy⟩ := (b i).property
      change p y = v i at hy
      rw [← hy]
      exact congrArg (fun q : H →L[ℂ] H => q y) hp.isIdempotentElem.eq
    have hb := (a - p).le_opNorm (v i)
    have hn := norm_sub_norm_le (p (v i)) (a (v i))
    rw [hpv, hv.norm_eq_one i] at hn
    simp only [sub_apply, hv.norm_eq_one i, mul_one] at hb
    rw [norm_sub_rev, hpv] at hb
    linarith
  have hsum : ∑ i : Fin (Module.finrank ℂ V), (1 - δ) ^ (2 * m) ≤ ∑ i, ‖(a.toLinearMap ^ m) (v i)‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    exact (pow_le_pow_left₀ (by linarith [hδ.2]) (hlow i) _).trans
      (symmetric_norm_pow_le a.toLinearMap ha.isSymmetric (v i) (hv.norm_eq_one i) m)
  rw [ContinuousLinearMap.toLinearMap_pow]
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
    hsum.trans (orthonormal_sum_norm_pow_le_trace a.toLinearMap ha.isSymmetric v hv m)

/-- The trace in Lemma `lem:trace` is real and has the asserted lower bound. -/
theorem trace_projection_estimate (a p : H →L[ℂ] H) (ha : IsSelfAdjoint a)
    (hp : IsStarProjection p) {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 1)
    (hap : ‖a - p‖ ≤ δ) (m : ℕ) :
    ∃ t : ℝ, LinearMap.trace ℂ H (a ^ (2 * m)).toLinearMap = (t : ℂ) ∧
      (Module.finrank ℂ (LinearMap.range p.toLinearMap) : ℝ) * (1 - δ) ^ (2 * m) ≤ t := by
  rw [ContinuousLinearMap.toLinearMap_pow]
  refine ⟨_, (ha.isSymmetric.pow (2 * m)).trace_eq_sum_eigenvalues rfl, ?_⟩
  have ht := trace_even_pow_ge_rank a p ha hp hδ hap m
  rw [ContinuousLinearMap.toLinearMap_pow,
    (ha.isSymmetric.pow (2 * m)).trace_eq_sum_eigenvalues rfl] at ht
  simpa using ht

end DynamicalCStarAlgebras
