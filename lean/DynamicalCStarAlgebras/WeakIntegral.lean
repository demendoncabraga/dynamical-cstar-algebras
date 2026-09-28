import DynamicalCStarAlgebras.Averaging
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section
open MeasureTheory
namespace DynamicalCStarAlgebras

variable {S H : Type*} [MeasurableSpace S] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The integrated sesquilinear form. Scalar integrability is the exact weak
integrability requirement, without separability or operator-norm integrability. -/
def weakIntegralForm (μ : Measure S) (f : S → H →L[ℂ] H)
    (hf : ∀ v w, Integrable (fun s => inner ℂ v (f s w)) μ) :
    H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ where
  toFun v :=
    { toFun := fun w => ∫ s, inner ℂ v (f s w) ∂μ
      map_add' := fun w z => by
        simp only [map_add, inner_add_right]
        exact integral_add (hf v w) (hf v z)
      map_smul' := fun c w => by
        simp only [map_smul, inner_smul_right, RingHom.id_apply, integral_const_mul,
          smul_eq_mul] }
  map_add' v w := by
    apply LinearMap.ext
    intro z
    change (∫ s, inner ℂ (v + w) (f s z) ∂μ) =
      (∫ s, inner ℂ v (f s z) ∂μ) + ∫ s, inner ℂ w (f s z) ∂μ
    simp only [inner_add_left]
    exact integral_add (hf v z) (hf w z)
  map_smul' c v := by
    apply LinearMap.ext
    intro w
    change (∫ s, inner ℂ (c • v) (f s w) ∂μ) =
      star c * ∫ s, inner ℂ v (f s w) ∂μ
    simp only [inner_smul_left, integral_const_mul, starRingEnd_apply]

/-- Section 2.4: every bounded integrated sesquilinear form is represented by
exactly one bounded complex-linear operator. Inner-product arguments are reversed
to match Mathlib's scalar convention. -/
theorem exists_unique_weakIntegral (μ : Measure S) (f : S → H →L[ℂ] H)
    (hf : ∀ v w, Integrable (fun s => inner ℂ v (f s w)) μ)
    (hbound : ∃ C : ℝ, ∀ v w,
      ‖∫ s, inner ℂ v (f s w) ∂μ‖ ≤ C * ‖v‖ * ‖w‖) :
    ∃! T : H →L[ℂ] H, ∀ v w, inner ℂ v (T w) =
      ∫ s, inner ℂ v (f s w) ∂μ := by
  obtain ⟨C, hC⟩ := hbound
  let B := (weakIntegralForm μ f hf).mkContinuous₂ C hC
  let T := (InnerProductSpace.continuousLinearMapOfBilin B).adjoint
  have hT (v w : H) : inner ℂ v (T w) = ∫ s, inner ℂ v (f s w) ∂μ := by
    exact ((InnerProductSpace.continuousLinearMapOfBilin B).adjoint_inner_right v w).trans
      (InnerProductSpace.continuousLinearMapOfBilin_apply B v w)
  refine ⟨T, hT, ?_⟩
  intro S hS
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_left ℂ
  intro v
  rw [hS, hT]

end DynamicalCStarAlgebras
