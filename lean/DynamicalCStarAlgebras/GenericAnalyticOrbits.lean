import DynamicalCStarAlgebras.GaussianApproximation
import Mathlib.Analysis.Calculus.Deriv.Star

noncomputable section
open MeasureTheory Filter Complex
open scoped Topology
namespace DynamicalCStarAlgebras

/-- Entire analytic elements for an arbitrary family of C*-automorphisms. -/
def analyticOrbitSubalgebra {A : Type*} [NonUnitalCStarAlgebra A]
    (σ : ℝ → A ≃⋆ₐ[ℂ] A) : NonUnitalStarSubalgebra ℂ A where
  carrier := {a | ∃ F : ℂ → A, Differentiable ℂ F ∧ ∀ t : ℝ, F (t : ℂ) = σ t a}
  zero_mem' := ⟨fun _ => 0, differentiable_const _, by simp⟩
  add_mem' := by
    rintro a b ⟨F, hF, hFa⟩ ⟨G, hG, hGb⟩
    exact ⟨fun z => F z + G z, hF.add hG, by simp [hFa, hGb]⟩
  mul_mem' := by
    rintro a b ⟨F, hF, hFa⟩ ⟨G, hG, hGb⟩
    refine ⟨fun z => F z * G z, ?_, by simp [hFa, hGb]⟩
    exact ((ContinuousLinearMap.mul ℂ A).differentiable.comp hF).clm_apply hG
  star_mem' := by
    rintro a ⟨F, hF, hFa⟩
    refine ⟨fun z => star (F (star z)), ?_, ?_⟩
    · intro z
      simpa only [Function.comp_def, starRingEnd_apply, star_star] using (hF (star z)).star_conj
    · intro t
      simpa only [Complex.star_def, Complex.conj_ofReal, hFa] using (map_star (σ t) a).symm
  smul_mem' := by
    rintro c a ⟨F, hF, hFa⟩
    exact ⟨fun z => c • F z, hF.const_smul c, by simp [hFa]⟩

/-- A C*-automorphism is an isometry as a complex linear map. -/
def cstarAutomorphismLinearIsometry {A : Type*} [NonUnitalCStarAlgebra A]
    (e : A ≃⋆ₐ[ℂ] A) : A →ₗᵢ[ℂ] A where
  toFun := e
  map_add' := e.map_add
  map_smul' := fun c a => map_smul e c a
  norm_map' := StarAlgEquiv.norm_map e

/-- The normalized Gaussian extension of an orbit. -/
def gaussianOrbitExtension {A : Type*} [NonUnitalCStarAlgebra A]
    (σ : ℝ → A ≃⋆ₐ[ℂ] A) (a : A) (z : ℂ) : A :=
  (Real.sqrt Real.pi : ℂ)⁻¹ • ∫ t : ℝ, gaussianTranslateKernel z t • σ t a

lemma gaussianOrbitExtension_entire {A : Type*} [NonUnitalCStarAlgebra A]
    (σ : ℝ → A ≃⋆ₐ[ℂ] A) (a : A) (ha : Continuous (fun t => σ t a)) :
    Differentiable ℂ (gaussianOrbitExtension σ a) :=
  (gaussian_smoothing_entire (fun t => σ t a) ha
    (fun t => (StarAlgEquiv.norm_map (σ t) a).le)).const_smul _

lemma gaussianOrbitExtension_real {A : Type*} [NonUnitalCStarAlgebra A]
    (σ : ℝ → A ≃⋆ₐ[ℂ] A)
    (hadd : ∀ s t a, σ (s + t) a = σ s (σ t a)) (a : A) (t : ℝ) :
    gaussianOrbitExtension σ a (t : ℂ) = σ t (gaussianOrbitExtension σ a 0) := by
  unfold gaussianOrbitExtension
  rw [map_smul]
  congr 1
  change _ = cstarAutomorphismLinearIsometry (σ t) _
  rw [← (cstarAutomorphismLinearIsometry (σ t)).integral_comp_comm]
  rw [← integral_add_left_eq_self (fun s : ℝ => gaussianTranslateKernel (t : ℂ) s • σ s a) t]
  apply integral_congr_ae
  filter_upwards with s
  change gaussianTranslateKernel (t : ℂ) (t + s) • σ (t + s) a =
    σ t (gaussianTranslateKernel 0 s • σ s a)
  simp [gaussianTranslateKernel, hadd]

/-- A Gaussian-smoothed continuous orbit is an entire analytic element. -/
lemma gaussianOrbitExtension_scaled_mem {A : Type*} [NonUnitalCStarAlgebra A]
    (σ : ℝ → A ≃⋆ₐ[ℂ] A)
    (hadd : ∀ s t a, σ (s + t) a = σ s (σ t a))
    (a : A) (ha : Continuous (fun t => σ t a)) {ε : ℝ} (hε : ε ≠ 0) :
    gaussianOrbitExtension (fun t => σ (ε * t)) a 0 ∈ analyticOrbitSubalgebra σ := by
  have hscaled : ∀ s t b, σ (ε * (s + t)) b = σ (ε * s) (σ (ε * t) b) := by
    intro s t b
    rw [mul_add, hadd]
  refine ⟨fun z => gaussianOrbitExtension (fun t => σ (ε * t)) a (z / (ε : ℂ)),
    (gaussianOrbitExtension_entire _ a (ha.comp (by fun_prop))).comp
      (differentiable_id.div_const _), ?_⟩
  intro t
  dsimp only
  rw [← Complex.ofReal_div, gaussianOrbitExtension_real _ hscaled,
    mul_div_cancel₀ _ hε]

/-- For any one-parameter automorphism group, the entire analytic elements are
dense precisely in its algebra of norm-continuous orbit elements. -/
theorem closure_analyticOrbitSubalgebra {A : Type*} [NonUnitalCStarAlgebra A]
    (σ : ℝ → A ≃⋆ₐ[ℂ] A)
    (hadd : ∀ s t a, σ (s + t) a = σ s (σ t a)) :
    closure (analyticOrbitSubalgebra σ : Set A) = (continuousOrbitSubalgebra σ : Set A) := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ (continuousOrbitSubalgebra_isClosed σ)
    rintro a ⟨F, hF, hFa⟩
    change Continuous (fun t => σ t a)
    have hcont := hF.continuous.comp Complex.continuous_ofReal
    simpa only [Function.comp_def, hFa] using hcont
  · intro a ha
    have hzero : σ 0 a = a := by
      apply (σ 0).injective
      change σ 0 (σ 0 a) = σ 0 a
      simpa only [zero_add] using (hadd 0 0 a).symm
    have hlim := gaussian_smoothing_approximation (fun t => σ t a) ha
      (fun t => (StarAlgEquiv.norm_map (σ t) a).le)
    have hseq : ∀ n : ℕ, gaussianOrbitExtension (fun t => σ ((1 / ((n : ℝ) + 1)) * t)) a 0 ∈
        analyticOrbitSubalgebra σ := by
      intro n
      exact gaussianOrbitExtension_scaled_mem σ hadd a ha (by positivity)
    have hlim' : Tendsto (fun n : ℕ =>
        gaussianOrbitExtension (fun t => σ ((1 / ((n : ℝ) + 1)) * t)) a 0) atTop (𝓝 a) := by
      simpa only [gaussianOrbitExtension, one_div_mul_eq_div, hzero] using hlim
    exact mem_closure_of_tendsto hlim' (Filter.Eventually.of_forall hseq)

/-- Entire analytic elements form a dense complex star-subalgebra for every
norm-continuous C*-algebra flow, with no unit hypothesis. -/
theorem analyticOrbitSubalgebra_dense {A : Type*} [NonUnitalCStarAlgebra A]
    (σ : ℝ → A ≃⋆ₐ[ℂ] A)
    (hadd : ∀ s t a, σ (s + t) a = σ s (σ t a))
    (hcont : ∀ a, Continuous (fun t => σ t a)) :
    Dense (analyticOrbitSubalgebra σ : Set A) := by
  intro a
  rw [closure_analyticOrbitSubalgebra σ hadd]
  exact hcont a

end DynamicalCStarAlgebras
