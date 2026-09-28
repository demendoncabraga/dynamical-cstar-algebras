import DynamicalCStarAlgebras.TranslationAveraging

namespace DynamicalCStarAlgebras

open MeasureTheory

universe u

/-- The real-valued de la Vallee Poussin kernel, viewed as a complex integrable kernel. -/
noncomputable def valleePoussin (s t : ℝ) : ℂ :=
  2 * (fejerKernel (2 * s) t : ℂ) - (fejerKernel s t : ℂ)

theorem integrable_valleePoussin (s : ℝ) : Integrable (valleePoussin s) := by
  exact ((integrable_fejerKernel_all (2 * s)).ofReal.const_mul (2 : ℂ)).sub
    (integrable_fejerKernel_all s).ofReal

theorem continuous_valleePoussin (s : ℝ) : Continuous (valleePoussin s) := by
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    (continuous_fejerKernel (2 * s)))).sub
      (Complex.continuous_ofReal.comp (continuous_fejerKernel s))

theorem integrable_fourierPlus_integrand {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun t => f t * Complex.exp (((t * ξ : ℝ) : ℂ) * Complex.I)) := by
  exact hf.smul_bdd 1 (continuous_diagonalPhase (fun _ : Unit => ξ) ()).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => (diagonalPhase_norm (fun _ : Unit => ξ) t ()).le)

theorem fourierPlus_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    fourierPlus (fun t => f t - g t) ξ = fourierPlus f ξ - fourierPlus g ξ := by
  simpa only [fourierPlus, sub_mul] using
    integral_sub (integrable_fourierPlus_integrand hf ξ) (integrable_fourierPlus_integrand hg ξ)

theorem fourierPlus_const_mul (c : ℂ) (f : ℝ → ℂ) (ξ : ℝ) :
    fourierPlus (fun t => c * f t) ξ = c * fourierPlus f ξ := by
  simp only [fourierPlus, mul_assoc, integral_const_mul]

theorem fourierPlus_valleePoussin {s : ℝ} (hs : 0 < s) (ξ : ℝ) :
    fourierPlus (valleePoussin s) ξ =
      2 * ((max (1 - |ξ| / (2 * s)) 0 : ℝ) : ℂ) - (max (1 - |ξ| / s) 0 : ℝ) := by
  unfold valleePoussin
  erw [fourierPlus_sub ((integrable_fejerKernel_all (2 * s)).ofReal.const_mul (2 : ℂ))
    (integrable_fejerKernel_all s).ofReal, fourierPlus_const_mul]
  erw [fourierPlus_fejerKernel (by positivity : 0 < 2 * s), fourierPlus_fejerKernel hs]

/-- Equation 5.03.Aug.26: the Fourier transform is one on the closed interval [-s,s]. -/
theorem fourierPlus_valleePoussin_plateau {s : ℝ} (hs : 0 < s) {ξ : ℝ} (hξ : |ξ| ≤ s) :
    fourierPlus (valleePoussin s) ξ = 1 := by
  have h1 : 0 ≤ 1 - |ξ| / s := sub_nonneg.mpr ((div_le_one hs).mpr hξ)
  have h2 : 0 ≤ 1 - |ξ| / (2 * s) :=
    sub_nonneg.mpr ((div_le_one (by positivity)).mpr (by linarith))
  rw [fourierPlus_valleePoussin hs, max_eq_left h1, max_eq_left h2]
  push_cast
  ring

theorem valleePoussin_norm_le {s : ℝ} (hs : 0 < s) (t : ℝ) :
    ‖valleePoussin s t‖ ≤ 2 * fejerKernel (2 * s) t + fejerKernel s t := by
  simpa [valleePoussin, norm_mul, Complex.norm_real,
    abs_of_nonneg (fejerKernel_nonneg hs.le t),
    abs_of_nonneg (fejerKernel_nonneg (by positivity : 0 ≤ 2 * s) t)] using
    norm_sub_le (2 * (fejerKernel (2 * s) t : ℂ)) (fejerKernel s t : ℂ)

/-- Equation 5.03.Aug.26: the kernel has L1 norm at most three. -/
theorem integral_norm_valleePoussin_le {s : ℝ} (hs : 0 < s) :
    ∫ t, ‖valleePoussin s t‖ ≤ 3 := by
  have hi := integral_mono (integrable_valleePoussin s).norm
    (((integrable_fejerKernel_all (2 * s)).const_mul 2).add (integrable_fejerKernel_all s))
    (valleePoussin_norm_le hs)
  simpa only [Pi.add_apply, integral_add ((integrable_fejerKernel_all (2 * s)).const_mul 2)
    (integrable_fejerKernel_all s), integral_const_mul, integral_fejerKernel hs,
    integral_fejerKernel (by positivity : 0 < 2 * s), mul_one,
    show (2 : ℝ) + 1 = 3 by norm_num] using hi

theorem valleePoussin_has_integrable_bound {s : ℝ} (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖valleePoussin s t‖ ≤ C * (1 + t ^ 2)⁻¹ := by
  let c (r : ℝ) := r / (2 * Real.pi) * (1 + 4 / r ^ 2)
  refine ⟨2 * c (2 * s) + c s, ?_, ?_⟩
  · positivity
  · intro t
    nlinarith [valleePoussin_norm_le hs t, fejerKernel_le_integrable_bound hs t,
      fejerKernel_le_integrable_bound (by positivity : 0 < 2 * s) t]

theorem averaging_valleePoussin_eq_self {X : Type u} (h : X → ℝ) {s : ℝ} (hs : 0 < s)
    (a : Operator X) (ha : ∀ x y, s < |h x - h y| → matrixEntry a x y = 0) :
    averagingOperator h (integrable_valleePoussin s) a = a := by
  refine operator_ext fun x y => ?_
  rw [matrixEntry_averagingOperator]
  by_cases hxy : |h x - h y| ≤ s
  · rw [fourierPlus_valleePoussin_plateau hs hxy, one_mul]
  · rw [ha x y (lt_of_not_ge hxy), mul_zero]

/-- Every finite d_h-propagation operator is a norm-continuity point. -/
theorem finitePropagation_mem_continuityPoints {X : Type u} (h : X → ℝ) (a : Operator X)
    (ha : @HasFinitePropagation X (realPullbackPseudoMetric h) a) : a ∈ continuityPoints h := by
  obtain ⟨s, hs, hprop⟩ := ha
  obtain ⟨C, hC, hb⟩ := valleePoussin_has_integrable_bound hs
  have he := averaging_valleePoussin_eq_self h hs a
    (fun x y hxy => hprop x y ((realPullbackPseudoMetric_dist h x y).symm ▸ hxy))
  exact he ▸ averagingOperator_mem_continuityPoints h (integrable_valleePoussin s)
    (continuous_valleePoussin s) hC hb a

end DynamicalCStarAlgebras
