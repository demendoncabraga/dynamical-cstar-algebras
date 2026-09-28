import DynamicalCStarAlgebras.FejerAverages

noncomputable section

namespace DynamicalCStarAlgebras

open MeasureTheory

lemma integral_Ioi_fejerKernel_le {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) :
    (∫ t : ℝ in Set.Ioi δ, fejerKernel s t) ≤ 2 / (s * Real.pi * δ) := by
  have hbound : ∀ t ∈ Set.Ioi δ, fejerKernel s t ≤ (2 / (s * Real.pi)) * t ^ (-2 : ℝ) := by
    intro t ht
    have htpos : 0 < t := hδ.trans ht
    have hb := fejerKernel_tail_bound hs htpos.ne'
    simpa only [Real.rpow_neg htpos.le, Real.rpow_two, div_mul_eq_div_mul_one_div,
      one_div] using hb
  have hi := setIntegral_mono_on (integrable_fejerKernel hs).integrableOn
    ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hδ).const_mul
      (2 / (s * Real.pi))) measurableSet_Ioi hbound
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hδ] at hi
  norm_num [Real.rpow_neg_one] at hi
  simpa only [div_mul_eq_div_mul_one_div, one_div] using! hi

/-- The integrated Fejér tail bound used in the proof of norm convergence. -/
theorem integral_fejerKernel_tail_le {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) :
    (∫ t : ℝ in {t | δ < |t|}, fejerKernel s t) ≤ 4 / (s * Real.pi * δ) := by
  have hset : {t : ℝ | δ < |t|} = Set.Iio (-δ) ∪ Set.Ioi δ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  have hd : Disjoint (Set.Iio (-δ)) (Set.Ioi δ) := by
    exact Set.disjoint_left.mpr fun _ hx hy => by
      change _ < -δ at hx
      change δ < _ at hy
      linarith
  have heq : (∫ t : ℝ in Set.Iio (-δ), fejerKernel s t) =
      ∫ t : ℝ in Set.Ioi δ, fejerKernel s t := by
    rw [← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi δ (fejerKernel s)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      simp [fejerKernel, mul_neg, neg_div, Real.sinc_neg]
  rw [hset, setIntegral_union hd measurableSet_Ioi (integrable_fejerKernel hs).integrableOn
    (integrable_fejerKernel hs).integrableOn, heq]
  have hi := integral_Ioi_fejerKernel_le hs hδ
  calc
    _ ≤ 2 / (s * Real.pi * δ) + 2 / (s * Real.pi * δ) := add_le_add hi hi
    _ = _ := by ring

/-- The precise quantitative error estimate in the manuscript's Fejér-convergence proof. -/
theorem fejerAverage_sub_norm_le_of_local_bound {X : Type*} (h : X → ℝ)
    (a : Operator X) (ha : a ∈ continuityPoints h) {s δ ε : ℝ}
    (hs : 0 < s) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hlocal : ∀ t : ℝ, |t| ≤ δ → ‖diagonalFlow h t a - a‖ ≤ ε) :
    ‖fejerAverage h s a - a‖ ≤ ε + 8 * ‖a‖ / (s * Real.pi * δ) := by
  have hglobal : ∀ t : ℝ, ‖diagonalFlow h t a - a‖ ≤ 2 * ‖a‖ := by
    intro t
    simpa only [diagonalFlow_norm, two_mul] using norm_sub_le (diagonalFlow h t a) a
  have hint : Integrable (fun t => fejerKernel s t * ‖diagonalFlow h t a - a‖) :=
    (integrable_fejerKernel hs).mul_bdd (ha.sub continuous_const).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by simpa only [norm_norm] using hglobal t)
  have hmass : (∫ t : ℝ, (fejerKernel s t : ℂ)) = 1 := by
    simpa only [integral_fejerKernel hs, RCLike.ofReal_one] using!
      (integral_ofReal (𝕜 := ℂ) (μ := volume) (f := fejerKernel s))
  have herror : ‖fejerAverage h s a - a‖ ≤
      ∫ t : ℝ, fejerKernel s t * ‖diagonalFlow h t a - a‖ := by
    simpa only [fejerAverage, Complex.norm_real,
      Real.norm_of_nonneg (fejerKernel_nonneg hs.le _)] using!
      averagingOperator_sub_norm_le h (f := fun t : ℝ => (fejerKernel s t : ℂ))
        (integrable_fejerKernel_all s).ofReal a ha hmass
  have hmeas : MeasurableSet {t : ℝ | |t| ≤ δ} :=
    isClosed_le continuous_abs continuous_const |>.measurableSet
  have hinside : (∫ t : ℝ in {t | |t| ≤ δ}, fejerKernel s t *
      ‖diagonalFlow h t a - a‖) ≤ ε := by
    have hb := setIntegral_mono_on hint.integrableOn
      ((integrable_fejerKernel hs).mul_const ε).integrableOn hmeas
      (fun t ht => mul_le_mul_of_nonneg_left (hlocal t ht) (fejerKernel_nonneg hs.le t))
    rw [integral_mul_const] at hb
    have hm : (∫ t : ℝ in {t | |t| ≤ δ}, fejerKernel s t) ≤ 1 := by
      simpa only [integral_fejerKernel hs] using
        setIntegral_le_integral (s := {t : ℝ | |t| ≤ δ}) (integrable_fejerKernel hs)
          (Filter.Eventually.of_forall fun t => fejerKernel_nonneg hs.le t)
    exact hb.trans (by nlinarith)
  have houtside : (∫ t : ℝ in {t | δ < |t|}, fejerKernel s t *
      ‖diagonalFlow h t a - a‖) ≤ 8 * ‖a‖ / (s * Real.pi * δ) := by
    have hb := setIntegral_mono_on (s := {t : ℝ | δ < |t|}) hint.integrableOn
      ((integrable_fejerKernel hs).mul_const (2 * ‖a‖)).integrableOn
      (isOpen_lt continuous_const continuous_abs).measurableSet
      (fun t _ => mul_le_mul_of_nonneg_left (hglobal t) (fejerKernel_nonneg hs.le t))
    rw [integral_mul_const] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_right (integral_fejerKernel_tail_le hs hδ)
      (by positivity)).trans_eq (by ring))
  have hcompl : {t : ℝ | |t| ≤ δ}ᶜ = {t : ℝ | δ < |t|} := by ext t; simp
  rw [← integral_add_compl hmeas hint, hcompl] at herror
  exact herror.trans (add_le_add hinside houtside)

end DynamicalCStarAlgebras
