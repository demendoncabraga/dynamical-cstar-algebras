import DynamicalCStarAlgebras.TraceEstimate

noncomputable section
namespace DynamicalCStarAlgebras
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

lemma symmetric_trace_even_eq_sum_norm {ι : Type*} [Fintype ι]
    (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) (b : OrthonormalBasis ι ℂ H) (m : ℕ) :
    (LinearMap.trace ℂ H (a ^ (2 * m)).toLinearMap).re =
      ∑ i, ‖(a ^ m) (b i)‖ ^ 2 := by
  rw [LinearMap.trace_eq_sum_inner _ b, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [two_mul, pow_add]
  change (inner ℂ (b i) ((a ^ m) ((a ^ m) (b i)))).re = _
  rw [← (ha.pow m).isSymmetric.apply_clm]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

lemma trace_even_pow_le_of_basis_bound {ι : Type*} [Fintype ι]
    (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) (b : OrthonormalBasis ι ℂ H)
    (m : ℕ) {B : ℝ} (hb : ∀ i, ‖(a ^ m) (b i)‖ ≤ B) :
    (LinearMap.trace ℂ H (a ^ (2 * m)).toLinearMap).re ≤ Fintype.card ι * B ^ 2 := by
  rw [symmetric_trace_even_eq_sum_norm a ha b m]
  calc
    _ ≤ ∑ _i : ι, B ^ 2 := Finset.sum_le_sum fun i _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hb i) 2
    _ = _ := by simp

/-- The comparison of upper and lower trace estimates in Eq.1.sep.26.1.rain. -/
theorem trace_power_ratio_bound (a p : H →L[ℂ] H) (ha : IsSelfAdjoint a)
    (hp : IsStarProjection p) {δ α : ℝ} (hδ : δ ∈ Set.Ioo 0 1)
    (hap : ‖a - p‖ ≤ δ) (m : ℕ)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H)
    (hN : 1 < (Module.finrank ℂ H : ℝ))
    (hrank : (Module.finrank ℂ H : ℝ) /
      (2 * Real.log (Module.finrank ℂ H) ^ (2 * α)) ≤
        Module.finrank ℂ (LinearMap.range p.toLinearMap))
    (hb : ∀ i, ‖(a ^ m) (b i)‖ ≤ 2 * (2 * δ) ^ m) :
    ((1 - δ) / (2 * δ)) ^ (2 * m) ≤
      8 * Real.log (Module.finrank ℂ H) ^ (2 * α) := by
  have hL : 0 < Real.log (Module.finrank ℂ H) ^ (2 * α) :=
    Real.rpow_pos_of_pos (Real.log_pos hN) _
  have hlow := trace_even_pow_ge_rank a p ha hp hδ hap m
  have hup := trace_even_pow_le_of_basis_bound a ha b m hb
  have hr := mul_le_mul_of_nonneg_right hrank (show 0 ≤ (1 - δ) ^ (2 * m) from pow_nonneg (sub_nonneg.mpr hδ.2.le) _)
  have ht := hr.trans (hlow.trans hup)
  simp only [Fintype.card_fin] at ht
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity :
    0 < 2 * Real.log (Module.finrank ℂ H) ^ (2 * α))] at ht
  have hm : (2 * (2 * δ) ^ m) ^ 2 = 4 * (2 * δ) ^ (2 * m) := by ring
  rw [hm] at ht
  have hc : (1 - δ) ^ (2 * m) ≤
      8 * Real.log (Module.finrank ℂ H) ^ (2 * α) * (2 * δ) ^ (2 * m) := by
    apply (mul_le_mul_iff_right₀ (show 0 < (Module.finrank ℂ H : ℝ) by linarith)).mp
    nlinarith only [ht]
  rw [div_pow]
  exact (div_le_iff₀ (pow_pos (by linarith [hδ.1]) _)).mpr hc

end DynamicalCStarAlgebras
