import DynamicalCStarAlgebras.TraceComparison

noncomputable section
open Filter
open scoped Topology
namespace DynamicalCStarAlgebras

lemma floor_power_lower_bound {b c t β : ℝ} (hb : 1 ≤ b) (ht : 0 < t) :
    b ^ (-2 : ℝ) * t ^ (2 * β * Real.log b / Real.log c) ≤
      b ^ (2 * ⌊β * Real.log t / Real.log c⌋₊) := by
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  have hn := (Nat.lt_floor_add_one (β * Real.log t / Real.log c)).le
  have he : Real.log b * (-2) + Real.log t * (2 * β * Real.log b / Real.log c) ≤
      (2 * ⌊β * Real.log t / Real.log c⌋₊ : ℕ) * Real.log b := by
    push_cast
    have h := mul_le_mul_of_nonneg_left hn (Real.log_nonneg hb)
    simp only [div_eq_mul_inv] at h ⊢
    nlinarith only [h]
  rw [Real.rpow_def_of_pos hbpos, Real.rpow_def_of_pos ht, ← Real.exp_add,
    ← Real.exp_log hbpos, ← Real.exp_nat_mul]
  simpa only [Real.log_exp] using Real.exp_le_exp.mpr he

lemma exponent_le_of_eventual_rpow_bound {x : ℕ → ℝ} {u v c C : ℝ}
    (hx : Tendsto x atTop atTop) (hc : 0 < c)
    (hb : ∀ᶠ n in atTop, c * x n ^ u ≤ C * x n ^ v) : u ≤ v := by
  by_contra huv
  have hd : 0 < u - v := sub_pos.mpr (lt_of_not_ge huv)
  have ht := (tendsto_rpow_atTop hd).comp hx
  have hh := ht.eventually (eventually_gt_atTop (C / c))
  obtain ⟨n, hn, hp, hb⟩ := (hh.and ((hx.eventually (eventually_gt_atTop 0)).and hb)).exists
  simp only [Function.comp_apply, Real.rpow_sub hp] at hn
  have hv : 0 < x n ^ v := Real.rpow_pos_of_pos hp _
  have h1 := (lt_div_iff₀ hv).mp hn
  have h2 := (div_mul_eq_mul_div C c (x n ^ v))
  rw [h2] at h1
  have h3 := (div_lt_iff₀ hc).mp h1
  nlinarith only [h3, hb]

/-- The eventual trace comparison forces the exponent inequality after rounding `m_n`. -/
theorem trace_exponent_le_of_eventual_ratio_bound {N : ℕ → ℝ} {δ α β : ℝ}
    (hN : Tendsto N atTop atTop) (hδ : δ ∈ Set.Ioo 0 (1 / 3 : ℝ))
    (hb : ∀ᶠ n in atTop,
      ((1 - δ) / (2 * δ)) ^
        (2 * ⌊β * Real.log (Real.log (N n)) / Real.log ((1 + δ) / δ)⌋₊) ≤
          8 * Real.log (N n) ^ (2 * α)) :
    β * (Real.log ((1 - δ) / (2 * δ)) / Real.log ((1 + δ) / δ)) ≤ α := by
  have hbase : 1 ≤ (1 - δ) / (2 * δ) :=
    (le_div_iff₀ (by linarith [hδ.1])).mpr (by linarith [hδ.2])
  have hx : Tendsto (fun n => Real.log (N n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hN
  have hp : 0 < (1 - δ) / (2 * δ) := zero_lt_one.trans_le hbase
  have hpow : ∀ᶠ n in atTop,
      ((1 - δ) / (2 * δ)) ^ (-2 : ℝ) *
        Real.log (N n) ^ (2 * β * Real.log ((1 - δ) / (2 * δ)) /
          Real.log ((1 + δ) / δ)) ≤ 8 * Real.log (N n) ^ (2 * α) := by
    filter_upwards [hb, hx.eventually (eventually_gt_atTop 0)] with n hn hpos
    exact (floor_power_lower_bound hbase hpos).trans hn
  have he := exponent_le_of_eventual_rpow_bound hx
    (Real.rpow_pos_of_pos hp (-2)) hpow
  simp only [div_eq_mul_inv] at he ⊢
  nlinarith only [he]

lemma tendsto_trace_log_ratio :
    Tendsto (fun δ : ℝ => Real.log ((1 - δ) / (2 * δ)) /
      Real.log ((1 + δ) / δ)) (𝓝[>] 0) (𝓝 1) := by
  have hid : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hp : Tendsto (fun δ : ℝ => Real.log (1 + δ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.add hid).log (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have hm : Tendsto (fun δ : ℝ => Real.log (1 - δ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.sub hid).log (by norm_num : (1 : ℝ) - 0 ≠ 0)
  have hd : Tendsto (fun δ : ℝ => Real.log (1 + δ) - Real.log δ) (𝓝[>] 0) atTop := by
    simpa only [sub_eq_add_neg, Function.comp_apply] using
      hp.add_atTop (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).add
    (((hm.sub_const (Real.log 2)).sub hp).div_atTop hd)
  have ht' : Tendsto (fun δ : ℝ => 1 +
      (Real.log (1 - δ) - Real.log 2 - Real.log (1 + δ)) /
        (Real.log (1 + δ) - Real.log δ)) (𝓝[>] 0) (𝓝 1) := by simpa using ht
  apply ht'.congr'
  filter_upwards [eventually_mem_nhdsWithin,
    hid.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with δ hδ hδ1
  have hpos : 0 < δ := hδ
  have hden : 0 < Real.log ((1 + δ) / δ) :=
    Real.log_pos ((lt_div_iff₀ hpos).mpr (by linarith))
  rw [Real.log_div (by linarith : 1 + δ ≠ 0) hpos.ne'] at hden
  rw [Real.log_div (by linarith : 1 - δ ≠ 0) (by positivity : 2 * δ ≠ 0),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hpos.ne',
    Real.log_div (by linarith : 1 + δ ≠ 0) hpos.ne']
  field_simp
  ring

/-- The numerical contradiction in the nonmembership proof, allowing the threshold
in the component index to depend on the approximation error. -/
theorem trace_asymptotic_obstruction {N : ℕ → ℝ} {α β : ℝ}
    (hN : Tendsto N atTop atTop)
    (hb : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᶠ n in atTop,
      ((1 - δ) / (2 * δ)) ^
        (2 * ⌊β * Real.log (Real.log (N n)) / Real.log ((1 + δ) / δ)⌋₊) ≤
          8 * Real.log (N n) ^ (2 * α)) : β ≤ α := by
  have ht : Tendsto (fun δ : ℝ => β * (Real.log ((1 - δ) / (2 * δ)) /
      Real.log ((1 + δ) / δ))) (𝓝[>] 0) (𝓝 β) := by
    simpa using tendsto_trace_log_ratio.const_mul β
  apply le_of_tendsto ht
  have hid : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  filter_upwards [hb, eventually_mem_nhdsWithin,
    hid.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))] with δ hb hpos hsmall
  exact trace_exponent_le_of_eventual_ratio_bound hN ⟨hpos, hsmall⟩ hb

end DynamicalCStarAlgebras
