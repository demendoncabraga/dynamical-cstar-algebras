import DynamicalCStarAlgebras.TraceAsymptotics

noncomputable section
open Filter
open scoped Topology
namespace DynamicalCStarAlgebras

lemma floor_log_power_upper {c t β : ℝ} (hc : 1 < c) (ht : 1 ≤ t) (hβ : 0 ≤ β) :
    c ^ ⌊β * Real.log t / Real.log c⌋₊ ≤ t ^ β := by
  have hn := Nat.floor_le (div_nonneg (mul_nonneg hβ (Real.log_nonneg ht))
    (Real.log_pos hc).le)
  have he : (⌊β * Real.log t / Real.log c⌋₊ : ℝ) * Real.log c ≤ Real.log t * β := by
    have h := (le_div_iff₀ (Real.log_pos hc)).mp hn
    nlinarith only [h]
  rw [← Real.exp_log (zero_lt_one.trans hc), ← Real.exp_nat_mul,
    Real.rpow_def_of_pos (zero_lt_one.trans_le ht)]
  simpa only [Real.log_exp] using Real.exp_le_exp.mpr he

lemma radius_product_bound {c t C K s q : ℝ} (m : ℕ)
    (hc : 0 ≤ c) (ht : 1 < t) (hC : 0 < C) (hK : 0 < K) (hq : 0 ≤ q)
    (hm : (m : ℝ) ≤ K * Real.log t) (hp : c ^ m ≤ t ^ s) :
    (m : ℝ) * ((m : ℝ) * c ^ m * C) ^ q ≤
      C ^ q * K ^ (1 + q) * Real.log t ^ (1 + q) * t ^ (s * q) := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hl : 0 < Real.log t := Real.log_pos ht
  calc
    _ ≤ (K * Real.log t) * ((K * Real.log t) * t ^ s * C) ^ q := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ K * Real.log t * t ^ s) hC.le,
        Real.mul_rpow (by positivity : 0 ≤ K * Real.log t) (Real.rpow_nonneg ht0.le _),
        Real.mul_rpow hK.le hl.le, ← Real.rpow_mul ht0.le,
        Real.rpow_add hK 1 q, Real.rpow_add hl 1 q]
      simp only [Real.rpow_one]
      ring

lemma eventually_radius_product_le {c C β β' D : ℝ} (hc : 1 < c)
    (hC : 0 < C) (hβ' : 0 < β') (hβ : β' < β) (hD : 0 < D) :
    ∀ᶠ t : ℝ in atTop,
      let m := ⌊β' * Real.log t / Real.log c⌋₊
      (m : ℝ) * ((m : ℝ) * c ^ m * C) ^ (1 / β) ≤ D * t := by
  let K := β' / Real.log c
  let M := C ^ (1 / β) * K ^ (1 + 1 / β)
  have hβ0 : 0 < β := hβ'.trans hβ
  have hK : 0 < K := div_pos hβ' (Real.log_pos hc)
  have hM : 0 < M := mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hK _)
  have hs : 0 < 1 - β' * (1 / β) := by
    have := (div_lt_one hβ0).mpr hβ
    simpa only [div_eq_mul_inv, one_mul] using sub_pos.mpr this
  have ho := (isLittleO_log_rpow_rpow_atTop (1 + 1 / β) hs).bound (div_pos hD hM)
  filter_upwards [ho, eventually_gt_atTop (1 : ℝ)] with t hbound ht
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hl : 0 < Real.log t := Real.log_pos ht
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hl.le _),
    abs_of_nonneg (Real.rpow_nonneg ht0.le _)] at hbound
  have hm : (⌊β' * Real.log t / Real.log c⌋₊ : ℝ) ≤ K * Real.log t := by
    simpa only [K, div_mul_eq_mul_div] using
      Nat.floor_le (div_nonneg (mul_nonneg hβ'.le hl.le) (Real.log_pos hc).le)
  have hp := floor_log_power_upper hc ht.le hβ'.le
  have hh := radius_product_bound _ (zero_lt_one.trans hc).le ht hC hK
    (by positivity : 0 ≤ 1 / β) hm hp
  change _ ≤ M * Real.log t ^ (1 + 1 / β) * t ^ (β' * (1 / β)) at hh
  refine hh.trans ?_
  calc
    _ ≤ M * (D / M * t ^ (1 - β' * (1 / β))) * t ^ (β' * (1 / β)) := by gcongr
    _ = D * t := by
      rw [← mul_assoc M, mul_div_cancel₀ D hM.ne']
      rw [mul_assoc, ← Real.rpow_add ht0, sub_add_cancel, Real.rpow_one]

/-- The source radii and integer powers eventually satisfy the ball-size constraint. -/
theorem eventually_nonmembership_radius_admissible {N : ℕ → ℝ}
    {δ C β β' k : ℝ} (hN : Tendsto N atTop atTop) (hδ : 0 < δ) (hC : 0 < C)
    (hβ' : 0 < β') (hβ : β' < β) (hk : 1 < k) :
    ∀ᶠ n in atTop,
      let m := ⌊β' * Real.log (Real.log (N n)) / Real.log ((1 + δ) / δ)⌋₊
      let r := ((m : ℝ) * ((1 + δ) / δ) ^ m * C) ^ (1 / β)
      0 < m ∧ 0 < r ∧ (m : ℝ) * r ≤ Real.log (N n) / (2 * Real.log k) := by
  have hc : 1 < (1 + δ) / δ := (lt_div_iff₀ hδ).mpr (by linarith)
  have hx : Tendsto (fun n => Real.log (N n)) atTop atTop := Real.tendsto_log_atTop.comp hN
  have hlogk : 0 < Real.log k := Real.log_pos hk
  have hp := hx.eventually (eventually_radius_product_le hc hC hβ' hβ
    (by positivity : 0 < 1 / (2 * Real.log k)))
  have hm := (((Real.tendsto_log_atTop.comp hx).const_mul_atTop hβ').atTop_div_const
    (Real.log_pos hc)).eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hp, hm] with n hn hm
  dsimp only
  have hm' : 0 < ⌊β' * Real.log (Real.log (N n)) / Real.log ((1 + δ) / δ)⌋₊ :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one ((Nat.one_le_floor_iff _).mpr hm)
  refine ⟨hm', Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  simpa only [one_div_mul_eq_div] using hn

/-- The radius in Eq.Choice.of.rn.1 makes the compression error at most `delta^m`. -/
theorem nonmembership_radius_error_le {δ C β : ℝ} (hδ : 0 < δ) (hC : 0 < C)
    (hβ : 0 < β) (m : ℕ) (hm : 0 < m) :
    (m : ℝ) * (1 + δ) ^ (m - 1) * C *
      (((m : ℝ) * ((1 + δ) / δ) ^ m * C) ^ (1 / β)) ^ (-β) ≤ δ ^ m := by
  have hc : 0 < (1 + δ) / δ := div_pos (by linarith) hδ
  have hbase : 0 < (m : ℝ) * ((1 + δ) / δ) ^ m * C := by positivity
  rw [← Real.rpow_mul hbase.le, show 1 / β * -β = (-1 : ℝ) by field_simp,
    Real.rpow_neg_one]
  calc
    _ ≤ (m : ℝ) * (1 + δ) ^ m * C *
        ((m : ℝ) * ((1 + δ) / δ) ^ m * C)⁻¹ := by
      gcongr
      · linarith
      · exact Nat.sub_le m 1
    _ = δ ^ m := by
      rw [div_pow]
      field_simp

end DynamicalCStarAlgebras
