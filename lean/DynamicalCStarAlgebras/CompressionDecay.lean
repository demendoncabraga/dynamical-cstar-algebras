import DynamicalCStarAlgebras.RadiusChoice

noncomputable section
namespace DynamicalCStarAlgebras

/-- The small-compression and polynomial-modulus estimates give the power bound
used immediately before the trace comparison in the nonmembership proof. -/
theorem norm_pow_delta_le_two_delta {X : Type*} [PseudoMetricSpace X]
    (a p : Operator X) (hp : IsStarProjection p) {δ C β : ℝ}
    (hδ : 0 < δ) (hC : 0 < C) (hβ : 0 < β) (hap : ‖a - p‖ ≤ δ)
    (hmod : ∀ r : ℝ, 0 < r → quasiLocalModulus a r ≤ C * r ^ (-β))
    (m : ℕ) (hm : 0 < m) (x : X)
    (hcomp : let r := ((m : ℝ) * ((1 + δ) / δ) ^ m * C) ^ (1 / β)
      ‖coordinateProjection (Metric.closedBall x (m * r)) * p *
        coordinateProjection (Metric.closedBall x (m * r))‖ ≤ δ) :
    ‖(a ^ m) (delta x)‖ ≤ 2 * (2 * δ) ^ m := by
  let r := ((m : ℝ) * ((1 + δ) / δ) ^ m * C) ^ (1 / β)
  let A := Metric.closedBall x (m * r)
  have hr : 0 < r := Real.rpow_pos_of_pos (by positivity) _
  have hnorm : ‖a‖ ≤ 1 + δ := by
    have h := norm_le_norm_add_norm_sub p a
    have hp1 := hp.norm_le
    rw [norm_sub_rev] at h
    linarith
  have hca : ‖coordinateProjection A * a * coordinateProjection A‖ ≤ 2 * δ := by
    have h := norm_le_norm_add_norm_sub (coordinateProjection A * p * coordinateProjection A)
      (coordinateProjection A * a * coordinateProjection A)
    have he := compression_sub_norm_le a p A A
    rw [norm_sub_rev] at h
    linarith
  have hb := norm_pow_delta_le_compression a x hr m
  have he := nonmembership_radius_error_le hδ hC hβ m hm
  have hu : (m : ℝ) * ‖a‖ ^ (m - 1) * quasiLocalModulus a r ≤ δ ^ m := by
    calc
      _ ≤ (m : ℝ) * (1 + δ) ^ (m - 1) * (C * r ^ (-β)) := by
        gcongr
        · exact quasiLocalModulus_nonneg a r
        · exact hmod r hr
      _ ≤ δ ^ m := by simpa only [r, mul_assoc] using he
  have hpw : δ ^ m ≤ (2 * δ) ^ m := pow_le_pow_left₀ hδ.le (by linarith) _
  have hca' := pow_le_pow_left₀ (norm_nonneg _) hca m
  linarith

end DynamicalCStarAlgebras
