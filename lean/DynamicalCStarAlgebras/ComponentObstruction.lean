import DynamicalCStarAlgebras.CoordinateTrace
noncomputable section
open Filter Classical
open scoped Topology
namespace DynamicalCStarAlgebras

/-- The component estimates rule out arbitrarily accurate self-adjoint approximants
with a uniform polynomial modulus of strictly larger exponent. -/
theorem component_approximation_obstruction {X : ℕ → Type*}
    [∀ n, Fintype (X n)] [∀ n, PseudoMetricSpace (X n)]
    (G : ∀ n, SimpleGraph (X n)) (hconn : ∀ n, (G n).Connected)
    (hdist : ∀ n (x y : X n), dist x y = ((G n).dist x y : ℝ))
    (k : ℕ) (hk : 2 ≤ k) (hdeg : ∀ n x, ((G n).neighborFinset x).card ≤ k)
    (hN : Tendsto (fun n => (Fintype.card (X n) : ℝ)) atTop atTop)
    (p : ∀ n, Operator (X n)) {α β C : ℝ} (hα : 0 < α) (hβ : α < β)
    (hp : ∀ᶠ n in atTop, IsStarProjection (p n) ∧
      Module.finrank ℂ (LinearMap.range (p n).toLinearMap) =
        ⌊(Fintype.card (X n) : ℝ) / Real.log (Fintype.card (X n)) ^ (2 * α)⌋₊ ∧
      ∀ A : Finset (X n), A.Nonempty →
        ‖coordinateProjection (A : Set (X n)) * p n‖ ≤ C * Real.sqrt
          (1 / Real.log (Fintype.card (X n)) ^ (2 * α) +
            (A.card : ℝ) / Fintype.card (X n) *
              Real.log (Real.exp 1 * Fintype.card (X n) / A.card)))
    (happrox : ∀ δ : ℝ, 0 < δ → ∃ (a : ∀ n, Operator (X n)) (D : ℝ), 0 < D ∧
      ∀ n, IsSelfAdjoint (a n) ∧ ‖a n - p n‖ ≤ δ ∧
        ∀ r : ℝ, 0 < r → quasiLocalModulus (a n) r ≤ D * r ^ (-β)) : False := by
  obtain ⟨β', hαβ', hβ'β⟩ := exists_between hβ
  have hgrowth := hN.eventually
    ((isLittleO_log_rpow_rpow_atTop (2 * α) (by norm_num : (0 : ℝ) < 1)).bound zero_lt_one)
  have hcontra : β' ≤ α := by
    apply trace_asymptotic_obstruction hN
    have hid : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    filter_upwards [eventually_mem_nhdsWithin,
      hid.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with δ hδ hδ1
    obtain ⟨a, D, hD, ha⟩ := happrox δ hδ
    have hdata : ∀ᶠ n in atTop, IsStarProjection (p n) ∧ ‖a n - p n‖ ≤ δ ∧
        (∀ r : ℝ, 0 < r → quasiLocalModulus (a n) r ≤ D * r ^ (-β)) ∧
        ∀ A : Finset (X n), A.Nonempty →
          ‖coordinateProjection (A : Set (X n)) * p n‖ ≤ C * Real.sqrt
            (1 / Real.log (Fintype.card (X n)) ^ (2 * α) +
              (A.card : ℝ) / Fintype.card (X n) *
                Real.log (Real.exp 1 * Fintype.card (X n) / A.card)) := by
      filter_upwards [hp] with n hn
      exact ⟨hn.1, (ha n).2.1, (ha n).2.2, hn.2.2⟩
    have hpow := eventually_nonmembership_power_bound G hconn hdist k hk hdeg hN a p
      hα (hα.trans hαβ') hβ'β hδ hD hdata
    filter_upwards [hpow, hp, hgrowth, hN.eventually (eventually_gt_atTop (1 : ℝ))]
      with n hn hp hg hlarge
    have hlog : 0 < Real.log (Fintype.card (X n)) := Real.log_pos hlarge
    have hsize : Real.log (Fintype.card (X n)) ^ (2 * α) ≤ Fintype.card (X n) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog.le _),
        Real.rpow_one, abs_of_nonneg (show (0 : ℝ) ≤ Fintype.card (X n) from Nat.cast_nonneg _), one_mul] using hg
    have hrank := floor_rank_lower_bound (Real.rpow_pos_of_pos hlog (2 * α)) hsize
    rw [← hp.2.1] at hrank
    exact coordinate_trace_power_ratio (a n) (p n) (ha n).1 hp.1 ⟨hδ, hδ1⟩
      (ha n).2.1 _ hlarge hrank hn
  exact (not_le_of_gt hαβ') hcontra

end DynamicalCStarAlgebras
