import DynamicalCStarAlgebras.SmallCompressions

noncomputable section
open Filter Classical
namespace DynamicalCStarAlgebras

/-- The geometric and analytic estimates together give the uniform basis-vector
bound at the chosen powers in the nonmembership proof. -/
theorem eventually_nonmembership_power_bound {X : ℕ → Type*}
    [∀ n, Fintype (X n)] [∀ n, PseudoMetricSpace (X n)]
    (G : ∀ n, SimpleGraph (X n)) (hconn : ∀ n, (G n).Connected)
    (hdist : ∀ n (x y : X n), dist x y = ((G n).dist x y : ℝ))
    (k : ℕ) (hk : 2 ≤ k) (hdeg : ∀ n x, ((G n).neighborFinset x).card ≤ k)
    (hN : Tendsto (fun n => (Fintype.card (X n) : ℝ)) atTop atTop)
    (a p : ∀ n, Operator (X n)) {α β β' δ C D : ℝ}
    (hα : 0 < α) (hβ' : 0 < β') (hβ : β' < β) (hδ : 0 < δ)
    (hD : 0 < D)
    (hdata : ∀ᶠ n in atTop, IsStarProjection (p n) ∧ ‖a n - p n‖ ≤ δ ∧
      (∀ r : ℝ, 0 < r → quasiLocalModulus (a n) r ≤ D * r ^ (-β)) ∧
      ∀ A : Finset (X n), A.Nonempty →
        ‖coordinateProjection (A : Set (X n)) * p n‖ ≤ C * Real.sqrt
          (1 / Real.log (Fintype.card (X n)) ^ (2 * α) +
            (A.card : ℝ) / Fintype.card (X n) *
              Real.log (Real.exp 1 * Fintype.card (X n) / A.card))) :
    ∀ᶠ n in atTop,
      let m := ⌊β' * Real.log (Real.log (Fintype.card (X n))) /
        Real.log ((1 + δ) / δ)⌋₊
      ∀ x : X n, ‖(a n ^ m) (delta x)‖ ≤ 2 * (2 * δ) ^ m := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hradii := eventually_nonmembership_radius_admissible hN hδ hD hβ' hβ hk1
  have hmajor := eventually_small_compression_majorant hN hα hδ C k
  filter_upwards [hdata, hradii, hmajor, hN.eventually (eventually_gt_atTop (1 : ℝ))]
    with n hn hr hm hlarge
  dsimp only at hr ⊢
  intro x
  let m := ⌊β' * Real.log (Real.log (Fintype.card (X n))) / Real.log ((1 + δ) / δ)⌋₊
  let r := ((m : ℝ) * ((1 + δ) / δ) ^ m * D) ^ (1 / β)
  let A := Finset.univ.filter fun y : X n => ((G n).dist x y : ℝ) ≤ m * r
  have hA : A.Nonempty := by
    refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simp only [SimpleGraph.dist_self, Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hr.2.1.le
  have hset : (A : Set (X n)) = Metric.closedBall x (m * r) := by
    ext y
    simp only [A, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Metric.mem_closedBall, hdist, SimpleGraph.dist_comm (u := y) (v := x)]
  have hcard : (A.card : ℝ) ≤ k * Real.sqrt (Fintype.card (X n)) :=
    graph_ball_card_le_sqrt (G n) (hconn n) k hk (hdeg n) x
      (mul_nonneg (Nat.cast_nonneg _) hr.2.1.le) (zero_lt_one.trans hlarge) hr.2.2
  have hcomp := (small_projection_compression_bound (p n) hn.1 A hA hlarge hcard
    (hn.2.2.2 A hA)).trans hm
  rw [hset] at hcomp
  exact norm_pow_delta_le_two_delta (a n) (p n) hn.1 hδ hD (hβ'.trans hβ)
    hn.2.1 hn.2.2.1 m hr.1 x hcomp

end DynamicalCStarAlgebras
