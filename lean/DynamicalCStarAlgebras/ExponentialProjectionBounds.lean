import DynamicalCStarAlgebras.PolynomialNonmembership

noncomputable section

namespace DynamicalCStarAlgebras

/-- A contraction supported on a subspace inherits its row-compression estimate. -/
lemma supported_compression_le {X : Type*} (a p : Operator X)
    (ha : ‖a‖ ≤ 1) (hpa : p * a = a) (A B : Set X) :
    ‖coordinateProjection A * a * coordinateProjection B‖ ≤
      ‖coordinateProjection A * p‖ := by
  calc
    _ ≤ ‖coordinateProjection A * a‖ := (norm_mul_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (coordinateProjection_norm_le B))
    _ = ‖(coordinateProjection A * p) * a‖ := by rw [mul_assoc, hpa]
    _ ≤ ‖coordinateProjection A * p‖ := (norm_mul_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) ha)

lemma supported_compression_le_min {X : Type*} (a p : Operator X)
    (hp : IsSelfAdjoint p) (ha : ‖a‖ ≤ 1) (hpa : p * a = a) (hap : a * p = a)
    (A B : Set X) :
    ‖coordinateProjection A * a * coordinateProjection B‖ ≤
      min ‖coordinateProjection A * p‖ ‖coordinateProjection B * p‖ := by
  apply le_min (supported_compression_le a p ha hpa A B)
  rw [← compression_star_norm a B A]
  apply supported_compression_le (star a) p ((norm_star a).trans_le ha)
  simpa only [star_mul, hp.star_eq] using congrArg star hap

/-- The choice of delta in the exponential-decay proof is admissible, including
the integer-rank observation needed for the upper endpoint one half. -/
lemma quarter_rank_delta_bounds {N κ r : ℝ} {m : ℕ}
    (hN : 0 < N) (hκ : 1 < κ) (hr : 0 ≤ r)
    (hm : N ^ (1 / 4 : ℝ) ≤ m)
    (hsize : 1 / N ≤ κ ^ (-r / 2)) (hsmall : κ ^ (-r / 2) ≤ 1 / 2) :
    0 < (1 : ℝ) / m ∧
      max (κ ^ (-r / 2)) (1 / (m : ℝ)) ≤ 1 / 2 ∧
      max (κ ^ (-r / 2)) (1 / (m : ℝ)) ≤ κ ^ (-r / 8) := by
  have hNtwo : 2 ≤ N := by
    have h := hsize.trans hsmall
    rw [div_le_iff₀ hN] at h
    linarith
  have hmone : (1 : ℝ) < m := lt_of_lt_of_le
    (Real.one_lt_rpow (by linarith) (by norm_num : (0 : ℝ) < 1 / 4)) hm
  have hmtwo : (2 : ℝ) ≤ m := by
    have h : 1 < m := by exact_mod_cast hmone
    exact_mod_cast h
  have hmpos : (0 : ℝ) < m := by linarith
  have hhalf : (1 : ℝ) / m ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hmpos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hquarter : κ ^ (r / 8) ≤ N ^ (1 / 4 : ℝ) := by
    have hbase : κ ^ (r / 2) ≤ N := by
      rw [show -r / 2 = -(r / 2) by ring, Real.rpow_neg (by linarith : 0 ≤ κ)] at hsize
      exact (one_div_le_one_div hN
        (Real.rpow_pos_of_pos (show 0 < κ by linarith) (r / 2))).mp (by
          simpa only [one_div] using hsize)
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith : 0 ≤ κ) _) hbase
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_mul (by linarith : 0 ≤ κ)] at h
    simpa only [show r / 2 * (1 / 4 : ℝ) = r / 8 by ring] using h
  have hinv : (1 : ℝ) / m ≤ κ ^ (-r / 8) := by
    rw [show -r / 8 = -(r / 8) by ring, Real.rpow_neg (by linarith : 0 ≤ κ)]
    simpa only [one_div] using one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos (show 0 < κ by linarith) (r / 8)) (hquarter.trans hm)
  exact ⟨by positivity, max_le hsmall hhalf, max_le
    (Real.rpow_le_rpow_of_exponent_le hκ.le (by linarith)) hinv⟩

/-- The finite-component estimate in Eq.UnifExpDecay. The good-subspace
estimate is used only at a value of delta in its stated closed interval. -/
theorem finite_good_projection_compression {X : Type*} [Fintype X]
    (a p : Operator X) (hp : IsSelfAdjoint p) (ha : ‖a‖ ≤ 1)
    (hpa : p * a = a) (hap : a * p = a)
    {C κ r : ℝ} {m : ℕ} (hC : 1 ≤ C) (hκ : 1 < κ) (hr : 0 ≤ r)
    (hm : (Fintype.card X : ℝ) ^ (1 / 4 : ℝ) ≤ m)
    (hgood : ∀ (S : Finset X) (δ : ℝ), 1 / (m : ℝ) ≤ δ → δ ≤ 1 / 2 →
      (S.card : ℝ) ≤ δ * Fintype.card X →
      ‖coordinateProjection (S : Set X) * p‖ ≤ C * Real.sqrt (δ * Real.log (1 / δ)))
    (A B : Finset X)
    (hsep : min ((A.card : ℝ) / Fintype.card X) ((B.card : ℝ) / Fintype.card X) ≤
      κ ^ (-r / 2)) :
    ‖coordinateProjection (A : Set X) * a * coordinateProjection (B : Set X)‖ ≤
      2 * C * κ ^ (-r / 24) := by
  classical
  have hκ0 : 0 < κ := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hout : 0 ≤ 2 * C * κ ^ (-r / 24) := by positivity
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · by_cases hsmall : κ ^ (-r / 2) ≤ 1 / 2
      · have hN : (0 : ℝ) < Fintype.card X := by
          exact_mod_cast (Fintype.card_pos_iff.mpr ⟨hA.choose⟩)
        have hAc : (1 : ℝ) ≤ A.card := by exact_mod_cast hA.card_pos
        have hBc : (1 : ℝ) ≤ B.card := by exact_mod_cast hB.card_pos
        have hsize : 1 / (Fintype.card X : ℝ) ≤ κ ^ (-r / 2) :=
          (le_min (div_le_div_of_nonneg_right hAc hN.le)
            (div_le_div_of_nonneg_right hBc hN.le)).trans hsep
        obtain ⟨hmi, hhalf, hdelta⟩ := quarter_rank_delta_bounds hN hκ hr hm hsize hsmall
        let δ := max (κ ^ (-r / 2)) (1 / (m : ℝ))
        have hδ : 0 < δ := hmi.trans_le (le_max_right _ _)
        have hscalar : C * Real.sqrt (δ * Real.log (1 / δ)) ≤
            2 * C * κ ^ (-r / 24) := by
          have hcub := Real.rpow_le_rpow hδ.le hdelta
            (by norm_num : (0 : ℝ) ≤ 1 / 3)
          rw [← Real.rpow_mul hκ0.le] at hcub
          have hcub' : δ ^ (1 / 3 : ℝ) ≤ κ ^ (-r / 24) := by
            simpa only [show -r / 8 * (1 / 3 : ℝ) = -r / 24 by ring] using hcub
          calc
            _ ≤ C * (2 * δ ^ (1 / 3 : ℝ)) :=
              mul_le_mul_of_nonneg_left (sqrt_entropy_le_two_cuberoot hδ) hC0
            _ ≤ C * (2 * κ ^ (-r / 24)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcub' (by norm_num)) hC0
            _ = _ := by ring
        have hmin := supported_compression_le_min a p hp ha hpa hap (A : Set X) (B : Set X)
        rcases (min_le_iff.mp hsep) with hleft | hright
        · exact (hmin.trans (min_le_left _ _)).trans ((hgood A δ (le_max_right _ _) hhalf
            ((div_le_iff₀ hN).mp (hleft.trans (le_max_left _ _)))).trans hscalar)
        · exact (hmin.trans (min_le_right _ _)).trans ((hgood B δ (le_max_right _ _) hhalf
            ((div_le_iff₀ hN).mp (hright.trans (le_max_left _ _)))).trans hscalar)
      · have hq : 1 / 2 < κ ^ (-r / 24) := (lt_of_not_ge hsmall).trans_le
          (Real.rpow_le_rpow_of_exponent_le hκ.le (by linarith))
        have hbound : 1 ≤ 2 * C * κ ^ (-r / 24) := by
          nlinarith [mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hκ0.le (-r / 24))]
        exact (compression_norm_le a _ _).trans (ha.trans hbound)
    · have hz : coordinateProjection (A : Set X) * a * coordinateProjection (B : Set X) = 0 :=
        compression_eq_zero_of_entries a _ _ (fun _ _ y hy => (hB ⟨y, hy⟩).elim)
      simpa only [hz, norm_zero] using hout
  · have hz : coordinateProjection (A : Set X) * a * coordinateProjection (B : Set X) = 0 :=
      compression_eq_zero_of_entries a _ _ (fun x hx _ _ => (hA ⟨x, hx⟩).elim)
    simpa only [hz, norm_zero] using hout

/-- A finite-component form of Eq.UnifExpDecay, with the source's exact constant
and exponent. No existence of good subspaces is assumed implicitly. -/
theorem finite_good_projection_modulus {X : Type*} [Fintype X] [PseudoMetricSpace X]
    (a p : Operator X) (hp : IsSelfAdjoint p) (ha : ‖a‖ ≤ 1)
    (hpa : p * a = a) (hap : a * p = a)
    {C κ : ℝ} {m : ℕ} (hC : 1 ≤ C) (hκ : 1 < κ)
    (hm : (Fintype.card X : ℝ) ^ (1 / 4 : ℝ) ≤ m)
    (hgood : ∀ (S : Finset X) (δ : ℝ), 1 / (m : ℝ) ≤ δ → δ ≤ 1 / 2 →
      (S.card : ℝ) ≤ δ * Fintype.card X →
      ‖coordinateProjection (S : Set X) * p‖ ≤ C * Real.sqrt (δ * Real.log (1 / δ)))
    (hsep : ∀ (A B : Finset X) (r : ℝ), 0 ≤ r →
      (∀ x ∈ A, ∀ y ∈ B, r ≤ dist x y) →
      min ((A.card : ℝ) / Fintype.card X) ((B.card : ℝ) / Fintype.card X) ≤ κ ^ (-r / 2))
    (r : ℝ) (hr : 0 ≤ r) :
    quasiLocalModulus a r ≤ 2 * C * κ ^ (-r / 24) := by
  classical
  apply (quasiLocalModulus_le_iff a r _).mpr
  intro A B hAB
  have h := finite_good_projection_compression a p hp ha hpa hap hC hκ hr hm hgood
    A.toFinset B.toFinset (hsep A.toFinset B.toFinset r hr
      (fun x hx y hy => hAB x (by simpa using hx) y (by simpa using hy)))
  simpa only [Set.coe_toFinset] using h

end DynamicalCStarAlgebras
