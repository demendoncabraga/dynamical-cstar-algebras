import DynamicalCStarAlgebras.HaarUnitaryMoments
import Mathlib.Data.Nat.Choose.Bounds

/-! The finite net and union-bound argument in Li--Zhang--Zhu,
Proposition 6.3, https://arxiv.org/html/2608.22439v2#S6.SS2.
The concentration estimate (6.6) is an explicit input to the final implication.
The conclusion retains the source's universal constant 32. The numerical union
bound uses a finite geometric majorant, so no infinite summation is needed. -/

noncomputable section
open Classical MeasureTheory
open scoped ENNReal
namespace DynamicalCStarAlgebras
lemma choose_le_exp_entropy {d k : ℕ} (hd : 0 < d) (hk : 0 < k) :
    (d.choose k : ℝ) ≤ Real.exp ((k : ℝ) * Real.log (Real.exp 1 * d / k)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hfac := Real.pow_div_factorial_le_exp (k : ℝ) hkR.le k
  calc
    (d.choose k : ℝ) ≤ (d : ℝ) ^ k / k.factorial := Nat.choose_le_pow_div k d
    _ = ((d : ℝ) / k) ^ k * ((k : ℝ) ^ k / k.factorial) := by
      rw [div_pow]
      field_simp
    _ ≤ ((d : ℝ) / k) ^ k * Real.exp k := mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = Real.exp ((k : ℝ) * Real.log (Real.exp 1 * d / k)) := by
      rw [mul_div_assoc, Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (div_pos hdR hkR)),
        Real.log_exp, mul_add, Real.exp_add, mul_one, Real.exp_nat_mul,
        Real.exp_log (div_pos hdR hkR), mul_comm]

lemma frame_log_entropy_ge_one {d k : ℝ} (hk : 0 < k) (hkd : k ≤ d) :
    1 ≤ Real.log (Real.exp 1 * d / k) := by
  have hd : 0 < d := hk.trans_le hkd
  apply (Real.le_log_iff_exp_le (by positivity)).mpr
  exact (le_div_iff₀ hk).mpr (mul_le_mul_of_nonneg_left hkd (Real.exp_pos 1).le)
lemma frame_net_union_term_le {d r k : ℕ} (hr : 0 < r) (hk : 0 < k) (hkd : k ≤ d) :
    (5 : ℝ) ^ (2 * r) * (d.choose k : ℝ) *
      (2 * Real.exp (-9 * ((r : ℝ) + k * Real.log (Real.exp 1 * d / k)))) ≤
        (1 / 2 : ℝ) ^ k := by
  have hd : 0 < d := hk.trans_le hkd
  have hL := frame_log_entropy_ge_one (d := (d : ℝ)) (by exact_mod_cast hk : (0 : ℝ) < k)
    (by exact_mod_cast hkd)
  have hlog5 : Real.log 5 ≤ 4 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hp : (5 : ℝ) ^ (2 * r) = Real.exp (2 * r * Real.log 5) := by
    rw [show (2 : ℝ) * r = ((2 * r : ℕ) : ℝ) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
  have hq : (1 / 2 : ℝ) ^ k = Real.exp (-(k : ℝ) * Real.log 2) := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp [inv_pow]
  rw [hp, hq]
  calc
    _ ≤ Real.exp (2 * r * Real.log 5) *
        Real.exp ((k : ℝ) * Real.log (Real.exp 1 * d / k)) *
          (2 * Real.exp (-9 * ((r : ℝ) + k * Real.log (Real.exp 1 * d / k)))) := by
      gcongr
      exact choose_le_exp_entropy hd hk
    _ = Real.exp (Real.log 2 + 2 * r * Real.log 5 +
        k * Real.log (Real.exp 1 * d / k) -
          9 * ((r : ℝ) + k * Real.log (Real.exp 1 * d / k))) := by
      simp only [neg_mul, Real.exp_sub, Real.exp_add, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    _ ≤ Real.exp (-(k : ℝ) * Real.log 2) := by
      apply Real.exp_le_exp.mpr
      have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) r) (sub_nonneg.mpr hlog5),
        mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (sub_nonneg.mpr hL),
        mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (sub_nonneg.mpr hlog2)]

lemma frame_geometric_sum_lt_one (d : ℕ) :
    (∑ k ∈ Finset.Icc 1 d, (1 / 2 : ℝ) ^ k) < 1 := by
  have hsum : (∑ k ∈ Finset.Icc 1 d, (1 / 2 : ℝ) ^ k) = 1 - (1 / 2 : ℝ) ^ d := by
    induction d with
    | zero => norm_num
    | succ d ih => rw [Finset.sum_Icc_succ_top (by omega), ih, pow_succ]; ring
  rw [hsum]
  have : 0 < (1 / 2 : ℝ) ^ d := by positivity
  linarith
lemma frame_threshold_le_thirtytwo {d r k : ℝ} (hd : 0 < d) (hr : 1 ≤ r)
    (hk : 0 < k) (hkd : k ≤ d) :
    2 * (Real.sqrt (k / d) + 12 / Real.sqrt (2 * d) +
      3 * Real.sqrt (r / d + k / d * Real.log (Real.exp 1 * d / k))) ≤
        32 * Real.sqrt (r / d + k / d * Real.log (Real.exp 1 * d / k)) := by
  have hL := frame_log_entropy_ge_one hk hkd
  have hr0 : 0 ≤ r := by linarith
  have hkr : k / d ≤ r / d + k / d * Real.log (Real.exp 1 * d / k) := by
    have hmul := mul_le_mul_of_nonneg_left hL (div_nonneg hk.le hd.le)
    linarith [div_nonneg hr0 hd.le]
  have hfirst := Real.sqrt_le_sqrt hkr
  have hsmall : 1 / (2 * d) ≤ r / d := by
    apply (div_le_div_iff₀ (by positivity) hd).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) hd.le]
  have hrS : r / d ≤ r / d + k / d * Real.log (Real.exp 1 * d / k) := by
    have : 0 ≤ k / d * Real.log (Real.exp 1 * d / k) := mul_nonneg
      (div_nonneg hk.le hd.le) (by linarith)
    linarith
  have hsecond := Real.sqrt_le_sqrt (hsmall.trans hrS)
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one] at hsecond
  simp only [div_eq_mul_inv, one_mul] at hfirst hsecond ⊢
  linarith

/-- Coordinate restriction as a bounded complex linear map. -/
def euclideanCoordinateRestrictionCLM {ι : Type*} [Fintype ι] (A : Finset ι) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ A where
  toFun := euclideanCoordinateRestriction A
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  cont := (PiLp.continuous_toLp 2 (fun _ : A => ℂ)).comp
    (continuous_pi fun i : A => PiLp.continuous_apply 2 (fun _ : ι => ℂ) (i : ι))
lemma euclideanCoordinateRestriction_norm_le {ι : Type*} [Fintype ι] (A : Finset ι)
    (z : EuclideanSpace ℂ ι) : ‖euclideanCoordinateRestriction A z‖ ≤ ‖z‖ := by
  have hsq : ‖euclideanCoordinateRestriction A z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [norm_sq_euclideanCoordinateRestriction, EuclideanSpace.norm_sq_eq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)
  nlinarith [norm_nonneg z, norm_nonneg (euclideanCoordinateRestriction A z)]

lemma measure_double_finset_union_le {Ω α β : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (I : Finset α) (J : Finset β) (bad : α → β → Set Ω)
    (q : ℝ≥0∞) (hbad : ∀ i ∈ I, ∀ j ∈ J, μ (bad i j) ≤ q) :
    μ (⋃ i ∈ I, ⋃ j ∈ J, bad i j) ≤ I.card * J.card * q := by
  calc
    _ ≤ ∑ i ∈ I, μ (⋃ j ∈ J, bad i j) := measure_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ I, ∑ j ∈ J, μ (bad i j) := Finset.sum_le_sum fun _ _ =>
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ I, ∑ _j ∈ J, q := Finset.sum_le_sum fun i hi =>
      Finset.sum_le_sum fun j hj => hbad i hi j hj
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- The finite net and union-bound portion of Proposition 6.3, with its
concentration estimate (6.6) kept as an explicit premise. -/
theorem exists_frame_bound_of_coordinate_tails {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d r : ℕ} (hr : 0 < r) (hrd : r ≤ d)
    (U : Ω → (EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d)))
    (htail : ∀ (A : Finset (Fin d)), A.Nonempty →
      ∀ (v : EuclideanSpace ℂ (Fin r)), ‖v‖ = 1 → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      μ {ω | Real.sqrt ((A.card : ℝ) / d) + 12 / Real.sqrt (2 * d) + t <
        ‖euclideanCoordinateRestriction A (U ω v)‖} ≤
          ENNReal.ofReal (2 * Real.exp (-(d : ℝ) * t ^ 2))) :
    ∃ ω, ∀ (A : Finset (Fin d)), A.Nonempty →
      ‖(euclideanCoordinateRestrictionCLM A).comp (U ω).toContinuousLinearMap‖ ≤
        32 * Real.sqrt ((r : ℝ) / d + (A.card : ℝ) / d *
          Real.log (Real.exp 1 * d / A.card)) := by
  obtain ⟨s, hs, hcard, hnet⟩ := exists_half_net_sphere_complex
    (E := EuclideanSpace ℂ (Fin r))
  have hcard' : s.card ≤ 5 ^ (2 * r) := by simpa using hcard
  have hd : 0 < d := hr.trans_le hrd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let S (k : ℕ) : ℝ := Real.sqrt ((r : ℝ) / d + (k : ℝ) / d *
    Real.log (Real.exp 1 * d / k))
  let M (k : ℕ) : ℝ := Real.sqrt ((k : ℝ) / d) + 12 / Real.sqrt (2 * d) + 3 * S k
  let bad (k : ℕ) (A : Finset (Fin d)) (v : EuclideanSpace ℂ (Fin r)) : Set Ω :=
    {ω | M k < ‖euclideanCoordinateRestriction A (U ω v)‖}
  have hbad : ∀ k ∈ Finset.Icc 1 d, ∀ A ∈ Finset.univ.powersetCard k,
      ∀ v ∈ s, μ (bad k A v) ≤ ENNReal.ofReal
        (2 * Real.exp (-9 * ((r : ℝ) + k * Real.log (Real.exp 1 * d / k)))) := by
    intro k hk A hA v hv
    have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
    have hkd : k ≤ d := (Finset.mem_Icc.mp hk).2
    have hAk : A.card = k := (Finset.mem_powersetCard.mp hA).2
    have hAne : A.Nonempty := Finset.card_pos.mp (hAk.symm ▸ hkpos)
    have hL := frame_log_entropy_ge_one (d := (d : ℝ))
      (by exact_mod_cast hkpos : (0 : ℝ) < k) (by exact_mod_cast hkd)
    have hSbase : 0 ≤ (r : ℝ) / d + (k : ℝ) / d *
        Real.log (Real.exp 1 * d / k) := by positivity
    by_cases ht : 3 * S k ≤ 1
    · have hh := htail A hAne v (hs v hv) (3 * S k) (by dsimp [S]; positivity) ht
      rw [hAk] at hh
      have hsq : (d : ℝ) * (3 * S k) ^ 2 =
          9 * ((r : ℝ) + k * Real.log (Real.exp 1 * d / k)) := by
        dsimp [S]
        rw [mul_pow, Real.sq_sqrt hSbase]
        field_simp
        ring
      simpa only [bad, M, neg_mul, hsq] using hh
    · have hempty : bad k A v = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro ω hω
        have hn := euclideanCoordinateRestriction_norm_le A (U ω v)
        rw [(U ω).norm_map, hs v hv] at hn
        have hM : 1 < M k := by
          dsimp [M]
          have : 0 ≤ 12 / Real.sqrt (2 * (d : ℝ)) := by positivity
          have := Real.sqrt_nonneg ((k : ℝ) / d)
          linarith
        exact (not_lt_of_ge (hn.trans hM.le)) hω
      simp [hempty]
  let B (k : ℕ) : Set Ω := ⋃ A ∈ Finset.univ.powersetCard k, ⋃ v ∈ s, bad k A v
  have hB : ∀ k ∈ Finset.Icc 1 d, μ (B k) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    intro k hk
    let q : ℝ := 2 * Real.exp (-9 * ((r : ℝ) + k * Real.log (Real.exp 1 * d / k)))
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hbound := measure_double_finset_union_le μ (Finset.univ.powersetCard k) s
      (bad k) (ENNReal.ofReal q) (hbad k hk)
    simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at hbound
    calc
      μ (B k) ≤ (d.choose k : ℝ≥0∞) * s.card * ENNReal.ofReal q := hbound
      _ = ENNReal.ofReal ((s.card : ℝ) * (d.choose k : ℝ) * q) := by
        simp [ENNReal.ofReal_mul, hq, mul_comm, mul_left_comm]
      _ ≤ ENNReal.ofReal ((5 : ℝ) ^ (2 * r) * (d.choose k : ℝ) * q) := by
        apply ENNReal.ofReal_le_ofReal
        gcongr
        exact_mod_cast hcard'
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := ENNReal.ofReal_le_ofReal
        (frame_net_union_term_le hr (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2)
  have htotal : μ (⋃ k ∈ Finset.Icc 1 d, B k) < 1 := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 d, μ (B k) := measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.Icc 1 d, ENNReal.ofReal ((1 / 2 : ℝ) ^ k) :=
        Finset.sum_le_sum hB
      _ = ENNReal.ofReal (∑ k ∈ Finset.Icc 1 d, (1 / 2 : ℝ) ^ k) :=
        (ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)).symm
      _ < 1 := ENNReal.ofReal_lt_one.mpr (frame_geometric_sum_lt_one d)
  have hnot : (⋃ k ∈ Finset.Icc 1 d, B k) ≠ Set.univ := by
    intro h
    rw [h, measure_univ] at htotal
    exact (lt_irrefl _) htotal
  obtain ⟨ω, hω⟩ := Set.nonempty_compl.mpr hnot
  refine ⟨ω, ?_⟩
  intro A hA
  have hAc : A.card ≤ d := by simpa using Finset.card_le_univ A
  have hAk : A.card ∈ Finset.Icc 1 d := Finset.mem_Icc.mpr ⟨hA.card_pos, hAc⟩
  have hbound : ∀ v ∈ s, ‖euclideanCoordinateRestriction A (U ω v)‖ ≤ M A.card := by
    intro v hv
    apply le_of_not_gt
    intro h
    apply hω
    exact Set.mem_iUnion.mpr ⟨A.card, Set.mem_iUnion.mpr ⟨hAk,
      Set.mem_iUnion.mpr ⟨A, Set.mem_iUnion.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩,
          Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hv, h⟩⟩⟩⟩⟩⟩
  have hop := opNorm_le_two_of_half_net s hnet
    ((euclideanCoordinateRestrictionCLM A).comp (U ω).toContinuousLinearMap)
    (show 0 ≤ M A.card by dsimp [M, S]; positivity) hbound
  exact hop.trans (frame_threshold_le_thirtytwo hdR (by exact_mod_cast hr)
    (by exact_mod_cast hA.card_pos) (by exact_mod_cast hAc))

end DynamicalCStarAlgebras
