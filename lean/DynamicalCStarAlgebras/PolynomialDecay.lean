import DynamicalCStarAlgebras.DecayAlgebras

noncomputable section

namespace DynamicalCStarAlgebras

open Filter

universe u

/-- The exact positive-radius bound in Definition Defi.QLalpha. -/
def HasPolynomialDecay {X : Type u} [PseudoMetricSpace X] (α : ℝ) (a : Operator X) : Prop :=
  ∃ M : ℝ, 0 < M ∧ ∀ r : ℝ, 0 < r → quasiLocalModulus a r ≤ M * r ^ (-α)

def polynomialQuasiLocal {X : Type u} [PseudoMetricSpace X] (α : ℝ) : Set (Operator X) :=
  closure {a | HasPolynomialDecay α a}

theorem rpow_half_neg (r α : ℝ) (hr : 0 ≤ r) :
    (r / 2) ^ (-α) = (2 : ℝ) ^ α * r ^ (-α) := by
  rw [Real.div_rpow hr (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [div_inv_eq_mul, mul_comm]

theorem HasPolynomialDecay.star {X : Type u} [PseudoMetricSpace X] {α : ℝ}
    {a : Operator X} (ha : HasPolynomialDecay α a) : HasPolynomialDecay α (star a) := by
  simpa only [HasPolynomialDecay, quasiLocalModulus_star] using ha

theorem HasPolynomialDecay.add {X : Type u} [PseudoMetricSpace X] {α : ℝ}
    {a b : Operator X} (ha : HasPolynomialDecay α a) (hb : HasPolynomialDecay α b) :
    HasPolynomialDecay α (a + b) :=
  ha.elim fun M hM => hb.elim fun N hN =>
    ⟨M + N, add_pos hM.1 hN.1, fun r hr =>
      ((quasiLocalModulus_add_le a b r).trans (add_le_add (hM.2 r hr) (hN.2 r hr))).trans_eq
        (add_mul M N (r ^ (-α))).symm⟩

theorem HasPolynomialDecay.mul {X : Type u} [PseudoMetricSpace X] {α : ℝ}
    {a b : Operator X} (ha : HasPolynomialDecay α a) (hb : HasPolynomialDecay α b) :
    HasPolynomialDecay α (a * b) := by
  obtain ⟨M, hM, haM⟩ := ha
  obtain ⟨N, hN, hbN⟩ := hb
  refine ⟨(M * ‖b‖ + ‖a‖ * N + 1) * (2 : ℝ) ^ α, by positivity, fun r hr => ?_⟩
  have hp := (quasiLocalModulus_mul_le a b (r / 2) (r / 2)).trans (add_le_add
    (mul_le_mul_of_nonneg_right (haM (r / 2) (half_pos hr)) (norm_nonneg b))
    (mul_le_mul_of_nonneg_left (hbN (r / 2) (half_pos hr)) (norm_nonneg a)))
  rw [add_halves, rpow_half_neg r α hr.le] at hp
  nlinarith [mul_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) α)
    (Real.rpow_pos_of_pos hr (-α))]

/-- A large-radius polynomial estimate extends to all positive radii using the operator norm. -/
theorem hasPolynomialDecay_of_eventually {X : Type u} [PseudoMetricSpace X]
    {α M : ℝ} (hα : 0 ≤ α) (hM : 0 < M) (a : Operator X)
    (ha : ∀ᶠ r in atTop, quasiLocalModulus a r ≤ M * r ^ (-α)) :
    HasPolynomialDecay α a := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp ha
  have hS : 0 < max R 1 := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  refine ⟨max M ((‖a‖ + 1) * (max R 1) ^ α), lt_of_lt_of_le hM (le_max_left _ _),
    fun r hr => ?_⟩
  by_cases hRr : R ≤ r
  · exact (hR r hRr).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hr.le _))
  · have hp : (max R 1) ^ (-α) ≤ r ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos hr ((le_of_not_ge hRr).trans (le_max_left R 1))
        (neg_nonpos.mpr hα)
    have he : ((‖a‖ + 1) * (max R 1) ^ α) * (max R 1) ^ (-α) = ‖a‖ + 1 := by
      rw [mul_assoc, ← Real.rpow_add hS, add_neg_cancel, Real.rpow_zero, mul_one]
    exact (quasiLocalModulus_le_norm a r).trans ((le_add_of_nonneg_right zero_le_one).trans
      (he.symm.trans_le (mul_le_mul (le_max_right _ _) hp (Real.rpow_nonneg hS.le _)
        ((hM.le).trans (le_max_left _ _)))))

theorem HasExponentialDecay.hasPolynomialDecay {X : Type u} [PseudoMetricSpace X]
    {a : Operator X} (ha : HasExponentialDecay a) {α : ℝ} (hα : 0 ≤ α) :
    HasPolynomialDecay α a := by
  obtain ⟨c, hc, M, hM, haM⟩ := ha
  refine hasPolynomialDecay_of_eventually hα hM a ?_
  filter_upwards [(isLittleO_exp_neg_mul_rpow_atTop hc (-α)).bound zero_lt_one,
    eventually_ge_atTop (0 : ℝ)] with r hb hr
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (Real.rpow_nonneg hr _), one_mul] at hb
  exact (haM r hr).trans (mul_le_mul_of_nonneg_left hb hM.le)

theorem HasPolynomialDecay.of_le {X : Type u} [PseudoMetricSpace X]
    {a : Operator X} {α β : ℝ} (ha : HasPolynomialDecay β a) (hα : 0 ≤ α) (hαβ : α ≤ β) :
    HasPolynomialDecay α a := by
  obtain ⟨M, hM, haM⟩ := ha
  exact hasPolynomialDecay_of_eventually hα hM a
    ((eventually_ge_atTop (1 : ℝ)).mono fun r hr =>
      (haM r (zero_lt_one.trans_le hr)).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hr (neg_le_neg hαβ)) hM.le))

theorem HasPolynomialDecay.isQuasiLocal {X : Type u} [PseudoMetricSpace X]
    {a : Operator X} {α : ℝ} (ha : HasPolynomialDecay α a) (hα : 0 < α) :
    IsQuasiLocal (CoarseStructure.ofPseudoMetric X) a := by
  obtain ⟨M, _hM, haM⟩ := ha
  have ht : Tendsto (fun r : ℝ => M * r ^ (-α)) atTop (nhds 0) := by
    simpa only [mul_zero] using! (tendsto_rpow_neg_atTop hα).const_mul M
  exact (isQuasiLocal_iff_modulus_tendsto a).mpr (squeeze_zero'
    (Eventually.of_forall (quasiLocalModulus_nonneg a))
    ((eventually_gt_atTop 0).mono fun r hr => haM r hr) ht)

def polynomialDecayStarSubalgebra {X : Type u} [PseudoMetricSpace X]
    (α : ℝ) (hα : 0 < α) : StarSubalgebra ℂ (Operator X) where
  carrier := {a | HasPolynomialDecay α a}
  zero_mem' := by simpa only [map_zero] using!
    (hasFinitePropagation_algebraMap (X := X) 0).hasExponentialDecay.hasPolynomialDecay hα.le
  one_mem' := by simpa only [map_one] using!
    (hasFinitePropagation_algebraMap (X := X) 1).hasExponentialDecay.hasPolynomialDecay hα.le
  add_mem' := HasPolynomialDecay.add
  mul_mem' := HasPolynomialDecay.mul
  star_mem' := HasPolynomialDecay.star
  algebraMap_mem' z := (hasFinitePropagation_algebraMap z).hasExponentialDecay.hasPolynomialDecay hα.le

def polynomialQuasiLocalStarSubalgebra {X : Type u} [PseudoMetricSpace X]
    (α : ℝ) (hα : 0 < α) : StarSubalgebra ℂ (Operator X) :=
  (polynomialDecayStarSubalgebra α hα).topologicalClosure

theorem polynomialQuasiLocal_algebra {X : Type u} [PseudoMetricSpace X]
    (α : ℝ) (hα : 0 < α) :
    (polynomialQuasiLocalStarSubalgebra (X := X) α hα : Set (Operator X)) = polynomialQuasiLocal α ∧
      IsClosed (polynomialQuasiLocalStarSubalgebra (X := X) α hα : Set (Operator X)) :=
  ⟨rfl, (polynomialDecayStarSubalgebra α hα).isClosed_topologicalClosure⟩

theorem exponentialQuasiLocal_subset_polynomialQuasiLocal {X : Type u} [PseudoMetricSpace X]
    {α : ℝ} (hα : 0 ≤ α) :
    (exponentialQuasiLocal : Set (Operator X)) ⊆ polynomialQuasiLocal α :=
  closure_mono fun _ ha => ha.hasPolynomialDecay hα

theorem polynomialQuasiLocal_antitone {X : Type u} [PseudoMetricSpace X]
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) :
    (polynomialQuasiLocal β : Set (Operator X)) ⊆ polynomialQuasiLocal α :=
  closure_mono fun _ ha => ha.of_le hα hαβ

theorem polynomialQuasiLocal_subset_quasiLocal {X : Type u} [PseudoMetricSpace X]
    {α : ℝ} (hα : 0 < α) :
    polynomialQuasiLocal α ⊆ quasiLocal (CoarseStructure.ofPseudoMetric X) :=
  closure_minimal (fun _ ha => ha.isQuasiLocal hα) (isClosed_quasiLocal _)

/-- The complete Section 5 decay-algebra inclusion chain. -/
theorem decayAlgebra_inclusions {X : Type u} [PseudoMetricSpace X]
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    uniformRoe (CoarseStructure.ofPseudoMetric X) ⊆ exponentialQuasiLocal ∧
      (exponentialQuasiLocal : Set (Operator X)) ⊆ polynomialQuasiLocal β ∧
      (polynomialQuasiLocal β : Set (Operator X)) ⊆ polynomialQuasiLocal α ∧
      polynomialQuasiLocal α ⊆ quasiLocal (CoarseStructure.ofPseudoMetric X) :=
  ⟨uniformRoe_subset_exponentialQuasiLocal,
    exponentialQuasiLocal_subset_polynomialQuasiLocal (hα.trans hαβ).le,
    polynomialQuasiLocal_antitone hα.le hαβ.le, polynomialQuasiLocal_subset_quasiLocal hα⟩

end DynamicalCStarAlgebras
