import DynamicalCStarAlgebras.QuasiLocalAlgebra

noncomputable section

namespace DynamicalCStarAlgebras

open Filter

universe u

theorem quasiLocalModulus_le_norm {X : Type u} [PseudoMetricSpace X]
    (a : Operator X) (r : ℝ) : quasiLocalModulus a r ≤ ‖a‖ :=
  (quasiLocalModulus_le_iff _ _ _).mpr fun A B _ => compression_norm_le a A B

theorem quasiLocalModulus_smul_le {X : Type u} [PseudoMetricSpace X]
    (c : ℂ) (a : Operator X) (r : ℝ) :
    quasiLocalModulus (c • a) r ≤ ‖c‖ * quasiLocalModulus a r := by
  refine (quasiLocalModulus_le_iff _ _ _).mpr fun A B hAB => ?_
  rw [mul_smul_comm, smul_mul_assoc, norm_smul]
  exact mul_le_mul_of_nonneg_left ((quasiLocalModulus_le_iff a r _).mp le_rfl A B hAB)
    (norm_nonneg c)

/-- The pointwise exponential bound in Definition Defi.QL.exp. -/
def HasExponentialDecay {X : Type u} [PseudoMetricSpace X] (a : Operator X) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ M : ℝ, 0 < M ∧
    ∀ r : ℝ, 0 ≤ r → quasiLocalModulus a r ≤ M * Real.exp (-c * r)

/-- The norm closure defining QL_exp. -/
def exponentialQuasiLocal {X : Type u} [PseudoMetricSpace X] : Set (Operator X) :=
  closure {a | HasExponentialDecay a}

theorem exp_neg_mul_antitone {c d r : ℝ} (hcd : c ≤ d) (hr : 0 ≤ r) :
    Real.exp (-d * r) ≤ Real.exp (-c * r) :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hcd) hr)

theorem HasExponentialDecay.star {X : Type u} [PseudoMetricSpace X] {a : Operator X}
    (ha : HasExponentialDecay a) : HasExponentialDecay (star a) := by
  simpa only [HasExponentialDecay, quasiLocalModulus_star] using ha

theorem HasExponentialDecay.add {X : Type u} [PseudoMetricSpace X] {a b : Operator X}
    (ha : HasExponentialDecay a) (hb : HasExponentialDecay b) : HasExponentialDecay (a + b) := by
  obtain ⟨c, hc, M, hM, haM⟩ := ha
  obtain ⟨d, hd, N, hN, hbN⟩ := hb
  refine ⟨min c d, lt_min hc hd, M + N, add_pos hM hN, fun r hr => ?_⟩
  simpa only [add_mul] using (quasiLocalModulus_add_le a b r).trans (add_le_add
    ((haM r hr).trans (mul_le_mul_of_nonneg_left (exp_neg_mul_antitone (min_le_left c d) hr) hM.le))
    ((hbN r hr).trans (mul_le_mul_of_nonneg_left (exp_neg_mul_antitone (min_le_right c d) hr) hN.le)))

theorem HasExponentialDecay.mul {X : Type u} [PseudoMetricSpace X] {a b : Operator X}
    (ha : HasExponentialDecay a) (hb : HasExponentialDecay b) : HasExponentialDecay (a * b) := by
  obtain ⟨c, hc, M, hM, haM⟩ := ha
  obtain ⟨d, hd, N, hN, hbN⟩ := hb
  refine ⟨min c d / 2, half_pos (lt_min hc hd), M * ‖b‖ + ‖a‖ * N + 1,
    by positivity, fun r hr => ?_⟩
  have hA := (haM (r / 2) (div_nonneg hr (by norm_num))).trans
    (mul_le_mul_of_nonneg_left (exp_neg_mul_antitone (min_le_left c d) (div_nonneg hr (by norm_num))) hM.le)
  have hB := (hbN (r / 2) (div_nonneg hr (by norm_num))).trans
    (mul_le_mul_of_nonneg_left (exp_neg_mul_antitone (min_le_right c d)
      (div_nonneg hr (by norm_num))) hN.le)
  have hp := (quasiLocalModulus_mul_le a b (r / 2) (r / 2)).trans
    (add_le_add (mul_le_mul_of_nonneg_right hA (norm_nonneg b))
      (mul_le_mul_of_nonneg_left hB (norm_nonneg a)))
  rw [show -(min c d / 2) * r = -min c d * (r / 2) by ring]
  nlinarith [show 0 < Real.exp (-min c d * (r / 2)) from Real.exp_pos _ ,
    (show r / 2 + r / 2 = r from add_halves r) ▸ hp]

theorem HasExponentialDecay.smul {X : Type u} [PseudoMetricSpace X] {a : Operator X}
    (ha : HasExponentialDecay a) (z : ℂ) : HasExponentialDecay (z • a) := by
  obtain ⟨c, hc, M, hM, haM⟩ := ha
  refine ⟨c, hc, (‖z‖ + 1) * M, mul_pos (by positivity) hM, fun r hr => ?_⟩
  have hz := (quasiLocalModulus_smul_le z a r).trans
    (mul_le_mul_of_nonneg_left (haM r hr) (norm_nonneg z))
  nlinarith [mul_pos hM (Real.exp_pos (-c * r))]

theorem HasFinitePropagation.hasExponentialDecay {X : Type u} [PseudoMetricSpace X]
    {a : Operator X} (ha : HasFinitePropagation a) : HasExponentialDecay a := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp ((finitePropagation_iff_modulus_eventually_zero a).mp ha)
  refine ⟨1, by norm_num, (‖a‖ + 1) * Real.exp R, by positivity, fun r hr => ?_⟩
  rw [neg_one_mul, mul_assoc, ← Real.exp_add]
  by_cases hRr : R ≤ r
  · rw [hR r hRr]
    positivity
  · have he : 1 ≤ Real.exp (R + -r) := Real.one_le_exp_iff.mpr (by linarith)
    nlinarith [quasiLocalModulus_le_norm a r, norm_nonneg a]

theorem hasFinitePropagation_algebraMap {X : Type u} [PseudoMetricSpace X] (z : ℂ) :
    HasFinitePropagation (algebraMap ℂ (Operator X) z) := by
  have he : diagonalMultiplier (algebraMap ℂ (BoundedDiagonal X) z) =
      algebraMap ℂ (Operator X) z := diagonalMultiplierHom.commutes z
  exact he ▸ (controlled_iff_finitePropagation _).mp
    (diagonalMultiplier_hasControlledPropagation (CoarseStructure.ofPseudoMetric X) _)

def exponentialDecayStarSubalgebra {X : Type u} [PseudoMetricSpace X] :
    StarSubalgebra ℂ (Operator X) where
  carrier := {a | HasExponentialDecay a}
  zero_mem' := by simpa only [zero_smul] using!
    (hasFinitePropagation_algebraMap (X := X) 1).hasExponentialDecay.smul 0
  one_mem' := by simpa only [map_one] using!
    (hasFinitePropagation_algebraMap (X := X) 1).hasExponentialDecay
  add_mem' := HasExponentialDecay.add
  mul_mem' := HasExponentialDecay.mul
  star_mem' := HasExponentialDecay.star
  algebraMap_mem' z := (hasFinitePropagation_algebraMap z).hasExponentialDecay

def exponentialQuasiLocalStarSubalgebra {X : Type u} [PseudoMetricSpace X] :
    StarSubalgebra ℂ (Operator X) := exponentialDecayStarSubalgebra.topologicalClosure

theorem coe_exponentialQuasiLocalStarSubalgebra {X : Type u} [PseudoMetricSpace X] :
    (exponentialQuasiLocalStarSubalgebra (X := X) : Set (Operator X)) = exponentialQuasiLocal := rfl

theorem exponentialQuasiLocalStarSubalgebra_isClosed {X : Type u} [PseudoMetricSpace X] :
    IsClosed (exponentialQuasiLocalStarSubalgebra (X := X) : Set (Operator X)) :=
  exponentialDecayStarSubalgebra.isClosed_topologicalClosure

theorem uniformRoe_subset_exponentialQuasiLocal {X : Type u} [PseudoMetricSpace X] :
    uniformRoe (CoarseStructure.ofPseudoMetric X) ⊆ exponentialQuasiLocal :=
  closure_mono fun _ ha => ((controlled_iff_finitePropagation _).mp ha).hasExponentialDecay

theorem HasExponentialDecay.isQuasiLocal {X : Type u} [PseudoMetricSpace X]
    {a : Operator X} (ha : HasExponentialDecay a) :
    IsQuasiLocal (CoarseStructure.ofPseudoMetric X) a := by
  obtain ⟨c, hc, M, _hM, haM⟩ := ha
  have ht : Tendsto (fun r : ℝ => M * Real.exp (-c * r)) atTop (nhds 0) := by
    simpa only [Function.comp_def, neg_mul, mul_zero] using!
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)).const_mul M
  exact (isQuasiLocal_iff_modulus_tendsto a).mpr (squeeze_zero'
    (Eventually.of_forall (quasiLocalModulus_nonneg a))
    ((eventually_ge_atTop 0).mono fun r hr => haM r hr) ht)

theorem exponentialQuasiLocal_subset_quasiLocal {X : Type u} [PseudoMetricSpace X] :
    exponentialQuasiLocal ⊆ quasiLocal (CoarseStructure.ofPseudoMetric X) :=
  closure_minimal (fun _ ha => ha.isQuasiLocal) (isClosed_quasiLocal _)

/-- The exponential decay closure is a closed complex star-subalgebra between Roe and quasi-local. -/
theorem exponentialQuasiLocal_algebra {X : Type u} [PseudoMetricSpace X] :
    (exponentialQuasiLocalStarSubalgebra (X := X) : Set (Operator X)) = exponentialQuasiLocal ∧
      IsClosed (exponentialQuasiLocalStarSubalgebra (X := X) : Set (Operator X)) ∧
      uniformRoe (CoarseStructure.ofPseudoMetric X) ⊆ exponentialQuasiLocal ∧
      exponentialQuasiLocal ⊆ quasiLocal (CoarseStructure.ofPseudoMetric X) :=
  ⟨coe_exponentialQuasiLocalStarSubalgebra, exponentialQuasiLocalStarSubalgebra_isClosed,
    uniformRoe_subset_exponentialQuasiLocal, exponentialQuasiLocal_subset_quasiLocal⟩

end DynamicalCStarAlgebras
