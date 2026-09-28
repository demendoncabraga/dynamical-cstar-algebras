import DynamicalCStarAlgebras.MetricQuasiLocal

noncomputable section

namespace DynamicalCStarAlgebras

universe u

/-- Norms of compressions by sets separated by at least r. -/
def compressionNorms {X : Type u} [PseudoMetricSpace X] (a : Operator X) (r : ℝ) : Set ℝ :=
  {s | ∃ A B : Set X, (∀ x ∈ A, ∀ y ∈ B, r ≤ dist x y) ∧
    s = ‖coordinateProjection A * a * coordinateProjection B‖}

theorem compressionNorms_nonempty {X : Type u} [PseudoMetricSpace X]
    (a : Operator X) (r : ℝ) : (compressionNorms a r).Nonempty :=
  ⟨_, ∅, ∅, fun _ hx => hx.elim, rfl⟩

theorem compressionNorms_bddAbove {X : Type u} [PseudoMetricSpace X]
    (a : Operator X) (r : ℝ) : BddAbove (compressionNorms a r) :=
  ⟨‖a‖, fun _ hs => hs.elim fun A hA => hA.elim fun B hB =>
    hB.2 ▸ compression_norm_le a A B⟩

/-- Definition `Defi.QL.Decay.modulus`, extended harmlessly to all real radii.
Every set of values is nonempty and bounded above by the operator norm. -/
def quasiLocalModulus {X : Type u} [PseudoMetricSpace X] (a : Operator X) (r : ℝ) : ℝ :=
  sSup (compressionNorms a r)

theorem quasiLocalModulus_le_iff {X : Type u} [PseudoMetricSpace X]
    (a : Operator X) (r ε : ℝ) : quasiLocalModulus a r ≤ ε ↔
      ∀ A B : Set X, (∀ x ∈ A, ∀ y ∈ B, r ≤ dist x y) →
        ‖coordinateProjection A * a * coordinateProjection B‖ ≤ ε :=
  ⟨fun h A B hAB => (le_csSup (compressionNorms_bddAbove a r)
      (show ‖coordinateProjection A * a * coordinateProjection B‖ ∈ compressionNorms a r
        from ⟨A, B, hAB, rfl⟩)).trans h,
    fun h => csSup_le (compressionNorms_nonempty a r) fun _ hs =>
      hs.elim fun A hA => hA.elim fun B hB => hB.2 ▸ h A B hB.1⟩

theorem quasiLocalModulus_nonneg {X : Type u} [PseudoMetricSpace X]
    (a : Operator X) (r : ℝ) : 0 ≤ quasiLocalModulus a r :=
  (compressionNorms_nonempty a r).elim fun _ hs =>
    hs.elim fun A hA => hA.elim fun B hB =>
      (hB.2 ▸ norm_nonneg (coordinateProjection A * a * coordinateProjection B)).trans
        (le_csSup (compressionNorms_bddAbove a r) hs)

theorem quasiLocalModulus_antitone {X : Type u} [PseudoMetricSpace X]
    (a : Operator X) : Antitone (quasiLocalModulus a) :=
  fun _ _ hrs => (quasiLocalModulus_le_iff _ _ _).mpr fun A B hAB =>
    (quasiLocalModulus_le_iff _ _ _).mp le_rfl A B
      (fun x hx y hy => hrs.trans (hAB x hx y hy))

/-- Quasi-locality is equivalent to arbitrarily small values of the modulus. -/
theorem isMetricQuasiLocal_iff_modulus {X : Type u} [PseudoMetricSpace X]
    (a : Operator X) : IsMetricQuasiLocal a ↔
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ quasiLocalModulus a R ≤ ε := by
  simp only [IsMetricQuasiLocal, quasiLocalModulus_le_iff]

theorem dist_quasiLocalModulus_zero {X : Type u} [PseudoMetricSpace X]
    (a : Operator X) (r : ℝ) : dist (quasiLocalModulus a r) 0 = quasiLocalModulus a r := by
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg (quasiLocalModulus_nonneg a r)]

/-- Example `Example.decay.ql`: quasi-locality is exactly decay of the modulus to zero. -/
theorem isQuasiLocal_iff_modulus_tendsto {X : Type u} [PseudoMetricSpace X]
    (a : Operator X) : IsQuasiLocal (CoarseStructure.ofPseudoMetric X) a ↔
      Filter.Tendsto (quasiLocalModulus a) Filter.atTop (nhds 0) := by
  rw [isQuasiLocal_iff_metric, isMetricQuasiLocal_iff_modulus, Metric.tendsto_atTop]
  simp only [dist_quasiLocalModulus_zero]
  exact ⟨fun h ε hε => (h (ε / 2) (half_pos hε)).elim fun R hR =>
    ⟨R, fun _ hr => lt_of_le_of_lt ((quasiLocalModulus_antitone a hr).trans hR.2)
      (half_lt_self hε)⟩,
    fun h ε hε => (h ε hε).elim fun N hN =>
      ⟨max N 1, lt_of_lt_of_le zero_lt_one (le_max_right N 1),
        (hN (max N 1) (le_max_left N 1)).le⟩⟩

theorem matrixEntry_eq_zero_of_compression_eq_zero {X : Type u} {a : Operator X}
    {A B : Set X} (h : coordinateProjection A * a * coordinateProjection B = 0)
    {x y : X} (hx : x ∈ A) (hy : y ∈ B) : matrixEntry a x y = 0 := by
  have h0 : coordinateProjection A (a (coordinateProjection B (delta y))) x = 0 :=
    congrArg (fun T : Operator X => T (delta y) x) h
  simpa only [matrixEntry, coordinateProjection_delta_of_mem hy,
    coordinateProjection_apply_of_mem A _ hx] using h0

theorem quasiLocalModulus_eq_zero_iff {X : Type u} [PseudoMetricSpace X]
    (a : Operator X) (r : ℝ) : quasiLocalModulus a r = 0 ↔
      ∀ x y, r ≤ dist x y → matrixEntry a x y = 0 :=
  ⟨fun h x y hxy => matrixEntry_eq_zero_of_compression_eq_zero
    (norm_le_zero_iff.mp ((quasiLocalModulus_le_iff a r 0).mp h.le {x} {y}
      (by simpa only [Set.mem_singleton_iff, forall_eq] using hxy)))
    (Set.mem_singleton x) (Set.mem_singleton y),
    fun h => le_antisymm ((quasiLocalModulus_le_iff a r 0).mpr fun A B hAB =>
      (compression_eq_zero_of_entries a A B fun x hx y hy => h x y (hAB x hx y hy)) ▸
        le_of_eq (norm_zero : ‖(0 : Operator X)‖ = 0)) (quasiLocalModulus_nonneg a r)⟩

/-- Example `Example.decay.uRa`: finite propagation is eventual vanishing of the modulus. -/
theorem finitePropagation_iff_modulus_eventually_zero {X : Type u} [PseudoMetricSpace X]
    (a : Operator X) : HasFinitePropagation a ↔
      ∀ᶠ r in Filter.atTop, quasiLocalModulus a r = 0 :=
  ⟨fun h => h.elim fun R hR => Filter.eventually_atTop.mpr
    ⟨R + 1, fun r hr => (quasiLocalModulus_eq_zero_iff a r).mpr fun x y hxy =>
      hR.2 x y ((lt_add_one R).trans_le (hr.trans hxy))⟩,
    fun h => (Filter.eventually_atTop.mp h).elim fun R hR =>
      ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right R 1),
        fun x y hxy => (quasiLocalModulus_eq_zero_iff a (max R 1)).mp
          (hR (max R 1) (le_max_left R 1)) x y hxy.le⟩⟩

end DynamicalCStarAlgebras
