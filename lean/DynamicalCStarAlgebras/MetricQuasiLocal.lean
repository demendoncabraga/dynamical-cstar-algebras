import DynamicalCStarAlgebras.RoeQuasiLocal

/-! Comparison of the entourage and metric definitions of quasi-locality. -/

namespace DynamicalCStarAlgebras

universe u

/-- Metric quasi-locality, with separation expressed pointwise. This also treats
empty subsets correctly, without a convention for the infimum of an empty set. -/
def IsMetricQuasiLocal {X : Type u} [PseudoMetricSpace X] (a : Operator X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ A B : Set X,
    (∀ x ∈ A, ∀ y ∈ B, R ≤ dist x y) →
      ‖coordinateProjection A * a * coordinateProjection B‖ ≤ ε

/-- Section 2.2: the metric and entourage definitions of quasi-locality agree. -/
theorem isQuasiLocal_iff_metric {X : Type u} [PseudoMetricSpace X] (a : Operator X) :
    IsQuasiLocal (CoarseStructure.ofPseudoMetric X) a ↔ IsMetricQuasiLocal a :=
  ⟨fun h ε hε => (h ε hε).elim fun _ hE => hE.1.elim fun S hS =>
    ⟨max S 0 + 1, lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left (le_max_right S 0)),
      fun A B hAB => hE.2 A B (Set.disjoint_left.mpr fun p hp hpE =>
        not_le_of_gt
          ((lt_add_of_le_of_pos (le_max_left S 0) zero_lt_one).trans_le
            (hAB p.1 hp.1 p.2 hp.2)) (hS p hpE))⟩,
    fun h ε hε => (h ε hε).elim fun R hR =>
      ⟨{p | dist p.1 p.2 < R}, ⟨R, fun _ hp => hp.le⟩,
        fun A B hAB => hR.2 A B fun x hx y hy => le_of_not_gt fun hxy =>
          Set.disjoint_left.mp hAB (show (x, y) ∈ A ×ˢ B from ⟨hx, hy⟩) hxy⟩⟩

end DynamicalCStarAlgebras
