import DynamicalCStarAlgebras.SchurBounds

noncomputable section

namespace DynamicalCStarAlgebras

/-- The matrix entries strictly outside a propagation radius. -/
def matrixTail {X : Type*} [PseudoMetricSpace X] (a : Operator X) (R : ℝ) (x y : X) : ℂ :=
  if R < dist x y then matrixEntry a x y else 0

/-- A Schur-small tail produces a finite-propagation approximation with the same error. -/
theorem finitePropagation_approximation_of_schur_tail {X : Type*} [PseudoMetricSpace X]
    (a : Operator X) {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (htail : HasSchurBound (matrixTail a R) C) :
    ∃ b : Operator X, HasFinitePropagation b ∧ ‖a - b‖ ≤ C := by
  let t := operatorOfSchurMatrix (matrixTail a R) htail hC
  refine ⟨a - t, ⟨R, hR, fun x y hxy => ?_⟩, ?_⟩
  · change (matrixEntryCLM x y) (a - t) = 0
    simp only [map_sub, matrixEntryCLM_apply, t, matrixEntry_operatorOfSchurMatrix,
      matrixTail, if_pos hxy, sub_self]
  · simpa only [sub_sub_cancel] using norm_operatorOfSchurMatrix_le _ htail hC

/-- Vanishing absolute row and column tails imply membership in the uniform Roe algebra. -/
theorem uniformRoe_of_schur_tails {X : Type*} [PseudoMetricSpace X] (a : Operator X)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ HasSchurBound (matrixTail a R) ε) :
    a ∈ uniformRoe (CoarseStructure.ofPseudoMetric X) := by
  rw [uniformRoe_metric_eq, Metric.mem_closure_iff]
  exact fun ε hε => (htail (ε / 2) (half_pos hε)).elim fun R ⟨hR, ht⟩ =>
    (finitePropagation_approximation_of_schur_tail a hR (half_pos hε).le ht).elim
      fun b ⟨hb, hdist⟩ => ⟨b, hb, by simpa only [dist_eq_norm] using
        (hdist.trans_lt (half_lt_self hε))⟩

end DynamicalCStarAlgebras
