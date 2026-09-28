import DynamicalCStarAlgebras.OperatorSupport

noncomputable section
open scoped ENNReal
namespace DynamicalCStarAlgebras

/-- Metric propagation, as an extended nonnegative real number so that an
unbounded support has propagation infinity and the zero operator has propagation zero. -/
def metricPropagation {X : Type*} [PseudoMetricSpace X] (a : Operator X) : ℝ≥0∞ :=
  ⨆ p : operatorSupport a, edist p.val.1 p.val.2

lemma metricPropagation_le_iff {X : Type*} [PseudoMetricSpace X]
    (a : Operator X) (R : ℝ≥0∞) : metricPropagation a ≤ R ↔
      ∀ x y, matrixEntry a x y ≠ 0 → edist x y ≤ R := by
  simp only [metricPropagation, iSup_le_iff, Subtype.forall, operatorSupport,
    Set.mem_ofPred_eq, Prod.forall]

/-- The extended supremum is at most a nonnegative bound exactly when all
matrix entries beyond that bound vanish. -/
theorem metricPropagation_le_ofReal_iff {X : Type*} [PseudoMetricSpace X]
    (a : Operator X) {R : ℝ} (hR : 0 ≤ R) :
    metricPropagation a ≤ ENNReal.ofReal R ↔
      ∀ x y, R < dist x y → matrixEntry a x y = 0 := by
  rw [metricPropagation_le_iff]
  constructor
  · intro h x y hxy
    by_contra hn
    have hb := h x y hn
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hR] at hb
    linarith
  · intro h x y hn
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (le_of_not_gt fun hxy => hn (h x y hxy))

/-- The source supremum definition and finite-propagation predicate agree. -/
theorem metricPropagation_lt_top_iff {X : Type*} [PseudoMetricSpace X]
    (a : Operator X) : metricPropagation a < ⊤ ↔ HasFinitePropagation a := by
  constructor
  · intro hfin
    refine ⟨(metricPropagation a).toReal + 1, by positivity, ?_⟩
    intro x y hxy
    by_contra hne
    have hb := (metricPropagation_le_iff a (metricPropagation a)).mp le_rfl x y hne
    have hdist : dist x y ≤ (metricPropagation a).toReal := by
      simpa only [edist_dist, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist x y)] using
        ENNReal.toReal_mono hfin.ne hb
    linarith
  · rintro ⟨R, hR, hprop⟩
    exact lt_of_le_of_lt ((metricPropagation_le_ofReal_iff a hR.le).mpr hprop)
      ENNReal.ofReal_lt_top

end DynamicalCStarAlgebras
