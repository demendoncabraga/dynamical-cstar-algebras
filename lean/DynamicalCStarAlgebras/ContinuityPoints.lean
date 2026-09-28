import DynamicalCStarAlgebras.DiagonalStar

namespace DynamicalCStarAlgebras

universe u

theorem diagonalFlow_sub {X : Type u} (h : X → ℝ) (t : ℝ) (a b : Operator X) :
    diagonalFlow h t (a - b) = diagonalFlow h t a - diagonalFlow h t b := by
  simp only [diagonalFlow, mul_sub, sub_mul]

theorem diagonalFlow_dist {X : Type u} (h : X → ℝ) (t : ℝ) (a b : Operator X) :
    dist (diagonalFlow h t a) (diagonalFlow h t b) = dist a b := by
  simp only [dist_eq_norm, ← diagonalFlow_sub, diagonalFlow_norm]

/-- The norm-continuity points of the diagonal pre-flow, as in the introduction. -/
def continuityPoints {X : Type u} (h : X → ℝ) : Set (Operator X) :=
  {a | Continuous (fun t : ℝ => diagonalFlow h t a)}

/-- Uniformly nonexpanding maps have a closed set of continuous orbits. -/
theorem isClosed_continuousOrbitSet {E : Type*} [PseudoMetricSpace E]
    (f : ℝ → E → E) (hf : ∀ t x y, dist (f t x) (f t y) ≤ dist x y) :
    IsClosed {x | Continuous (fun t : ℝ => f t x)} := by
  refine isClosed_of_closure_subset fun a ha => continuous_iff_continuousAt.mpr fun t => ?_
  refine Metric.continuousAt_iff.mpr fun ε hε => ?_
  obtain ⟨b, hb, hab⟩ := Metric.mem_closure_iff.mp ha (ε / 3) (by positivity)
  obtain ⟨δ, hδ, hbδ⟩ := (Metric.continuousAt_iff (a := t)).mp hb.continuousAt
    (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have hd := dist_triangle4 (f s a) (f s b) (f t b) (f t a)
  linarith [hbδ hs, hf s a b, hf t b a, dist_comm b a]

/-- Norm-continuity of an orbit is closed under operator-norm limits. -/
theorem isClosed_continuityPoints {X : Type u} (h : X → ℝ) :
    IsClosed (continuityPoints h) :=
  isClosed_continuousOrbitSet (diagonalFlow h) fun t a b => (diagonalFlow_dist h t a b).le

/-- For a diagonal pre-flow, continuity at zero implies continuity at every time. -/
theorem mem_continuityPoints_iff_continuousAt_zero {X : Type u} (h : X → ℝ)
    (a : Operator X) : a ∈ continuityPoints h ↔
      ContinuousAt (fun t : ℝ => diagonalFlow h t a) 0 := by
  refine ⟨fun ha => ha.continuousAt, fun ha => continuous_iff_continuousAt.mpr fun t => ?_⟩
  have hc := (continuous_diagonalFlow h t).continuousAt.comp
    (ha.comp_of_eq (continuousAt_id.sub continuousAt_const) (sub_self t))
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, ← diagonalFlow_add,
    ← add_sub_assoc, add_sub_cancel_left] using hc

/-- The continuity points form a unital complex star-subalgebra. -/
noncomputable def continuityPointsStarSubalgebra {X : Type u} (h : X → ℝ) :
    StarSubalgebra ℂ (Operator X) where
  carrier := {a | Continuous (fun t : ℝ => diagonalFlowEquiv h t a)}
  zero_mem' := by simpa only [Set.mem_ofPred_eq, map_zero] using
    (continuous_const : Continuous (fun _ : ℝ => (0 : Operator X)))
  one_mem' := by simpa only [Set.mem_ofPred_eq, map_one] using
    (continuous_const : Continuous (fun _ : ℝ => (1 : Operator X)))
  add_mem' ha hb := by simpa only [Set.mem_ofPred_eq, map_add, Pi.add_def] using ha.add hb
  mul_mem' ha hb := by simpa only [Set.mem_ofPred_eq, map_mul, Pi.mul_def] using ha.mul hb
  star_mem' ha := by simpa only [Set.mem_ofPred_eq, map_star] using ha.star
  algebraMap_mem' c := by simpa only [Set.mem_ofPred_eq, AlgHomClass.commutes] using
    (continuous_const : Continuous (fun _ : ℝ => algebraMap ℂ (Operator X) c))

theorem coe_continuityPointsStarSubalgebra {X : Type u} (h : X → ℝ) :
    (continuityPointsStarSubalgebra h : Set (Operator X)) = continuityPoints h :=
  show {a | Continuous (fun t : ℝ => diagonalFlowEquiv h t a)} =
    {a | Continuous (fun t : ℝ => diagonalFlow h t a)} from by
      simp only [diagonalFlowEquiv_apply]

/-- The norm-closed complex star-subalgebra of continuity points from the introduction. -/
theorem continuityPointsStarSubalgebra_isClosed {X : Type u} (h : X → ℝ) :
    IsClosed (continuityPointsStarSubalgebra h : Set (Operator X)) :=
  (coe_continuityPointsStarSubalgebra h).symm ▸ isClosed_continuityPoints h

end DynamicalCStarAlgebras
