import DynamicalCStarAlgebras.SeparatedBlockSelection

namespace DynamicalCStarAlgebras

/-- Uniform local finiteness for a coarse structure, stated on symmetric
entourages exactly as in Section 2.1. -/
def CoarseStructure.UniformlyLocallyFinite {X : Type*} (C : CoarseStructure X) : Prop :=
  ∀ E ∈ C.controlled, (∀ x y, (x, y) ∈ E → (y, x) ∈ E) →
    ∃ N : ℕ, ∀ x : X, {y | (x, y) ∈ E}.Finite ∧ {y | (x, y) ∈ E}.ncard ≤ N

/-- Symmetrizing an entourage gives the same kind of uniform fiber bound for
arbitrary controlled relations. -/
theorem CoarseStructure.UniformlyLocallyFinite.fiber_bounds {X : Type*}
    {C : CoarseStructure X} (hC : C.UniformlyLocallyFinite) {E : Set (X × X)}
    (hE : E ∈ C.controlled) :
    ∃ N : ℕ, ∀ x : X, {y | (x, y) ∈ E}.Finite ∧ {y | (x, y) ∈ E}.ncard ≤ N := by
  obtain ⟨N, hN⟩ := hC (E ∪ {p | (p.2, p.1) ∈ E}) (C.union hE (C.inverse hE))
    (fun _ _ hp => hp.elim Or.inr Or.inl)
  refine ⟨N, fun x => ?_⟩
  have hs : {y | (x, y) ∈ E} ⊆ {y | (x, y) ∈ E ∪ {p | (p.2, p.1) ∈ E}} :=
    fun _ hy => Or.inl hy
  exact ⟨(hN x).1.subset hs, (Set.ncard_le_ncard hs (hN x).1).trans (hN x).2⟩

/-- The coarse-space definition specializes exactly to uniform finite ball bounds. -/
theorem coarse_uniformlyLocallyFinite_iff {X : Type*} [PseudoMetricSpace X] :
    (CoarseStructure.ofPseudoMetric X).UniformlyLocallyFinite ↔ UniformlyLocallyFinite X := by
  constructor
  · intro hC R hR
    obtain ⟨N, hN⟩ := hC.fiber_bounds (E := {p : X × X | dist p.1 p.2 ≤ R})
      ⟨R, fun _ hp => hp⟩
    refine ⟨N, fun x => ?_⟩
    simpa only [Metric.closedBall, Set.mem_ofPred_eq, dist_comm x] using hN x
  · intro hX E hE _
    obtain ⟨R, hR⟩ := hE
    obtain ⟨N, hN⟩ := hX (max R 0 + 1) (by positivity)
    refine ⟨N, fun x => ?_⟩
    have hs : {y | (x, y) ∈ E} ⊆ Metric.closedBall x (max R 0 + 1) := by
      intro y hy
      change dist y x ≤ _
      rw [dist_comm]
      exact (hR (x, y) hy).trans ((le_max_left R 0).trans (by linarith))
    exact ⟨(hN x).1.subset hs, (Set.ncard_le_ncard hs (hN x).1).trans (hN x).2⟩

end DynamicalCStarAlgebras
