import DynamicalCStarAlgebras.MatchingRayGraph
import DynamicalCStarAlgebras.CayleyGrowth

noncomputable section
open Classical
namespace DynamicalCStarAlgebras
namespace CoarseMatchingCover
variable {X : Type*} [PseudoMetricSpace X]

instance graph_locallyFinite (M : CoarseMatchingCover X) : M.graph.LocallyFinite :=
  fun a => (M.neighbor_bound a).1.fintype

/-- The matching-ray construction has degree at most three. -/
theorem graph_degree_le (M : CoarseMatchingCover X) (a : X × ℕ) :
    (M.graph.neighborFinset a).card ≤ 3 := by
  have h := (M.neighbor_bound a).2
  simpa only [← SimpleGraph.coe_neighborFinset, Set.ncard_coe_finset] using h

/-- Pull the graph metric back to the injectively embedded ray roots. -/
@[instance_reducible] def rootMetric (M : CoarseMatchingCover X) [Nonempty X] : MetricSpace X :=
  MetricSpace.induced (fun x : X => (x, (0 : ℕ)))
    (fun _ _ h => congrArg Prod.fst h) (connectedGraphMetric M.graph M.connected)

/-- Restricting the graph metric to its roots retains exponential volume growth. -/
theorem rootMetric_exponentialGrowth (M : CoarseMatchingCover X) [Nonempty X] :
    @AtMostExponentialGrowth X M.rootMetric.toPseudoMetricSpace := by
  let : PseudoMetricSpace (X × ℕ) := (connectedGraphMetric M.graph M.connected).toPseudoMetricSpace
  obtain ⟨L, hL, hb⟩ := graphMetric_exponentialGrowth_of_boundedDegree
    M.graph M.connected 3 M.graph_degree_le
  let : PseudoMetricSpace X := M.rootMetric.toPseudoMetricSpace
  refine ⟨L, hL, fun n hn x => ?_⟩
  let f : X → X × ℕ := fun x => (x, 0)
  have hf : Function.Injective f := fun _ _ h => congrArg Prod.fst h
  have hi : Set.MapsTo f (Metric.closedBall x (n : ℝ)) (Metric.closedBall (f x) (n : ℝ)) :=
    fun y hy => hy
  obtain ⟨hfin, hcard⟩ := hb n hn (f x)
  refine ⟨hfin.of_injOn hi hf.injOn, ?_⟩
  exact (Nat.cast_le.mpr (Set.ncard_le_ncard_of_injOn f hi hf.injOn hfin)).trans hcard

/-- The induced metric has exactly the original controlled sets. -/
theorem rootMetric_coarseStructure (M : CoarseMatchingCover X) [Nonempty X] :
    @CoarseStructure.ofPseudoMetric X M.rootMetric.toPseudoMetricSpace =
      CoarseStructure.ofPseudoMetric X := by
  have he : (@CoarseStructure.ofPseudoMetric X M.rootMetric.toPseudoMetricSpace).controlled =
      (CoarseStructure.ofPseudoMetric X).controlled := by
    ext E
    constructor
    · rintro ⟨R, hR⟩
      refine ⟨(max R 0) ^ 2, fun p hp => ?_⟩
      have hl := M.root_distance_lower p.1 p.2
      have hu := hR p hp
      change (M.graph.dist (p.1, 0) (p.2, 0) : ℝ) ≤ R at hu
      have hn : (0 : ℝ) ≤ M.graph.dist (p.1, 0) (p.2, 0) := Nat.cast_nonneg _
      exact hl.trans (pow_le_pow_left₀ hn (hu.trans (le_max_left _ _)) 2)
    · rintro ⟨R, hR⟩
      obtain ⟨N, hN⟩ := M.root_distance_upper R
      refine ⟨(N : ℝ), fun p hp => ?_⟩
      change (M.graph.dist (p.1, 0) (p.2, 0) : ℝ) ≤ (N : ℝ)
      exact_mod_cast hN p.1 p.2 (hR p hp)
  cases h₁ : @CoarseStructure.ofPseudoMetric X M.rootMetric.toPseudoMetricSpace
  cases h₂ : CoarseStructure.ofPseudoMetric X
  simp_all

end CoarseMatchingCover
/-- Every uniformly locally finite metric space admits an injective coarse embedding
into a connected graph of degree at most three (DGLY, Proposition 5.1).
The two bounded-distance implications state both coarse controls explicitly. -/
theorem exists_boundedDegree_coarseEmbedding {X : Type u} [MetricSpace X]
    (hX : UniformlyLocallyFinite X) :
    ∃ (Y : Type u) (G : SimpleGraph Y), G.Connected ∧
      (∀ y, (G.neighborSet y).Finite ∧ (G.neighborSet y).ncard ≤ 3) ∧
      ∃ f : X → Y, Function.Injective f ∧
        (∀ R : ℝ, ∃ N : ℕ, ∀ x y, dist x y ≤ R → G.dist (f x) (f y) ≤ N) ∧
        (∀ N : ℕ, ∃ R : ℝ, ∀ x y, G.dist (f x) (f y) ≤ N → dist x y ≤ R) := by
  cases isEmpty_or_nonempty X with
  | inl h =>
    let G : SimpleGraph PUnit := ⊥
    refine ⟨PUnit, G, ?_, ?_, fun x => isEmptyElim x, ?_, ?_, ?_⟩
    · exact { preconnected := fun x y => by cases x; cases y; exact .refl _,
              nonempty := inferInstance }
    · intro y
      simp [G]
    · intro x
      exact isEmptyElim x
    · exact fun R => ⟨0, fun x => isEmptyElim x⟩
    · exact fun N => ⟨0, fun x => isEmptyElim x⟩
  | inr h =>
    obtain ⟨M⟩ := exists_coarseMatchingCover hX
    refine ⟨X × ℕ, M.graph, M.connected, M.neighbor_bound, fun x => (x, 0),
      (fun _ _ h => congrArg Prod.fst h), M.root_distance_upper, ?_⟩
    intro N
    refine ⟨(N : ℝ) ^ 2, fun x y hxy => ?_⟩
    exact (M.root_distance_lower x y).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hxy) 2)

/-- Every uniformly locally finite metric space has a metric of exponential growth
on the same set with exactly the same coarse structure. -/
theorem exists_exponentialGrowth_metric {X : Type*} [m₀ : MetricSpace X]
    (hX : UniformlyLocallyFinite X) :
    ∃ m : MetricSpace X, @AtMostExponentialGrowth X m.toPseudoMetricSpace ∧
      @CoarseStructure.ofPseudoMetric X m.toPseudoMetricSpace =
        @CoarseStructure.ofPseudoMetric X m₀.toPseudoMetricSpace := by
  cases isEmpty_or_nonempty X with
  | inl h => exact ⟨m₀, ⟨2, by norm_num, fun n hn x => isEmptyElim x⟩, rfl⟩
  | inr h =>
    obtain ⟨M⟩ := exists_coarseMatchingCover hX
    exact ⟨M.rootMetric, M.rootMetric_exponentialGrowth, M.rootMetric_coarseStructure⟩

end DynamicalCStarAlgebras
