import DynamicalCStarAlgebras.GeodesicGrowth
import DynamicalCStarAlgebras.GraphSlicing
import Mathlib.Combinatorics.SimpleGraph.Cayley

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- Finite neighborhoods in a locally finite graph, without a finite vertex-set assumption. -/
def finiteGraphBall {X : Type*} (G : SimpleGraph X) [G.LocallyFinite] (x : X) : ℕ → Finset X
  | 0 => {x}
  | n + 1 => insert x ((G.neighborFinset x).biUnion fun y => finiteGraphBall G y n)

/-- The elementary bounded-degree count works for infinite graphs as well. -/
theorem finiteGraphBall_card_le {X : Type*} (G : SimpleGraph X) [G.LocallyFinite]
    (k : ℕ) (hdeg : ∀ x, (G.neighborFinset x).card ≤ k) (n : ℕ) (x : X) :
    (finiteGraphBall G x n).card ≤ (k + 1) ^ n := by
  induction n generalizing x with
  | zero => simp [finiteGraphBall]
  | succ n ih =>
    calc
      _ ≤ ((G.neighborFinset x).biUnion fun y => finiteGraphBall G y n).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ (∑ y ∈ G.neighborFinset x, (finiteGraphBall G y n).card) + 1 :=
        Nat.add_le_add_right Finset.card_biUnion_le 1
      _ ≤ (G.neighborFinset x).card * (k + 1) ^ n + 1 := by
        gcongr
        exact (Finset.sum_le_sum fun y _ => ih y).trans_eq (by simp)
      _ ≤ k * (k + 1) ^ n + 1 := by gcongr; exact hdeg x
      _ ≤ (k + 1) ^ (n + 1) := by
        rw [pow_succ]
        have hp : 1 ≤ (k + 1) ^ n := Nat.one_le_pow n _ (by omega)
        nlinarith

/-- A shortest path puts the metric ball inside the recursively counted finite neighborhood. -/
theorem graph_dist_mem_finiteGraphBall {X : Type*} (G : SimpleGraph X) [G.LocallyFinite]
    (hc : G.Connected) (n : ℕ) {x y : X} (hxy : G.dist x y ≤ n) :
    y ∈ finiteGraphBall G x n := by
  induction n generalizing x y with
  | zero =>
    have he := hc.dist_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hxy)
    simp [finiteGraphBall, he]
  | succ n ih =>
    obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist x y
    cases p with
    | nil => exact Finset.mem_insert_self _ _
    | @cons x z y hxz p =>
      refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨z, ?_, ?_⟩)
      · simpa using hxz
      · apply ih
        have hp' : p.length ≤ n := by
          simpa only [SimpleGraph.Walk.length_cons, Nat.add_le_add_iff_right] using hp.le.trans hxy
        exact (SimpleGraph.dist_le p).trans hp'

/-- A connected graph of uniformly bounded degree is uniformly locally finite in its graph metric. -/
theorem graphMetric_uniformlyLocallyFinite {X : Type*} (G : SimpleGraph X) [G.LocallyFinite]
    (hc : G.Connected) (k : ℕ) (hdeg : ∀ x, (G.neighborFinset x).card ≤ k) :
    letI := connectedGraphMetric G hc
    UniformlyLocallyFinite X := by
  let := connectedGraphMetric G hc
  intro R hR
  refine ⟨(k + 1) ^ ⌊R⌋₊, fun x => ?_⟩
  have hsub : Metric.closedBall x R ⊆ (finiteGraphBall G x ⌊R⌋₊ : Set X) := by
    intro y hy
    apply graph_dist_mem_finiteGraphBall G hc
    apply (Nat.le_floor_iff hR.le).mpr
    change (G.dist y x : ℝ) ≤ R at hy
    simpa only [G.dist_comm] using hy
  refine ⟨(finiteGraphBall G x ⌊R⌋₊).finite_toSet.subset hsub, ?_⟩
  exact (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans
    (by simpa only [Set.ncard_coe_finset] using finiteGraphBall_card_le G k hdeg ⌊R⌋₊ x)

/-- The same graph metric has the source exponential volume bound. -/
theorem graphMetric_exponentialGrowth_of_boundedDegree {X : Type*} (G : SimpleGraph X)
    [G.LocallyFinite] (hc : G.Connected) (k : ℕ)
    (hdeg : ∀ x, (G.neighborFinset x).card ≤ k) :
    letI := connectedGraphMetric G hc
    AtMostExponentialGrowth X :=
  graphMetric_atMostExponentialGrowth G hc (graphMetric_uniformlyLocallyFinite G hc k hdeg)

/-- A generating subset makes the undirected Cayley graph connected. -/
theorem mulCayley_connected {M : Type*} [Group M] (S : Set M)
    (hS : Subgroup.closure S = ⊤) : (SimpleGraph.mulCayley S).Connected := by
  let G := SimpleGraph.mulCayley S
  let H : Subgroup M :=
    { carrier := {g | ∀ x, G.Reachable x (x * g)}
      one_mem' := fun x => by simp
      mul_mem' := fun ha hb x => by
        simpa only [mul_assoc] using (ha x).trans (hb (x * _))
      inv_mem' := fun {a} ha x => by
        simpa only [inv_mul_cancel_right] using (ha (x * a⁻¹)).symm }
  have hSH : S ⊆ H := by
    intro s hs x
    by_cases hx : x = x * s
    · exact hx ▸ SimpleGraph.Reachable.refl x
    · exact ((SimpleGraph.mulCayley_adj' S x (x * s)).mpr
        ⟨hx, s, hs, Or.inl rfl⟩).reachable
  have htop : (⊤ : Subgroup M) ≤ H := hS ▸ (Subgroup.closure_le H).mpr hSH
  refine ⟨fun x y => ?_⟩
  have hxy := htop (show x⁻¹ * y ∈ (⊤ : Subgroup M) from trivial) x
  simpa only [mul_inv_cancel_left] using hxy

lemma mulCayley_neighbor_subset {M : Type*} [Group M] (S : Finset M) (x : M) :
    (SimpleGraph.mulCayley (S : Set M)).neighborSet x ⊆
      (S.image (fun s => x * s) ∪ S.image (fun s => x * s⁻¹) : Finset M) := by
  intro y hy
  obtain ⟨_, s, hs, hxy | hxy⟩ := (SimpleGraph.mulCayley_adj' (S : Set M) x y).mp hy
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, hs, hxy⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨s, hs, ((eq_mul_inv_iff_mul_eq).mpr hxy.symm).symm⟩)

instance mulCayley_locallyFinite {M : Type*} [Group M] (S : Finset M) :
    (SimpleGraph.mulCayley (S : Set M)).LocallyFinite := fun x =>
  ((Finset.finite_toSet _).subset (mulCayley_neighbor_subset S x)).fintype

lemma mulCayley_degree_le {M : Type*} [Group M] (S : Finset M) (x : M) :
    ((SimpleGraph.mulCayley (S : Set M)).neighborFinset x).card ≤ 2 * S.card := by
  have hsub : (SimpleGraph.mulCayley (S : Set M)).neighborFinset x ⊆
      S.image (fun s => x * s) ∪ S.image (fun s => x * s⁻¹) := by
    intro y hy
    exact mulCayley_neighbor_subset S x ((SimpleGraph.mem_neighborFinset _ _ _).mp hy)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (by have h₁ := Finset.card_image_le (s := S) (f := fun s => x * s)
        have h₂ := Finset.card_image_le (s := S) (f := fun s => x * s⁻¹)
        omega))

/-- Every finite generating set gives a uniformly locally finite Cayley graph,
with at most exponential growth in its unchanged shortest-path metric. -/
theorem finiteGeneratingSet_cayley_geometry {M : Type*} [Group M] (S : Finset M)
    (hS : Subgroup.closure (S : Set M) = ⊤) :
    letI := connectedGraphMetric (SimpleGraph.mulCayley (S : Set M)) (mulCayley_connected _ hS)
    UniformlyLocallyFinite M ∧ AtMostExponentialGrowth M :=
  ⟨graphMetric_uniformlyLocallyFinite _ (mulCayley_connected _ hS) (2 * S.card)
      (mulCayley_degree_le S),
    graphMetric_exponentialGrowth_of_boundedDegree _ (mulCayley_connected _ hS)
      (2 * S.card) (mulCayley_degree_le S)⟩

/-- The source Cayley-graph examples apply to every finitely generated group. -/
theorem finitelyGeneratedGroup_cayley_geometry (M : Type*) [Group M] [Group.FG M] :
    ∃ S : Finset M, ∃ hS : Subgroup.closure (S : Set M) = ⊤,
      letI := connectedGraphMetric (SimpleGraph.mulCayley (S : Set M)) (mulCayley_connected _ hS)
      UniformlyLocallyFinite M ∧ AtMostExponentialGrowth M := by
  obtain ⟨S, hS, hf⟩ := Group.fg_iff.mp (inferInstance : Group.FG M)
  have hs : Subgroup.closure (hf.toFinset : Set M) = ⊤ := by simpa using hS
  exact ⟨hf.toFinset, hs, finiteGeneratingSet_cayley_geometry _ hs⟩

end DynamicalCStarAlgebras
