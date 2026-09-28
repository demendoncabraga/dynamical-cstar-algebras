import DynamicalCStarAlgebras.GraphUnionExponentialMetric

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- The usual bounded-step quasigeodesic formulation of large-scale geodesicity:
chain lengths are bounded by an affine function of endpoint distance. -/
def IsLargeScaleGeodesic (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∃ a b s : ℝ, 0 < a ∧ 0 ≤ b ∧ 0 < s ∧ ∀ x y : X,
    ∃ (n : ℕ) (f : ℕ → X), (n : ℝ) ≤ a * dist x y + b ∧ f 0 = x ∧ f n = y ∧
      ∀ i < n, dist (f i) (f (i + 1)) ≤ s

/-- Finite iterated metric neighborhoods used to count bounded-step chains. -/
def iteratedMetricBall {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) (s : ℝ) (x : X) : ℕ → Finset X
  | 0 => {x}
  | n + 1 => (iteratedMetricBall hX s x n).biUnion
      (fun y => (hX.finite_closedBall y s).toFinset)

lemma card_iteratedMetricBall_le {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) (s : ℝ) (x : X) (K : ℕ)
    (hK : ∀ y : X, (Metric.closedBall y s).ncard ≤ K) (n : ℕ) :
    (iteratedMetricBall hX s x n).card ≤ K ^ n := by
  induction n with
  | zero => simp [iteratedMetricBall]
  | succ n ih =>
    calc
      _ ≤ ∑ y ∈ iteratedMetricBall hX s x n, (hX.finite_closedBall y s).toFinset.card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ iteratedMetricBall hX s x n, K := Finset.sum_le_sum fun y _ => by
        simpa only [← Set.ncard_eq_toFinset_card] using hK y
      _ = (iteratedMetricBall hX s x n).card * K := by simp
      _ ≤ K ^ n * K := Nat.mul_le_mul_right K ih
      _ = _ := (pow_succ K n).symm

lemma iteratedMetricBall_mono {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) {s : ℝ} (hs : 0 ≤ s) (x : X) :
    Monotone (iteratedMetricBall hX s x) := by
  apply monotone_nat_of_le_succ
  intro n y hy
  exact Finset.mem_biUnion.mpr ⟨y, hy, by simpa using hs⟩

lemma chain_mem_iteratedMetricBall {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) (s : ℝ) (f : ℕ → X) (n : ℕ)
    (hf : ∀ i < n, dist (f i) (f (i + 1)) ≤ s) :
    f n ∈ iteratedMetricBall hX s (f 0) n := by
  induction n with
  | zero => simp [iteratedMetricBall]
  | succ n ih =>
    apply Finset.mem_biUnion.mpr
    refine ⟨f n, ih (fun i hi => hf i (by omega)), ?_⟩
    simpa only [Set.Finite.mem_toFinset, Metric.mem_closedBall, dist_comm] using hf n (by omega)

/-- Uniform local finiteness and large-scale geodesicity imply the source
exponential volume bound, with no exact-geodesicity assumption. -/
theorem IsLargeScaleGeodesic.atMostExponentialGrowth
    {X : Type*} [PseudoMetricSpace X] (hgeo : IsLargeScaleGeodesic X)
    (hX : UniformlyLocallyFinite X) : AtMostExponentialGrowth X := by
  obtain ⟨a, b, s, ha, hb, hs, hchain⟩ := hgeo
  obtain ⟨K₀, hK₀⟩ := hX s hs
  let K := max K₀ 2
  let q := ⌈a + b⌉₊ + 1
  have hK : ∀ y : X, (Metric.closedBall y s).ncard ≤ K :=
    fun y => (hK₀ y).2.trans (Nat.le_max_left _ _)
  refine ⟨((K ^ q : ℕ) : ℝ), ?_, ?_⟩
  · have hK2 : 2 ≤ K := Nat.le_max_right _ _
    exact_mod_cast (lt_of_lt_of_le (show 1 < K by omega) (Nat.le_pow (show 0 < q by omega)))
  intro r hr x
  have hsub : Metric.closedBall x r ⊆ (iteratedMetricBall hX s x (q * r) : Set X) := by
    intro y hy
    obtain ⟨n, f, hn, hx, hy', hf⟩ := hchain x y
    have hd : dist x y ≤ r := by simpa only [Metric.mem_closedBall, dist_comm] using hy
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hq : a + b ≤ (q : ℝ) := by
      exact (Nat.le_ceil (a + b)).trans (by simp [q])
    have hn' : n ≤ q * r := by
      apply Nat.cast_le.mp (show (n : ℝ) ≤ ((q * r : ℕ) : ℝ) from ?_)
      push_cast
      have hd' := mul_le_mul_of_nonneg_left hd ha.le
      have hq' := mul_le_mul_of_nonneg_right hq (show 0 ≤ (r : ℝ) by positivity)
      nlinarith
    apply iteratedMetricBall_mono hX hs.le x hn'
    simpa only [hx, hy'] using chain_mem_iteratedMetricBall hX s f n hf
  refine ⟨hX.finite_closedBall _ _, ?_⟩
  have hc := (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans
    (by simpa only [Set.ncard_coe_finset] using card_iteratedMetricBall_le hX s x K hK (q * r))
  rw [pow_mul] at hc
  exact_mod_cast hc

/-- Shortest-path metrics of connected graphs are bounded-step geodesic metrics. -/
theorem graphMetric_isLargeScaleGeodesic {X : Type*} (G : SimpleGraph X) (hc : G.Connected) :
    letI := connectedGraphMetric G hc
    IsLargeScaleGeodesic X := by
  let := connectedGraphMetric G hc
  refine ⟨1, 0, 1, by norm_num, le_rfl, by norm_num, ?_⟩
  intro x y
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist x y
  refine ⟨p.length, p.getVert, ?_, p.getVert_zero, p.getVert_length, ?_⟩
  · change (p.length : ℝ) ≤ 1 * (G.dist x y : ℝ) + 0
    simp only [hp, one_mul, add_zero, le_refl]
  · intro i hi
    change ((G.dist (p.getVert i) (p.getVert (i + 1)) : ℕ) : ℝ) ≤ 1
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr (p.adj_getVert_succ hi)]
    norm_num

/-- The connected-graph case of the source growth observation, including
uniformly locally finite Cayley graphs with their word metrics. -/
theorem graphMetric_atMostExponentialGrowth {X : Type*} (G : SimpleGraph X) (hc : G.Connected) :
    letI := connectedGraphMetric G hc
    UniformlyLocallyFinite X → AtMostExponentialGrowth X := by
  let := connectedGraphMetric G hc
  exact (graphMetric_isLargeScaleGeodesic G hc).atMostExponentialGrowth

end DynamicalCStarAlgebras
