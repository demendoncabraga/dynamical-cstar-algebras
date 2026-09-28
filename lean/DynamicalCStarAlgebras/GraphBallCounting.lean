import DynamicalCStarAlgebras.CompressionDecay

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

lemma graph_ball_subset_neighbors {X : Type*} [Fintype X] (G : SimpleGraph X)
    (hc : G.Connected) (x : X) (n : ℕ) :
    (Finset.univ.filter fun y => G.dist x y ≤ n + 1) ⊆
      insert x ((G.neighborFinset x).biUnion fun z =>
        Finset.univ.filter fun y => G.dist z y ≤ n) := by
  intro y hy
  have hd := (Finset.mem_filter.mp hy).2
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist x y
  cases p with
  | nil => exact Finset.mem_insert_self _ _
  | @cons u z y hxz p =>
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    refine ⟨z, by simpa using hxz, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have hlen : p.length ≤ n := by simpa only [SimpleGraph.Walk.length_cons, Nat.add_le_add_iff_right] using hp.le.trans hd
    exact (SimpleGraph.dist_le p).trans hlen

lemma graph_ball_card_le_geom_sum {X : Type*} [Fintype X] (G : SimpleGraph X)
    (hc : G.Connected) (k : ℕ) (hk : ∀ x, (G.neighborFinset x).card ≤ k)
    (n : ℕ) (x : X) :
    (Finset.univ.filter fun y => G.dist x y ≤ n).card ≤ ∑ j ∈ Finset.range (n + 1), k ^ j := by
  induction n generalizing x with
  | zero =>
    simp only [Nat.zero_add, Finset.sum_range_one, pow_zero]
    apply Finset.card_le_one.mpr
    intro y hy z hz
    have hy' := hc.dist_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (Finset.mem_filter.mp hy).2)
    have hz' := hc.dist_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (Finset.mem_filter.mp hz).2)
    exact hy'.symm.trans hz' 
  | succ n ih =>
    calc
      _ ≤ (insert x ((G.neighborFinset x).biUnion fun z =>
          Finset.univ.filter fun y => G.dist z y ≤ n)).card :=
        Finset.card_le_card (graph_ball_subset_neighbors G hc x n)
      _ ≤ ((G.neighborFinset x).biUnion fun z =>
          Finset.univ.filter fun y => G.dist z y ≤ n).card + 1 := Finset.card_insert_le _ _
      _ ≤ (∑ z ∈ G.neighborFinset x,
          (Finset.univ.filter fun y => G.dist z y ≤ n).card) + 1 :=
        Nat.add_le_add_right (Finset.card_biUnion_le) 1
      _ ≤ (G.neighborFinset x).card * (∑ j ∈ Finset.range (n + 1), k ^ j) + 1 := by
        gcongr
        exact (Finset.sum_le_sum fun z _ => ih z).trans_eq (by simp)
      _ ≤ k * (∑ j ∈ Finset.range (n + 1), k ^ j) + 1 := by gcongr; exact hk x
      _ = _ := by
        rw [Finset.sum_range_succ' (fun j => k ^ j) (n + 1)]
        simp only [pow_succ', ← Finset.mul_sum, pow_zero]

lemma graph_ball_card_le_power {X : Type*} [Fintype X] (G : SimpleGraph X)
    (hc : G.Connected) (k : ℕ) (hk : 2 ≤ k) (hdeg : ∀ x, (G.neighborFinset x).card ≤ k)
    (n : ℕ) (x : X) :
    (Finset.univ.filter fun y => G.dist x y ≤ n).card ≤ k ^ (n + 1) := by
  have hsum : ∀ n : ℕ, (∑ j ∈ Finset.range (n + 1), k ^ j) < k ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa using (show 1 < k by omega)
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ k (n + 1)]
      exact (Nat.add_lt_add_right ih _).trans_le (by
        simpa only [Nat.mul_two] using Nat.mul_le_mul_left (k ^ (n + 1)) hk)
  exact (graph_ball_card_le_geom_sum G hc k hdeg n x).trans (hsum n).le

/-- The source bounded-degree ball estimate, for every nonnegative real radius. -/
theorem graph_ball_card_le_real_power {X : Type*} [Fintype X] (G : SimpleGraph X)
    (hc : G.Connected) (k : ℕ) (hk : 2 ≤ k) (hdeg : ∀ x, (G.neighborFinset x).card ≤ k)
    (x : X) {r : ℝ} (hr : 0 ≤ r) :
    ((Finset.univ.filter fun y => (G.dist x y : ℝ) ≤ r).card : ℝ) ≤ (k : ℝ) ^ (r + 1) := by
  have hs : (Finset.univ.filter fun y => (G.dist x y : ℝ) ≤ r) ⊆
      (Finset.univ.filter fun y => G.dist x y ≤ ⌊r⌋₊) := by
    intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Nat.le_floor_iff hr).mpr (Finset.mem_filter.mp hy).2⟩
  have hcard := (Finset.card_le_card hs).trans (graph_ball_card_le_power G hc k hk hdeg ⌊r⌋₊ x)
  have hcast : ((Finset.univ.filter fun y => (G.dist x y : ℝ) ≤ r).card : ℝ) ≤
      (k : ℝ) ^ (⌊r⌋₊ + 1) := by exact_mod_cast hcard
  refine hcast.trans ?_
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ k by omega))
  push_cast
  linarith [Nat.floor_le hr]

/-- The radius constraint in Eq.mnrn.k.claim ensures the required small ball size. -/
theorem graph_ball_card_le_sqrt {X : Type*} [Fintype X] (G : SimpleGraph X)
    (hc : G.Connected) (k : ℕ) (hk : 2 ≤ k) (hdeg : ∀ x, (G.neighborFinset x).card ≤ k)
    (x : X) {r N : ℝ} (hr : 0 ≤ r) (hN : 0 < N)
    (hsmall : r ≤ Real.log N / (2 * Real.log k)) :
    ((Finset.univ.filter fun y => (G.dist x y : ℝ) ≤ r).card : ℝ) ≤ k * Real.sqrt N := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hk0 : (0 : ℝ) < k := zero_lt_one.trans hk1
  have hlog : 0 < Real.log k := Real.log_pos hk1
  have hp : (k : ℝ) ^ r ≤ Real.sqrt N := by
    rw [Real.rpow_def_of_pos hk0, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hN]
    apply Real.exp_le_exp.mpr
    have hs := (le_div_iff₀ (by positivity : 0 < 2 * Real.log k)).mp hsmall
    nlinarith only [hs]
  calc
    _ ≤ (k : ℝ) ^ (r + 1) := graph_ball_card_le_real_power G hc k hk hdeg x hr
    _ = k * (k : ℝ) ^ r := by rw [Real.rpow_add_one hk0.ne']; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp hk0.le

end DynamicalCStarAlgebras
