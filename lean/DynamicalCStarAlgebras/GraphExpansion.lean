import DynamicalCStarAlgebras.CompactOffBlock

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

/-- The closed one-step graph neighborhood of a finite vertex set. -/
def graphNeighborhood {X : Type*} [Fintype X] (G : SimpleGraph X) (A : Finset X) : Finset X :=
  Finset.univ.filter fun x => x ∈ A ∨ ∃ y ∈ A, G.Adj y x

/-- The external vertex boundary used in the manuscript's expander definition. -/
def graphBoundary {X : Type*} [Fintype X] (G : SimpleGraph X) (A : Finset X) : Finset X :=
  graphNeighborhood G A \ A

/-- Vertex expansion for every set containing at most half of the vertices. -/
def HasVertexExpansion {X : Type*} [Fintype X] (G : SimpleGraph X) (γ : ℝ) : Prop :=
  ∀ A : Finset X, (A.card : ℝ) ≤ Fintype.card X / 2 →
    γ * A.card ≤ (graphBoundary G A).card

theorem subset_graphNeighborhood {X : Type*} [Fintype X] (G : SimpleGraph X) (A : Finset X) :
    A ⊆ graphNeighborhood G A := by
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, Or.inl hx⟩

/-- Expansion gives a multiplicative increase in the closed neighborhood. -/
theorem HasVertexExpansion.neighborhood_card {X : Type*} [Fintype X] {G : SimpleGraph X}
    {γ : ℝ} (hG : HasVertexExpansion G γ) (A : Finset X)
    (hA : (A.card : ℝ) ≤ Fintype.card X / 2) :
    (1 + γ) * A.card ≤ (graphNeighborhood G A).card := by
  have hc := Finset.card_sdiff_add_card_eq_card (subset_graphNeighborhood G A)
  have he := hG A hA
  dsimp [graphBoundary] at he
  have hcr : ((graphNeighborhood G A \ A).card : ℝ) + A.card = (graphNeighborhood G A).card := by
    exact_mod_cast hc
  nlinarith

/-- Repeated closed neighborhoods. -/
def graphThickening {X : Type*} [Fintype X] (G : SimpleGraph X) (A : Finset X) : ℕ → Finset X
  | 0 => A
  | n + 1 => graphNeighborhood G (graphThickening G A n)

/-- Graph neighborhoods increase with the radius. -/
theorem graphThickening_mono {X : Type*} [Fintype X] (G : SimpleGraph X) (A : Finset X) :
    Monotone (graphThickening G A) :=
  monotone_nat_of_le_succ fun n => subset_graphNeighborhood G (graphThickening G A n)

/-- Until reaching half of the graph, neighborhoods grow at the expansion rate. -/
theorem HasVertexExpansion.thickening_card {X : Type*} [Fintype X] {G : SimpleGraph X}
    {γ : ℝ} (hG : HasVertexExpansion G γ) (hγ : 0 ≤ γ) (A : Finset X) (n : ℕ)
    (hn : ((graphThickening G A n).card : ℝ) ≤ Fintype.card X / 2) :
    (1 + γ) ^ n * A.card ≤ (graphThickening G A n).card := by
  induction n with
  | zero => simp [graphThickening]
  | succ n ih =>
    have hcard : ((graphThickening G A n).card : ℝ) ≤ (graphThickening G A (n + 1)).card := by
      exact_mod_cast Finset.card_le_card (graphThickening_mono G A (Nat.le_succ n))
    have hprev := hcard.trans hn
    have he := hG.neighborhood_card (graphThickening G A n) hprev
    have hi := mul_le_mul_of_nonneg_left (ih hprev) (by positivity : 0 ≤ 1 + γ)
    simpa only [graphThickening, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hi.trans he

/-- Every vertex in an n-step neighborhood is joined to the original set by a short walk. -/
theorem graphThickening_walk {X : Type*} [Fintype X] (G : SimpleGraph X)
    (A : Finset X) (n : ℕ) {x : X} (hx : x ∈ graphThickening G A n) :
    ∃ a ∈ A, ∃ p : G.Walk a x, p.length ≤ n := by
  induction n generalizing x with
  | zero => exact ⟨x, hx, SimpleGraph.Walk.nil, by simp⟩
  | succ n ih =>
    rcases (Finset.mem_filter.mp hx).2 with hx | ⟨y, hy, hxy⟩
    · obtain ⟨a, ha, p, hp⟩ := ih hx
      exact ⟨a, ha, p, hp.trans (Nat.le_succ n)⟩
    · obtain ⟨a, ha, p, hp⟩ := ih hy
      exact ⟨a, ha, p.concat hxy, by simpa only [SimpleGraph.Walk.length_concat] using Nat.add_le_add_right hp 1⟩

/-- Neighborhoods of separated sets remain disjoint until their radii meet. -/
theorem graphThickening_disjoint {X : Type*} [Fintype X] (G : SimpleGraph X)
    (A B : Finset X) (n : ℕ) (hsep : ∀ a ∈ A, ∀ b ∈ B, 2 * n < G.dist a b) :
    Disjoint (graphThickening G A n) (graphThickening G B n) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨a, ha, p, hp⟩ := graphThickening_walk G A n hx
  obtain ⟨b, hb, q, hq⟩ := graphThickening_walk G B n hy
  have ht := SimpleGraph.dist_le (p.append q.reverse)
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] at ht
  have hs := hsep a ha b hb
  omega

/-- Integer-radius separation bounds the smaller relative size by geometric decay. -/
theorem HasVertexExpansion.separated_card {X : Type*} [Fintype X] {G : SimpleGraph X}
    {γ : ℝ} (hG : HasVertexExpansion G γ) (hγ : 0 ≤ γ)
    (A B : Finset X) (n : ℕ) (hsep : ∀ a ∈ A, ∀ b ∈ B, 2 * n < G.dist a b) :
    (1 + γ) ^ n * min (A.card : ℝ) B.card ≤ Fintype.card X / 2 := by
  have hd := graphThickening_disjoint G A B n hsep
  have hsum : ((graphThickening G A n).card : ℝ) + (graphThickening G B n).card ≤ Fintype.card X := by
    exact_mod_cast (show (graphThickening G A n).card + (graphThickening G B n).card ≤ Fintype.card X from
      (Finset.card_union_of_disjoint hd).symm.trans_le (Finset.card_le_univ _))
  have hor : ((graphThickening G A n).card : ℝ) ≤ Fintype.card X / 2 ∨
      ((graphThickening G B n).card : ℝ) ≤ Fintype.card X / 2 := by
    by_contra hn
    push Not at hn
    linarith
  rcases hor with hA | hB
  · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans
      ((hG.thickening_card hγ A n hA).trans hA)
  · exact (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)).trans
      ((hG.thickening_card hγ B n hB).trans hB)

end DynamicalCStarAlgebras
