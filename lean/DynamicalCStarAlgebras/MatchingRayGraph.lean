import DynamicalCStarAlgebras.CoarseMatchingCover
import Mathlib.Combinatorics.SimpleGraph.Metric

noncomputable section
open Classical
namespace DynamicalCStarAlgebras
namespace CoarseMatchingCover

variable {X : Type*} [PseudoMetricSpace X]

/-- One matching joins an even port on one ray to an odd port on another. -/
def horizontal (M : CoarseMatchingCover X) (a b : X × ℕ) : Prop :=
  ∃ n, a.2 = 2 * n ∧ b.2 = 2 * n + 1 ∧ (a.1, b.1) ∈ M.relation n

/-- Rays joined by level matchings. Each vertex has at most two vertical
neighbors and one horizontal neighbor. -/
def graph (M : CoarseMatchingCover X) : SimpleGraph (X × ℕ) where
  Adj a b := (a.1 = b.1 ∧ (a.2 + 1 = b.2 ∨ b.2 + 1 = a.2)) ∨
    M.horizontal a b ∨ M.horizontal b a
  symm := ⟨by
    rintro a b (h | h | h)
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨by
    rintro a (h | h | h)
    · omega
    · obtain ⟨n, h⟩ := h
      omega
    · obtain ⟨n, h⟩ := h
      omega⟩

/-- A port participates in at most one horizontal edge. -/
theorem horizontal_neighbors_subsingleton (M : CoarseMatchingCover X) (a : X × ℕ) :
    {b | M.horizontal a b ∨ M.horizontal b a}.Subsingleton := by
  rintro b hb c hc
  rcases hb with ⟨n, hn, hb, hp⟩ | ⟨n, hb, hn, hp⟩
  · rcases hc with ⟨m, hm, hc, hq⟩ | ⟨m, hc, hm, hq⟩
    · have hnm : n = m := by omega
      subst m
      have he := (M.partialBijection n).1 (a₁ := ⟨(a.1, b.1), hp⟩)
        (a₂ := ⟨(a.1, c.1), hq⟩) rfl
      exact Prod.ext (congrArg (fun z : M.relation n => z.val.2) he) (by omega)
    · omega
  · rcases hc with ⟨m, hm, hc, hq⟩ | ⟨m, hc, hm, hq⟩
    · omega
    · have hnm : n = m := by omega
      subst m
      have he := (M.partialBijection n).2 (a₁ := ⟨(b.1, a.1), hp⟩)
        (a₂ := ⟨(c.1, a.1), hq⟩) rfl
      exact Prod.ext (congrArg (fun z : M.relation n => z.val.1) he) (by omega)

/-- The ray construction has degree at most three, including coincident
vertical and horizontal edges. -/
theorem neighbor_bound (M : CoarseMatchingCover X) (a : X × ℕ) :
    (M.graph.neighborSet a).Finite ∧ (M.graph.neighborSet a).ncard ≤ 3 := by
  let H := {b | M.horizontal a b ∨ M.horizontal b a}
  have hh : H.Subsingleton := M.horizontal_neighbors_subsingleton a
  let S := insert (a.1, a.2 + 1) (insert (a.1, a.2 - 1) H)
  have hf : S.Finite := (hh.finite.insert _).insert _
  have hsub : M.graph.neighborSet a ⊆ S := by
    intro b hb
    rcases hb with ⟨he, hv | hv⟩ | hh
    · exact Or.inl (Prod.ext he.symm hv.symm)
    · exact Or.inr (Or.inl (Prod.ext he.symm (by omega)))
    · exact Or.inr (Or.inr hh)
  refine ⟨hf.subset hsub, (Set.ncard_le_ncard hsub hf).trans ?_⟩
  have h₁ := Set.ncard_insert_le (a.1, a.2 + 1) (insert (a.1, a.2 - 1) H)
  have h₂ := Set.ncard_insert_le (a.1, a.2 - 1) H
  have h₃ : H.ncard ≤ 1 := (Set.ncard_le_one hh.finite).mpr hh
  change S.ncard ≤ 3
  dsimp only [S] at *
  omega

/-- The vertical ray gives a walk of exactly the prescribed height. -/
theorem ray_walk (M : CoarseMatchingCover X) (x : X) (n : ℕ) :
    ∃ p : M.graph.Walk (x, 0) (x, n), p.length = n := by
  induction n with
  | zero => exact ⟨.nil, rfl⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    have he : M.graph.Adj (x, n) (x, n + 1) := Or.inl ⟨rfl, Or.inl rfl⟩
    exact ⟨p.append (.cons he .nil), by simp [hp]⟩

/-- A matching at level n gives a uniformly short walk between the ray roots. -/
theorem matching_walk (M : CoarseMatchingCover X) {x y : X} {n : ℕ}
    (h : (x, y) ∈ M.relation n) :
    ∃ p : M.graph.Walk (x, 0) (y, 0), p.length = 4 * n + 2 := by
  obtain ⟨p, hp⟩ := M.ray_walk x (2 * n)
  obtain ⟨q, hq⟩ := M.ray_walk y (2 * n + 1)
  have he : M.graph.Adj (x, 2 * n) (y, 2 * n + 1) := Or.inr (Or.inl ⟨n, rfl, rfl, h⟩)
  refine ⟨p.append (.cons he q.reverse), ?_⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
    SimpleGraph.Walk.length_reverse, hp, hq]
  omega

/-- Every pair of roots is joined because the matching cover covers all distances. -/
theorem connected (M : CoarseMatchingCover X) [Nonempty X] : M.graph.Connected := by
  refine { preconnected := ?_, nonempty := inferInstance }
  intro a b
  obtain ⟨N, hN⟩ := M.covers (dist a.1 b.1)
  obtain ⟨n, _, hn⟩ := hN a.1 b.1 le_rfl
  obtain ⟨p, _⟩ := M.matching_walk hn
  obtain ⟨q, _⟩ := M.ray_walk a.1 a.2
  obtain ⟨r, _⟩ := M.ray_walk b.1 b.2
  exact ⟨q.reverse.append (p.append r)⟩

/-- One graph edge changes height by at most one and has controlled displacement
in the original metric. -/
theorem adj_bounds (M : CoarseMatchingCover X) {a b : X × ℕ} (h : M.graph.Adj a b) :
    dist a.1 b.1 ≤ (a.2 : ℝ) + 1 ∧ b.2 ≤ a.2 + 1 := by
  rcases h with ⟨he, hv⟩ | ⟨n, ha, hb, hp⟩ | ⟨n, hb, ha, hp⟩
  · exact ⟨by simp [he]; positivity, by omega⟩
  · refine ⟨(M.distance_le n _ _ hp).trans ?_, by omega⟩
    exact_mod_cast (show n ≤ a.2 + 1 by omega)
  · refine ⟨?_, by omega⟩
    rw [dist_comm]
    exact (M.distance_le n _ _ hp).trans (by exact_mod_cast (show n ≤ a.2 + 1 by omega))

/-- Original displacement is bounded by walk length and initial height. -/
theorem walk_displacement (M : CoarseMatchingCover X) {a b : X × ℕ}
    (p : M.graph.Walk a b) :
    dist a.1 b.1 ≤ (p.length : ℝ) * ((a.2 : ℝ) + p.length) := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    obtain ⟨hd, hh⟩ := M.adj_bounds hab
    have hh' : (b.2 : ℝ) ≤ (a.2 : ℝ) + 1 := by exact_mod_cast hh
    have hm := mul_le_mul_of_nonneg_left hh' (Nat.cast_nonneg p.length : (0 : ℝ) ≤ p.length)
    have ht := dist_triangle a.1 b.1 c.1
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- Graph distance between roots controls the original metric. -/
theorem root_distance_lower (M : CoarseMatchingCover X) [Nonempty X] (x y : X) :
    dist x y ≤ (M.graph.dist (x, 0) (y, 0) : ℝ) ^ 2 := by
  obtain ⟨p, hp⟩ := M.connected.exists_walk_length_eq_dist (x, 0) (y, 0)
  have h := M.walk_displacement p
  simpa [hp, pow_two] using h

/-- Bounded original distances give uniformly bounded graph distances between roots. -/
theorem root_distance_upper (M : CoarseMatchingCover X) (R : ℝ) :
    ∃ N : ℕ, ∀ x y, dist x y ≤ R → M.graph.dist (x, 0) (y, 0) ≤ N := by
  obtain ⟨N, hN⟩ := M.covers R
  refine ⟨4 * N + 2, ?_⟩
  intro x y hxy
  obtain ⟨n, hn, he⟩ := hN x y hxy
  obtain ⟨p, hp⟩ := M.matching_walk he
  have hd := M.graph.dist_le p
  omega

end CoarseMatchingCover
end DynamicalCStarAlgebras
