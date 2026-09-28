import DynamicalCStarAlgebras.OffBlockRemainder

noncomputable section

namespace DynamicalCStarAlgebras

/-- A countable partition into finite connected graphs with the metric and separation
conditions in the manuscript's definition of a coarse disjoint union. -/
structure CoarseGraphUnion (X : Type*) [PseudoMetricSpace X] where
  component : X → ℕ
  finite : ∀ n, Finite {x : X // component x = n}
  graph : ∀ n, SimpleGraph {x : X // component x = n}
  connected : ∀ n, (graph n).Connected
  dist_eq : ∀ n (x y : {x : X // component x = n}),
    dist (x : X) (y : X) = ((graph n).dist x y : ℝ)
  separated : ∀ r : ℝ, ∃ N : ℕ, ∀ x y : X,
    component x ≠ component y → N ≤ component x + component y → r ≤ dist x y

/-- Outside finitely many vertices, all distinct components are uniformly separated. -/
theorem CoarseGraphUnion.finite_separation {X : Type*} [PseudoMetricSpace X]
    (D : CoarseGraphUnion X) (r : ℝ) :
    ∃ F : Set X, F.Finite ∧
      ∀ x ∉ F, ∀ y ∉ F, D.component x ≠ D.component y → r ≤ dist x y := by
  classical
  obtain ⟨N, hN⟩ := D.separated r
  let F : Set X := ⋃ n ∈ (Finset.range N : Set ℕ), {x | D.component x = n}
  have hfiber (n : ℕ) : Set.Finite {x : X | D.component x = n} := by
    exact @Set.toFinite X {x | D.component x = n} (D.finite n)
  refine ⟨F, (Finset.range N).finite_toSet.biUnion (fun n _ => hfiber n), ?_⟩
  intro x hx y _ hxy
  apply hN x y hxy
  have hnx : N ≤ D.component x := by
    by_contra hn
    apply hx
    exact Set.mem_iUnion.mpr ⟨D.component x, Set.mem_iUnion.mpr
      ⟨Finset.mem_range.mpr (by omega), rfl⟩⟩
  omega

end DynamicalCStarAlgebras
