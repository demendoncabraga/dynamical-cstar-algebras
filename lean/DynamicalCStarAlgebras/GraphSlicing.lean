import DynamicalCStarAlgebras.FiniteHeightSlicing
import Mathlib.Combinatorics.SimpleGraph.Metric

noncomputable section

namespace DynamicalCStarAlgebras

/-- The shortest-path metric of a connected graph, with natural distances cast to real numbers. -/
@[instance_reducible] def connectedGraphMetric {X : Type*} (G : SimpleGraph X) (hG : G.Connected) : MetricSpace X where
  dist x y := (G.dist x y : ℝ)
  dist_self x := by simp
  dist_comm x y := by rw [G.dist_comm]
  dist_triangle x y z := by exact_mod_cast (hG.dist_triangle (u := x) (v := y) (w := z))
  eq_of_dist_eq_zero {x y} h := hG.dist_eq_zero_iff.mp (by exact_mod_cast h)

/-- The least Lipschitz constant on a finite metric space. -/
def finiteLipschitzConstant {X : Type*} [MetricSpace X] [Fintype X] (h : X → ℝ) : NNReal :=
  Finset.univ.sup (fun p : X × X => nndist (h p.1) (h p.2) / nndist p.1 p.2)

/-- The finite Lipschitz constant is attained as a bound and is no larger than any other bound. -/
theorem finiteLipschitzConstant_spec {X : Type*} [MetricSpace X] [Fintype X] (h : X → ℝ) :
    LipschitzWith (finiteLipschitzConstant h) h ∧
      ∀ L : NNReal, LipschitzWith L h → finiteLipschitzConstant h ≤ L := by
  constructor
  · rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    by_cases he : x = y
    · simp [he]
    · have hd : 0 < nndist x y := pos_iff_ne_zero.mpr (nndist_eq_zero.not.mpr he)
      have hn := (div_le_iff₀ hd).mp (Finset.le_sup (f := fun p : X × X =>
        nndist (h p.1) (h p.2) / nndist p.1 p.2) (Finset.mem_univ (x, y)))
      exact_mod_cast hn
  · intro L hL
    apply Finset.sup_le
    intro p _
    by_cases he : p.1 = p.2
    · simp [he]
    · exact (div_le_iff₀ (pos_iff_ne_zero.mpr (nndist_eq_zero.not.mpr he))).mpr (by exact_mod_cast hL.dist_le_mul p.1 p.2)

/-- Lemma IterSlicing with the least Lipschitz constant in the shortest-path metric. -/
theorem graph_slicing_estimate {X : Type*} [Fintype X] (G : SimpleGraph X) (hG : G.Connected)
    (h : X → ℝ) :
    letI := connectedGraphMetric G hG
    ∀ (a : Operator X) (k : ℕ), 0 < k →
      ‖(diagonalCommutator (finiteRealDiagonal h))^[k] a‖ ≤
        2 * (3 * (finiteLipschitzConstant h : ℝ)) ^ k *
          (‖a‖ + ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ k * quasiLocalModulus a (n + 2)) := by
  let inst : MetricSpace X := connectedGraphMetric G hG
  exact fun a k hk => finite_integer_slicing_estimate
    (fun x y => ⟨G.dist x y, rfl⟩) h (finiteLipschitzConstant_spec h).1 a k hk

end DynamicalCStarAlgebras
