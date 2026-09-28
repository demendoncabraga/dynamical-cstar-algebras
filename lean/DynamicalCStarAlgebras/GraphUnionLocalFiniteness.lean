import DynamicalCStarAlgebras.ExpanderGraphs

noncomputable section
open Classical Filter
namespace DynamicalCStarAlgebras

/-- A uniform degree bound makes a coarse disjoint union of finite graphs uniformly
locally finite; the finitely many nearby distinct components contribute a fixed buffer. -/
theorem CoarseGraphUnion.uniformlyLocallyFinite
    {X : Type*} [PseudoMetricSpace X] (D : CoarseGraphUnion X) (k : ℕ)
    (hdeg : ∀ n, letI := @Fintype.ofFinite {x : X // D.component x = n} (D.finite n)
      ∀ x, ((D.graph n).neighborFinset x).card ≤ k) :
    UniformlyLocallyFinite X := by
  let : ∀ n, Fintype {x : X // D.component x = n} :=
    fun n => @Fintype.ofFinite _ (D.finite n)
  intro R hR
  obtain ⟨N, hN⟩ := D.separated (R + 1)
  let F : Set X := ⋃ n ∈ (Finset.range N : Set ℕ), {x | D.component x = n}
  have hF : F.Finite := (Finset.range N).finite_toSet.biUnion
    (fun n _ => @Set.toFinite X {x | D.component x = n} (D.finite n))
  refine ⟨(max k 2) ^ (⌊R⌋₊ + 1) + F.ncard, fun x => ?_⟩
  let z : {y : X // D.component y = D.component x} := ⟨x, rfl⟩
  let A : Finset {y : X // D.component y = D.component x} :=
    Finset.univ.filter fun y => (D.graph (D.component x)).dist z y ≤ ⌊R⌋₊
  let S : Set X := (fun y : {y : X // D.component y = D.component x} => (y : X)) '' (A : Set _)
  have hS : S.Finite := A.finite_toSet.image _
  have hsub : Metric.closedBall x R ⊆ S ∪ F := by
    intro y hy
    have hd : dist x y ≤ R := by simpa only [Metric.mem_closedBall, dist_comm] using hy
    by_cases he : D.component y = D.component x
    · apply Or.inl
      refine ⟨⟨y, he⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      apply (Nat.le_floor_iff hR.le).mpr
      simpa only [z, ← D.dist_eq] using hd
    · apply Or.inr
      have hlt : D.component y < N := by
        by_contra hn
        have hsep := hN x y (Ne.symm he) (by omega)
        linarith
      exact Set.mem_iUnion.mpr ⟨D.component y, Set.mem_iUnion.mpr
        ⟨Finset.mem_range.mpr hlt, rfl⟩⟩
  refine ⟨(hS.union hF).subset hsub, ?_⟩
  calc
    _ ≤ (S ∪ F).ncard := Set.ncard_le_ncard hsub (hS.union hF)
    _ ≤ S.ncard + F.ncard := Set.ncard_union_le S F
    _ ≤ (max k 2) ^ (⌊R⌋₊ + 1) + F.ncard := by
      apply Nat.add_le_add_right
      rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]
      exact graph_ball_card_le_power (D.graph (D.component x)) (D.connected _)
        (max k 2) (Nat.le_max_right _ _) (fun y => (hdeg _ y).trans (Nat.le_max_left _ _)) _ z

end DynamicalCStarAlgebras
