import DynamicalCStarAlgebras.CoarseLocalFiniteness

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- A relation which is the graph of a bijection between two subsets. Matrix
coordinates are ordered as target, source. -/
def IsPartialBijection {X : Type*} (E : Set (X × X)) : Prop :=
  Function.Injective (fun p : E => p.val.1) ∧ Function.Injective (fun p : E => p.val.2)

/-- Every controlled relation on a uniformly locally finite coarse space is a
finite disjoint union of controlled partial bijections. The pair of finite
row/column labels gives N^2 colors; no optimal edge-coloring theorem is required. -/
theorem controlled_relation_partial_bijection_partition {X : Type*} (C : CoarseStructure X)
    (hC : C.UniformlyLocallyFinite) (E : Set (X × X)) (hE : E ∈ C.controlled) :
    ∃ (N : ℕ) (F : Fin N × Fin N → Set (X × X)),
      (⋃ i, F i) = E ∧ Pairwise (fun i j => Disjoint (F i) (F j)) ∧
      ∀ i, IsPartialBijection (F i) ∧ F i ∈ C.controlled := by
  obtain ⟨R, hR⟩ := hC.fiber_bounds hE
  obtain ⟨S, hS⟩ := hC.fiber_bounds (C.inverse hE)
  let N := max R S
  have hr (x : X) : Nonempty ({y | (x, y) ∈ E} ↪ Fin N) := by
    let := (hR x).1.fintype
    apply Function.Embedding.nonempty_of_card_le
    simpa only [Fintype.card_fin, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Nat.card_fin, N] using
      (hR x).2.trans (le_max_left R S)
  have hc (y : X) : Nonempty ({x | (x, y) ∈ E} ↪ Fin N) := by
    have hs : {x | (x, y) ∈ E}.Finite ∧ {x | (x, y) ∈ E}.ncard ≤ S := hS y
    let := hs.1.fintype
    apply Function.Embedding.nonempty_of_card_le
    simpa only [Fintype.card_fin, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Nat.card_fin, N] using
      hs.2.trans (le_max_right R S)
  let ir (x : X) := Classical.choice (hr x)
  let ic (y : X) := Classical.choice (hc y)
  let F (i : Fin N × Fin N) : Set (X × X) :=
    {p | ∃ hp : p ∈ E, (ir p.1 ⟨p.2, hp⟩, ic p.2 ⟨p.1, hp⟩) = i}
  have hFE (i : Fin N × Fin N) : F i ⊆ E := fun _ hp => hp.choose
  refine ⟨N, F, ?_, ?_, ?_⟩
  · ext p
    constructor
    · intro hp
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
      exact hFE i hi
    · intro hp
      exact Set.mem_iUnion.mpr ⟨(ir p.1 ⟨p.2, hp⟩, ic p.2 ⟨p.1, hp⟩), hp, rfl⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro p hpi hpj
    obtain ⟨hp, hi⟩ := hpi
    obtain ⟨_, hj⟩ := hpj
    exact hij (hi.symm.trans hj)
  · intro i
    refine ⟨⟨?_, ?_⟩, C.subset (hFE i) hE⟩
    · rintro ⟨⟨x, y⟩, hp⟩ ⟨⟨x', y'⟩, hq⟩ he
      change x = x' at he
      subst x'
      obtain ⟨hpE, hpI⟩ := hp
      obtain ⟨hqE, hqI⟩ := hq
      apply Subtype.ext
      change (x, y) = (x, y')
      exact congrArg (fun z => (x, z)) (congrArg Subtype.val
        ((ir x).injective (congrArg Prod.fst (hpI.trans hqI.symm))))
    · rintro ⟨⟨x, y⟩, hp⟩ ⟨⟨x', y'⟩, hq⟩ he
      change y = y' at he
      subst y'
      obtain ⟨hpE, hpI⟩ := hp
      obtain ⟨hqE, hqI⟩ := hq
      apply Subtype.ext
      change (x, y) = (x', y)
      exact congrArg (fun z => (z, y)) (congrArg Subtype.val
        ((ic y).injective (congrArg Prod.snd (hpI.trans hqI.symm))))

end DynamicalCStarAlgebras
