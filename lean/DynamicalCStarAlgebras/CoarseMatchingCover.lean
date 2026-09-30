import DynamicalCStarAlgebras.PartialTranslationPartition
import Mathlib.Data.Nat.Pairing

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- A sequence of partial bijections covering every metric entourage in finitely
many levels. Each level controls the original distance by its index. -/
structure CoarseMatchingCover (X : Type*) [PseudoMetricSpace X] where
  relation : ℕ → Set (X × X)
  partialBijection : ∀ n, IsPartialBijection (relation n)
  distance_le : ∀ n x y, (x, y) ∈ relation n → dist x y ≤ n
  covers : ∀ R : ℝ, ∃ N : ℕ, ∀ x y, dist x y ≤ R →
    ∃ n ≤ N, (x, y) ∈ relation n

/-- Uniform local finiteness supplies a countable, quantitatively controlled
cover by partial bijections. -/
theorem exists_coarseMatchingCover {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) : Nonempty (CoarseMatchingCover X) := by
  have hC := coarse_uniformlyLocallyFinite_iff.mpr hX
  have hp (r : ℕ) := controlled_relation_partial_bijection_partition
    (CoarseStructure.ofPseudoMetric X) hC {p | dist p.1 p.2 ≤ (r : ℝ)}
    ⟨r, fun _ h => h⟩
  choose N F hF using hp
  let I := Σ r : ℕ, Fin (N r) × Fin (N r)
  let code (i : I) := Nat.pair i.1 (Nat.pair i.2.1.val i.2.2.val)
  have hinj : Function.Injective code := by
    rintro ⟨r, i⟩ ⟨s, j⟩ h
    have h₁ := Nat.pair_eq_pair.mp h
    dsimp only at h₁
    obtain rfl := h₁.1
    have h₂ := Nat.pair_eq_pair.mp h₁.2
    have hij : i = j := Prod.ext (Fin.ext h₂.1) (Fin.ext h₂.2)
    exact congrArg (Sigma.mk r) hij
  let E (n : ℕ) : Set (X × X) := {p | ∃ i : I, code i = n ∧ p ∈ F i.1 i.2}
  refine ⟨{ relation := E, partialBijection := ?_, distance_le := ?_, covers := ?_ }⟩
  · intro n
    constructor
    · rintro ⟨p, i, hi, hp⟩ ⟨q, j, hj, hq⟩ h
      have hij := hinj (hi.trans hj.symm)
      subst j
      exact Subtype.ext (congrArg (fun z : F i.1 i.2 => z.val)
        (@((hF i.1).2.2 i.2).1.1 ⟨p, hp⟩ ⟨q, hq⟩ h))
    · rintro ⟨p, i, hi, hp⟩ ⟨q, j, hj, hq⟩ h
      have hij := hinj (hi.trans hj.symm)
      subst j
      exact Subtype.ext (congrArg (fun z : F i.1 i.2 => z.val)
        (@((hF i.1).2.2 i.2).1.2 ⟨p, hp⟩ ⟨q, hq⟩ h))
  · rintro n x y ⟨i, hi, hp⟩
    have hd : dist x y ≤ (i.1 : ℝ) := by
      have hm := Set.mem_iUnion.mpr ⟨i.2, hp⟩
      rw [(hF i.1).1] at hm
      exact hm
    have hn : i.1 ≤ n := hi ▸ Nat.left_le_pair i.1 (Nat.pair i.2.1.val i.2.2.val)
    exact hd.trans (Nat.cast_le.mpr hn)
  · intro R
    obtain ⟨r, hr⟩ := exists_nat_ge R
    refine ⟨Finset.univ.sup (fun i : Fin (N r) × Fin (N r) => code ⟨r, i⟩), ?_⟩
    intro x y hxy
    have hm : (x, y) ∈ ⋃ i, F r i := by
      rw [(hF r).1]
      exact hxy.trans hr
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hm
    exact ⟨code ⟨r, i⟩, Finset.le_sup (f := fun i => code ⟨r, i⟩) (Finset.mem_univ i), ⟨⟨r, i⟩, rfl, hi⟩⟩

end DynamicalCStarAlgebras
