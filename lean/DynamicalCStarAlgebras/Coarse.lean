import Mathlib

/-! Coarse structures and the largest substructure controlling a real-valued map.
The conventions are those of Section 2 and Definition 4.1 of the manuscript.
-/

namespace DynamicalCStarAlgebras

universe u

/-- The five entourage axioms from Section 2.1; no connectedness is imposed. -/
structure CoarseStructure (X : Type u) where
  controlled : Set (Set (X × X))
  diagonal : {p | p.1 = p.2} ∈ controlled
  subset : ∀ {E F}, E ⊆ F → F ∈ controlled → E ∈ controlled
  union : ∀ {E F}, E ∈ controlled → F ∈ controlled → E ∪ F ∈ controlled
  inverse : ∀ {E}, E ∈ controlled → {p | (p.2, p.1) ∈ E} ∈ controlled
  comp : ∀ {E F}, E ∈ controlled → F ∈ controlled →
    {p | ∃ z, (p.1, z) ∈ E ∧ (z, p.2) ∈ F} ∈ controlled

/-- Finite oscillation on an entourage, expressed without an unbounded real supremum. -/
def BoundedVariation {X : Type u} (h : X → ℝ) (E : Set (X × X)) : Prop :=
  ∃ R : ℝ, ∀ p ∈ E, dist (h p.1) (h p.2) ≤ R

/-- The manuscript's coarse maps into the usual real line. -/
def IsCoarseReal {X : Type u} (C : CoarseStructure X) (h : X → ℝ) : Prop :=
  ∀ E ∈ C.controlled, BoundedVariation h E

/-- Inclusion of coarse structures. -/
def CoarseStructure.IsSubstructure {X : Type u} (C D : CoarseStructure X) : Prop :=
  C.controlled ⊆ D.controlled

theorem BoundedVariation.diagonal {X : Type u} (h : X → ℝ) :
    BoundedVariation h {p : X × X | p.1 = p.2} :=
  ⟨0, fun _ hp => le_of_eq (dist_eq_zero.mpr (congrArg h hp))⟩

theorem BoundedVariation.subset {X : Type u} {h : X → ℝ} {E F : Set (X × X)}
    (hF : BoundedVariation h F) (hEF : E ⊆ F) : BoundedVariation h E :=
  hF.imp fun _ hR p hp => hR p (hEF hp)

theorem BoundedVariation.union {X : Type u} {h : X → ℝ} {E F : Set (X × X)}
    (hE : BoundedVariation h E) (hF : BoundedVariation h F) :
    BoundedVariation h (E ∪ F) :=
  hE.elim fun R hR => hF.elim fun S hS =>
    ⟨max R S, fun p hp => hp.elim
      (fun he => (hR p he).trans (le_max_left R S))
      (fun hf => (hS p hf).trans (le_max_right R S))⟩

theorem BoundedVariation.inverse {X : Type u} {h : X → ℝ} {E : Set (X × X)}
    (hE : BoundedVariation h E) : BoundedVariation h {p | (p.2, p.1) ∈ E} :=
  hE.imp fun _ hR p hp => (dist_comm (h p.1) (h p.2)) ▸ hR (p.2, p.1) hp

theorem BoundedVariation.comp {X : Type u} {h : X → ℝ} {E F : Set (X × X)}
    (hE : BoundedVariation h E) (hF : BoundedVariation h F) :
    BoundedVariation h {p | ∃ z, (p.1, z) ∈ E ∧ (z, p.2) ∈ F} :=
  hE.elim fun R hR => hF.elim fun S hS =>
    ⟨R + S, fun p hp => hp.elim fun z hz =>
      (dist_triangle (h p.1) (h z) (h p.2)).trans
        (add_le_add (hR (p.1, z) hz.1) (hS (z, p.2) hz.2))⟩

/-- Definition `Definition.Eh.largest.coarse.substructure`. -/
def CoarseStructure.restrictReal {X : Type u} (C : CoarseStructure X) (h : X → ℝ) :
    CoarseStructure X where
  controlled := {E | E ∈ C.controlled ∧ BoundedVariation h E}
  diagonal := ⟨C.diagonal, BoundedVariation.diagonal h⟩
  subset hEF hF := ⟨C.subset hEF hF.1, hF.2.subset hEF⟩
  union hE hF := ⟨C.union hE.1 hF.1, hE.2.union hF.2⟩
  inverse hE := ⟨C.inverse hE.1, hE.2.inverse⟩
  comp hE hF := ⟨C.comp hE.1 hF.1, hE.2.comp hF.2⟩

/-- Proposition `PropLargestCoarseStrucWithhCoarse`, including all three assertions. -/
theorem CoarseStructure.restrictReal_largest {X : Type u}
    (C : CoarseStructure X) (h : X → ℝ) :
    (C.restrictReal h).IsSubstructure C ∧
      IsCoarseReal (C.restrictReal h) h ∧
      ∀ D : CoarseStructure X, D.IsSubstructure C → IsCoarseReal D h →
        D.IsSubstructure (C.restrictReal h) :=
  ⟨fun _ hE => hE.1, fun _ hE => hE.2,
    fun _ hDC hh E hE => ⟨hDC hE, hh E hE⟩⟩

/-- The bounded-distance coarse structure of a pseudometric space (Section 2.1). -/
def CoarseStructure.ofPseudoMetric (X : Type u) [PseudoMetricSpace X] :
    CoarseStructure X where
  controlled := {E | ∃ R : ℝ, ∀ p ∈ E, dist p.1 p.2 ≤ R}
  diagonal := ⟨0, fun p hp => le_of_eq
    ((congrArg (fun x => dist x p.2) hp).trans (dist_self p.2))⟩
  subset hEF hF := hF.imp fun _ hR p hp => hR p (hEF hp)
  union hE hF := hE.elim fun R hR => hF.elim fun S hS =>
    ⟨max R S, fun p hp => hp.elim
      (fun he => (hR p he).trans (le_max_left R S))
      (fun hf => (hS p hf).trans (le_max_right R S))⟩
  inverse hE := hE.imp fun _ hR p hp => (dist_comm p.1 p.2) ▸ hR (p.2, p.1) hp
  comp hE hF := hE.elim fun R hR => hF.elim fun S hS =>
    ⟨R + S, fun p hp => hp.elim fun z hz =>
      (dist_triangle p.1 z p.2).trans
        (add_le_add (hR (p.1, z) hz.1) (hS (z, p.2) hz.2))⟩

/-- The pseudometric induced by an arbitrary real-valued map, with no injectivity. -/
abbrev realPullbackPseudoMetric {X : Type u} (h : X → ℝ) : PseudoMetricSpace X :=
  PseudoMetricSpace.induced h inferInstance

/-- The distance convention in the introduction and Section 3. -/
theorem realPullbackPseudoMetric_dist {X : Type u} (h : X → ℝ) (x y : X) :
    @dist X (realPullbackPseudoMetric h).toDist x y = |h x - h y| :=
  Real.dist_eq (h x) (h y)

/-- Coarse maps send every controlled relation to a controlled relation (Section 2.1). -/
def IsCoarseMap {X : Type u} {Y : Type*} (C : CoarseStructure X)
    (D : CoarseStructure Y) (f : X → Y) : Prop :=
  ∀ E ∈ C.controlled, (fun p : X × X => (f p.1, f p.2)) '' E ∈ D.controlled

/-- The bounded-oscillation definition agrees with the general definition for real targets. -/
theorem isCoarseReal_iff {X : Type u} (C : CoarseStructure X) (h : X → ℝ) :
    IsCoarseReal C h ↔ IsCoarseMap C (CoarseStructure.ofPseudoMetric ℝ) h :=
  ⟨fun hh E hE => (hh E hE).imp fun _ hR _ hq =>
      hq.elim fun p hp => hp.2 ▸ hR p hp.1,
    fun hh E hE => (hh E hE).imp fun _ hR p hp =>
      hR (h p.1, h p.2) ⟨p, hp, rfl⟩⟩

end DynamicalCStarAlgebras
