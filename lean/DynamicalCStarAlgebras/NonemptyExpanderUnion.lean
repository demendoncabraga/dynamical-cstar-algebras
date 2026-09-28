import DynamicalCStarAlgebras.ExpanderGraphUnion

noncomputable section
open Classical Filter
namespace DynamicalCStarAlgebras

lemma component_range_infinite_of_card_tendsto {X : Type*} (π : X → ℕ)
    (hcard : Tendsto (fun n => (Nat.card {x : X // π x = n} : ℝ)) atTop atTop) :
    (Set.range π).Infinite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_atTop.mp hcard) 1)
  apply (Set.Ici_infinite N).mono
  intro n hn
  have hc : 0 < Nat.card {x : X // π x = n} := by
    have hh := hN n hn
    exact_mod_cast (show (0 : ℝ) < Nat.card {x : X // π x = n} by linarith)
  obtain ⟨x⟩ := (Nat.card_pos_iff.mp hc).1
  exact ⟨x.val, x.property⟩

lemma vertexExpansion_iso {X Y : Type*} [Fintype X] [Fintype Y]
    {G : SimpleGraph X} {H : SimpleGraph Y} (e : G ≃g H) {γ : ℝ}
    (hG : HasVertexExpansion G γ) : HasVertexExpansion H γ := by
  intro B hB
  let A := B.image e.symm
  have hA : A.card = B.card := Finset.card_image_of_injective _ e.symm.injective
  have hab : (graphBoundary G A).image e = graphBoundary H B := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    have hxA (z : X) : z ∈ A ↔ e z ∈ B := by
      constructor
      · rintro hz
        obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hz
        rw [← he, e.apply_symm_apply]
        exact ha
      · intro hz
        exact Finset.mem_image.mpr ⟨e z, hz, e.symm_apply_apply z⟩
    simp only [Finset.mem_image, graphBoundary, Finset.mem_sdiff, graphNeighborhood,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨z, ⟨hz | ⟨w, hw, hzw⟩, hzn⟩, hzx⟩
      · exact False.elim (hzn hz)
      · have hz : z = x := e.injective hzx
        subst z
        exact ⟨Or.inr ⟨e w, (hxA w).mp hw, e.map_rel_iff.mpr hzw⟩, fun hx => hzn ((hxA x).mpr hx)⟩
    · rintro ⟨hx | ⟨w, hw, hwx⟩, hxn⟩
      · exact False.elim (hxn hx)
      · refine ⟨x, ⟨Or.inr ⟨e.symm w, ?_, ?_⟩, fun hx => hxn ((hxA x).mp hx)⟩, rfl⟩
        · simp only [A, Finset.mem_image]
          exact ⟨w, hw, rfl⟩
        · simpa using e.symm.map_rel_iff.mpr hwx
  have hb := hG A (by simpa only [hA, Fintype.card_congr e.toEquiv] using hB)
  rw [hA, ← hab, Finset.card_image_of_injective _ e.injective] at *
  exact hb

lemma graphIso_dist_eq {X Y : Type*} {G : SimpleGraph X} {H : SimpleGraph Y}
    (e : G ≃g H) (hG : G.Preconnected) (x y : X) : H.dist (e x) (e y) = G.dist x y := by
  have hH := e.preconnected_iff.mp hG
  apply Nat.le_antisymm
  · obtain ⟨p, hp⟩ := (hG x y).exists_walk_length_eq_dist
    exact (H.dist_le (p.map e.toHom)).trans_eq ((p.length_map e.toHom).trans hp)
  · obtain ⟨p, hp⟩ := (hH (e x) (e y)).exists_walk_length_eq_dist
    have ht := G.dist_le (p.map e.symm.toHom)
    change G.dist (e.symm (e x)) (e.symm (e y)) ≤ (p.map e.symm.toHom).length at ht
    simpa only [e.symm_apply_apply, p.length_map e.symm.toHom, hp] using ht

/-- Increasing enumeration of exactly the occupied component labels. -/
def occupiedComponentOrder {X : Type*} (π : X → ℕ) (hπ : (Set.range π).Infinite) :
    ℕ ≃o Set.range π :=
  letI := hπ.to_subtype
  Nat.Subtype.orderIsoOfNat (Set.range π)

/-- Relabeling the occupied components leaves the underlying space unchanged. -/
def occupiedComponent {X : Type*} (π : X → ℕ) (hπ : (Set.range π).Infinite) (x : X) : ℕ :=
  (occupiedComponentOrder π hπ).symm ⟨π x, Set.mem_range_self x⟩

lemma occupiedComponentOrder_component {X : Type*} (π : X → ℕ) (hπ : (Set.range π).Infinite) (x : X) :
    (occupiedComponentOrder π hπ (occupiedComponent π hπ x)).val = π x := by
  simp only [occupiedComponent, OrderIso.apply_symm_apply]

lemma occupiedComponent_fiber_iff {X : Type*} (π : X → ℕ) (hπ : (Set.range π).Infinite)
    (n : ℕ) (x : X) :
    occupiedComponent π hπ x = n ↔ π x = (occupiedComponentOrder π hπ n).val := by
  constructor
  · intro hx
    rw [← occupiedComponentOrder_component π hπ x, hx]
  · intro hx
    apply (occupiedComponentOrder π hπ).injective
    exact Subtype.ext ((occupiedComponentOrder_component π hπ x).trans hx)

def occupiedComponentFiberEquiv {X : Type*} (π : X → ℕ) (hπ : (Set.range π).Infinite) (n : ℕ) :
    {x : X // occupiedComponent π hπ x = n} ≃
      {x : X // π x = (occupiedComponentOrder π hπ n).val} :=
  Equiv.subtypeEquivRight (occupiedComponent_fiber_iff π hπ n)

lemma occupiedComponent_surjective {X : Type*} (π : X → ℕ) (hπ : (Set.range π).Infinite) :
    Function.Surjective (occupiedComponent π hπ) := by
  intro n
  obtain ⟨x, hx⟩ := (occupiedComponentOrder π hπ n).property
  exact ⟨x, (occupiedComponent_fiber_iff π hπ n x).mpr hx⟩

/-- The literal expander-union data from the manuscript; empty components are permitted. -/
structure ExpanderGraphUnionData (X : Type*) [PseudoMetricSpace X] where
  component : X → ℕ
  finite : ∀ n, Finite {x : X // component x = n}
  graph : ∀ n, SimpleGraph {x : X // component x = n}
  dist_eq : ∀ n (x y : {x : X // component x = n}),
    dist (x : X) (y : X) = ((graph n).dist x y : ℝ)
  separated : ∀ r : ℝ, ∃ N : ℕ, ∀ x y : X,
    component x ≠ component y → N ≤ component x + component y → r ≤ dist x y
  degreeBound : ℕ
  degree_le : ∀ n, letI := @Fintype.ofFinite {x : X // component x = n} (finite n)
    ∀ x, ((graph n).neighborFinset x).card ≤ degreeBound
  expansionConstant : ℝ
  expansion_pos : 0 < expansionConstant
  expansion : ∀ n, letI := @Fintype.ofFinite {x : X // component x = n} (finite n)
    HasVertexExpansion (graph n) expansionConstant
  card_tendsto : Tendsto (fun n => (Nat.card {x : X // component x = n} : ℝ)) atTop atTop

/-- Delete only empty labels and transport the graphs, retaining the same metric space. -/
def ExpanderGraphUnionData.toExpanderGraphUnion {X : Type*} [PseudoMetricSpace X]
    (D : ExpanderGraphUnionData X) : ExpanderGraphUnion X := by
  let hπ := component_range_infinite_of_card_tendsto D.component D.card_tendsto
  let π := occupiedComponent D.component hπ
  let q : ℕ → ℕ := fun n => (occupiedComponentOrder D.component hπ n).val
  let e := occupiedComponentFiberEquiv D.component hπ
  have hf (n : ℕ) : Finite {x : X // π x = n} := (e n).finite_iff.mpr (D.finite (q n))
  letI : ∀ n, Fintype {x : X // π x = n} := fun n => @Fintype.ofFinite _ (hf n)
  letI : ∀ n, Fintype {x : X // D.component x = n} := fun n => @Fintype.ofFinite _ (D.finite n)
  let G (n : ℕ) : SimpleGraph {x : X // π x = n} := (D.graph (q n)).comap (e n)
  have hG (n : ℕ) : HasVertexExpansion (G n) D.expansionConstant :=
    vertexExpansion_iso (SimpleGraph.Iso.comap (e n) (D.graph (q n))).symm (D.expansion (q n))
  have hmono : StrictMono q := (occupiedComponentOrder D.component hπ).strictMono
  have hq (x : X) : q (π x) = D.component x := occupiedComponentOrder_component D.component hπ x
  refine {
    component := π
    finite := hf
    graph := G
    connected := ?_
    dist_eq := ?_
    separated := ?_
    degreeBound := D.degreeBound
    degree_le := ?_
    expansionConstant := D.expansionConstant
    expansion_pos := D.expansion_pos
    expansion := hG
    card_tendsto := ?_
  }
  · intro n
    let : Nonempty {x : X // π x = n} := by
      obtain ⟨x, hx⟩ := occupiedComponent_surjective D.component hπ n
      exact ⟨⟨x, hx⟩⟩
    exact (hG n).connected D.expansion_pos
  · intro n x y
    calc
      dist (x : X) (y : X) = ((D.graph (q n)).dist (e n x) (e n y) : ℝ) := D.dist_eq (q n) (e n x) (e n y)
      _ = ((G n).dist x y : ℝ) := by
        exact congrArg (Nat.cast : ℕ → ℝ) (graphIso_dist_eq
          (SimpleGraph.Iso.comap (e n) (D.graph (q n))) ((hG n).preconnected D.expansion_pos) x y)
  · intro r
    obtain ⟨N, hN⟩ := D.separated r
    refine ⟨N, fun x y hxy hn => hN x y ?_ ?_⟩
    · intro hh
      apply hxy
      exact hmono.injective ((hq x).trans (hh.trans (hq y).symm))
    · rw [← hq x, ← hq y]
      exact hn.trans (Nat.add_le_add (hmono.id_le _) (hmono.id_le _))
  · intro n x
    have hi := (SimpleGraph.Iso.comap (e n) (D.graph (q n))).degree_eq x
    have hb := D.degree_le (q n) (e n x)
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hb ⊢
    exact hi ▸ hb
  · have hc := D.card_tendsto.comp hmono.tendsto_atTop
    apply hc.congr'
    exact Filter.Eventually.of_forall fun n => by
      change (Nat.card {x : X // D.component x = q n} : ℝ) =
        (Nat.card {x : X // π x = n} : ℝ)
      exact_mod_cast (Nat.card_congr (e n)).symm

/-- Empty components can be removed without changing the metric space, the uniform
constants, or which vertices lie in the same component. -/
theorem expanderGraphUnion_of_raw_data {X : Type*} [PseudoMetricSpace X]
    (D : ExpanderGraphUnionData X) :
    ∃ D' : ExpanderGraphUnion X, D'.degreeBound = D.degreeBound ∧
      D'.expansionConstant = D.expansionConstant ∧
      ∀ x y, D'.component x = D'.component y ↔ D.component x = D.component y := by
  refine ⟨D.toExpanderGraphUnion, rfl, rfl, fun x y => ?_⟩
  let hπ := component_range_infinite_of_card_tendsto D.component D.card_tendsto
  change occupiedComponent D.component hπ x = occupiedComponent D.component hπ y ↔ _
  unfold occupiedComponent
  rw [(occupiedComponentOrder D.component hπ).symm.injective.eq_iff]
  simp only [Subtype.mk.injEq]

end DynamicalCStarAlgebras
