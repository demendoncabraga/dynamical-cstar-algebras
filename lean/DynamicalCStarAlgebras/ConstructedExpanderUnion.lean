import DynamicalCStarAlgebras.ExpanderExistence
import DynamicalCStarAlgebras.NonemptyExpanderUnion

noncomputable section
open Classical Filter
namespace DynamicalCStarAlgebras

lemma PermutationExpanders.IsVertexExpander.hasVertexExpansion
    {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ} {h : ℝ}
    (hG : PermutationExpanders.IsVertexExpander G k h) : HasVertexExpansion G h := by
  intro A hA
  have ha : 2 * A.card ≤ Fintype.card V := by
    have hh : (2 : ℝ) * A.card ≤ Fintype.card V := by linarith
    exact_mod_cast hh
  have hb := hG.2.2 A ha
  have heq : ({v | v ∉ A ∧ ∃ u ∈ A, G.Adj v u} : Set V) =
      (graphBoundary G A : Set V) := by
    ext v
    simp only [graphBoundary, graphNeighborhood, Finset.mem_coe, Finset.mem_sdiff,
      Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hv, u, hu, huv⟩
      exact ⟨Or.inr ⟨u, hu, huv.symm⟩, hv⟩
    · rintro ⟨hv | ⟨u, hu, huv⟩, hnv⟩
      · exact False.elim (hnv hv)
      · exact ⟨hnv, u, hu, huv.symm⟩
  simpa only [heq, Set.ncard_coe_finset] using hb

/-- A chosen degree-64, expansion-1/2 graph on `n+5` vertices, obtained by
finite permutation counting rather than by a cited existence assumption. -/
def constructedExpanderGraph (n : ℕ) : SimpleGraph (Fin (n + 5)) :=
  Classical.choose (PermutationExpanders.exists_expander_on (Fin (n + 5)))

lemma constructedExpanderGraph_spec (n : ℕ) :
    PermutationExpanders.IsVertexExpander (constructedExpanderGraph n) 64 (1 / 2) :=
  Classical.choose_spec (PermutationExpanders.exists_expander_on (Fin (n + 5)))

lemma constructedExpanderGraph_connected (n : ℕ) : (constructedExpanderGraph n).Connected :=
  (constructedExpanderGraph_spec n).hasVertexExpansion.connected (by norm_num)

/-- A radius larger than the component label and its finite graph diameter. -/
def constructedExpanderRadius (n : ℕ) : ℕ :=
  n + Finset.univ.sup (fun p : Fin (n + 5) × Fin (n + 5) =>
    (constructedExpanderGraph n).dist p.1 p.2)

lemma constructedExpanderGraph_dist_le_radius (n : ℕ) (x y : Fin (n + 5)) :
    (constructedExpanderGraph n).dist x y ≤ constructedExpanderRadius n := by
  exact (Finset.le_sup (f := fun p : Fin (n + 5) × Fin (n + 5) =>
    (constructedExpanderGraph n).dist p.1 p.2) (Finset.mem_univ (x, y))).trans (Nat.le_add_left _ _)

/-- The countable vertex set of the constructed coarse disjoint union. -/
def ConstructedExpanderSpace := Σ n : ℕ, Fin (n + 5)

/-- Graph distance inside each component and a constant distance between each
pair of components, chosen larger than their diameters and labels. -/
def constructedExpanderDist : ConstructedExpanderSpace → ConstructedExpanderSpace → ℝ
  | ⟨n, x⟩, ⟨m, y⟩ => if h : m = n then
      ((constructedExpanderGraph n).dist x (h ▸ y) : ℝ)
    else (constructedExpanderRadius n : ℝ) + constructedExpanderRadius m + 1

lemma constructedExpanderDist_same (n : ℕ) (x y : Fin (n + 5)) :
    constructedExpanderDist ⟨n, x⟩ ⟨n, y⟩ = (constructedExpanderGraph n).dist x y := by
  simp [constructedExpanderDist]

lemma constructedExpanderDist_ne {n m : ℕ} (h : n ≠ m)
    (x : Fin (n + 5)) (y : Fin (m + 5)) :
    constructedExpanderDist ⟨n, x⟩ ⟨m, y⟩ =
      (constructedExpanderRadius n : ℝ) + constructedExpanderRadius m + 1 := by
  simp [constructedExpanderDist, h.symm]

instance constructedExpanderMetric : MetricSpace ConstructedExpanderSpace where
  dist := constructedExpanderDist
  dist_self := by
    rintro ⟨n, x⟩
    simp [constructedExpanderDist_same]
  dist_comm := by
    rintro ⟨n, x⟩ ⟨m, y⟩
    by_cases h : n = m
    · subst m
      simp only [constructedExpanderDist_same, SimpleGraph.dist_comm]
    · rw [constructedExpanderDist_ne h, constructedExpanderDist_ne (Ne.symm h)]
      ring
  dist_triangle := by
    rintro ⟨n, x⟩ ⟨m, y⟩ ⟨k, z⟩
    by_cases hnk : n = k
    · subst k
      by_cases hnm : n = m
      · subst m
        simp only [constructedExpanderDist_same]
        exact_mod_cast (constructedExpanderGraph_connected n).dist_triangle (u := x) (v := y) (w := z)
      · rw [constructedExpanderDist_same, constructedExpanderDist_ne hnm,
          constructedExpanderDist_ne (Ne.symm hnm)]
        have hb : ((constructedExpanderGraph n).dist x z : ℝ) ≤ constructedExpanderRadius n := by
          exact_mod_cast constructedExpanderGraph_dist_le_radius n x z
        nlinarith [Nat.cast_nonneg (α := ℝ) (constructedExpanderRadius n),
          Nat.cast_nonneg (α := ℝ) (constructedExpanderRadius m)]
    · by_cases hnm : n = m
      · subst m
        rw [constructedExpanderDist_ne hnk, constructedExpanderDist_same,
          constructedExpanderDist_ne hnk]
        exact le_add_of_nonneg_left (Nat.cast_nonneg _)
      · by_cases hmk : m = k
        · subst k
          rw [constructedExpanderDist_ne hnm, constructedExpanderDist_ne hnm,
            constructedExpanderDist_same]
          exact le_add_of_nonneg_right (Nat.cast_nonneg _)
        · rw [constructedExpanderDist_ne hnk, constructedExpanderDist_ne hnm,
            constructedExpanderDist_ne hmk]
          nlinarith [Nat.cast_nonneg (α := ℝ) (constructedExpanderRadius n),
          Nat.cast_nonneg (α := ℝ) (constructedExpanderRadius m)]
  eq_of_dist_eq_zero := by
    rintro ⟨n, x⟩ ⟨m, y⟩ hzero
    by_cases h : n = m
    · subst m
      rw [constructedExpanderDist_same, Nat.cast_eq_zero] at hzero
      have hxy := (constructedExpanderGraph_connected n).dist_eq_zero_iff.mp hzero
      subst y
      rfl
    · rw [constructedExpanderDist_ne h] at hzero
      have : (0 : ℝ) < (constructedExpanderRadius n : ℝ) + constructedExpanderRadius m + 1 := by positivity
      linarith

/-- Identifying a component fiber with its prescribed finite vertex set. -/
def constructedExpanderFiberEquiv (n : ℕ) :
    {x : ConstructedExpanderSpace // x.1 = n} ≃ Fin (n + 5) where
  toFun x := x.property ▸ x.val.2
  invFun y := ⟨⟨n, y⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨m, x⟩, h⟩
    cases h
    rfl
  right_inv _ := rfl

/-- Actual bounded-degree expander graph-union data on a countable metric space. -/
def constructedExpanderUnionData : ExpanderGraphUnionData ConstructedExpanderSpace where
  component := fun x => x.1
  finite n := (constructedExpanderFiberEquiv n).finite_iff.mpr inferInstance
  graph n := (constructedExpanderGraph n).comap (constructedExpanderFiberEquiv n)
  dist_eq := by
    intro n x y
    have hi := graphIso_dist_eq
      (SimpleGraph.Iso.comap (constructedExpanderFiberEquiv n) (constructedExpanderGraph n))
      ((SimpleGraph.Iso.comap (constructedExpanderFiberEquiv n) (constructedExpanderGraph n)).preconnected_iff.mpr
        (constructedExpanderGraph_connected n).preconnected) x y
    rw [← hi]
    rcases x with ⟨⟨m, x⟩, hx⟩
    rcases y with ⟨⟨k, y⟩, hy⟩
    dsimp only at hx hy
    subst m
    subst k
    exact constructedExpanderDist_same n x y
  separated := by
    intro r
    obtain ⟨N, hN⟩ := exists_nat_gt r
    refine ⟨N, ?_⟩
    rintro ⟨n, x⟩ ⟨m, y⟩ hne hlarge
    change r ≤ constructedExpanderDist _ _
    rw [constructedExpanderDist_ne hne]
    have hsize : (N : ℝ) ≤ (n : ℝ) + m := by exact_mod_cast hlarge
    have hn : (n : ℝ) ≤ constructedExpanderRadius n := by
      exact_mod_cast (show n ≤ constructedExpanderRadius n by unfold constructedExpanderRadius; omega)
    have hm : (m : ℝ) ≤ constructedExpanderRadius m := by
      exact_mod_cast (show m ≤ constructedExpanderRadius m by unfold constructedExpanderRadius; omega)
    linarith
  degreeBound := 64
  degree_le := by
    intro n
    let : Finite {x : ConstructedExpanderSpace // x.1 = n} :=
      (constructedExpanderFiberEquiv n).finite_iff.mpr inferInstance
    let := Fintype.ofFinite {x : ConstructedExpanderSpace // x.1 = n}
    intro x
    have hi := (SimpleGraph.Iso.comap (constructedExpanderFiberEquiv n)
      (constructedExpanderGraph n)).degree_eq x
    have hb := (constructedExpanderGraph_spec n).2.1 (constructedExpanderFiberEquiv n x)
    rw [← SimpleGraph.coe_neighborFinset, Set.ncard_coe_finset,
      SimpleGraph.card_neighborFinset_eq_degree] at hb
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hi ▸ hb
  expansionConstant := 1 / 2
  expansion_pos := by norm_num
  expansion := by
    intro n
    let : Finite {x : ConstructedExpanderSpace // x.1 = n} :=
      (constructedExpanderFiberEquiv n).finite_iff.mpr inferInstance
    let := Fintype.ofFinite {x : ConstructedExpanderSpace // x.1 = n}
    exact vertexExpansion_iso
      (SimpleGraph.Iso.comap (constructedExpanderFiberEquiv n) (constructedExpanderGraph n)).symm
      (constructedExpanderGraph_spec n).hasVertexExpansion
  card_tendsto := by
    have hc : ∀ n, Nat.card {x : ConstructedExpanderSpace // x.1 = n} = n + 5 := by
      intro n
      exact (Nat.card_congr (constructedExpanderFiberEquiv n)).trans (Nat.card_fin _)
    simp only [hc, Nat.cast_add, Nat.cast_ofNat]
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

/-- The constructed graph union is uniformly locally finite. -/
theorem constructedExpanderSpace_uniformlyLocallyFinite :
    UniformlyLocallyFinite ConstructedExpanderSpace :=
  constructedExpanderUnionData.toExpanderGraphUnion.uniformlyLocallyFinite

end DynamicalCStarAlgebras
