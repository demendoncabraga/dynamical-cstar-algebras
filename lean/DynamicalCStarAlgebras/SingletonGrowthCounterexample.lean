import DynamicalCStarAlgebras.ExponentialGrowth
import DynamicalCStarAlgebras.CoarseGraphUnions

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- A countable set with 2^(n²) points at each level n. Every point will be its own graph component. -/
abbrev CrowdedSingletons := Σ n : ℕ, Fin (2 ^ (n * n))

instance crowdedSingletons_countable : Countable CrowdedSingletons :=
  inferInstanceAs (Countable (Σ n : ℕ, Fin (2 ^ (n * n))))

instance crowdedSingletons_infinite : Infinite CrowdedSingletons :=
  Infinite.of_surjective (fun x : CrowdedSingletons => x.1)
    (fun n => ⟨⟨n, ⟨0, Nat.pow_pos (by decide)⟩⟩, rfl⟩)

/-- Distinct vertices at levels n and m are separated by n+m+1. -/
instance crowdedSingletons_metric : MetricSpace CrowdedSingletons where
  dist x y := if x = y then 0 else (x.1 : ℝ) + y.1 + 1
  dist_self x := by simp
  dist_comm x y := by simp only [eq_comm (a := x), add_comm (x.1 : ℝ)]
  dist_triangle x y z := by
    by_cases hxy : x = y
    · subst y
      simp
    by_cases hyz : y = z
    · subst z
      simp
    by_cases hxz : x = z
    · subst z
      simp [hxy, Ne.symm hxy]
      positivity
    simp only [if_neg hxy, if_neg hyz, if_neg hxz]
    linarith [show (0 : ℝ) ≤ y.1 by positivity]
  eq_of_dist_eq_zero {x y} h := by
    by_contra hxy
    rw [if_neg hxy] at h
    have : (0 : ℝ) < (x.1 : ℝ) + y.1 + 1 := by positivity
    linarith

/-- A finite collection of initial levels. -/
def crowdedSingletonPrefix (N : ℕ) : Finset CrowdedSingletons :=
  (Finset.range N).sigma (fun _n => Finset.univ)

@[simp] theorem mem_crowdedSingletonPrefix (N : ℕ) (x : CrowdedSingletons) :
    x ∈ crowdedSingletonPrefix N ↔ x.1 < N := by
  change (⟨x.1, x.2⟩ : Σ n : ℕ, Fin (2 ^ (n * n))) ∈
    (Finset.range N).sigma (fun _n => Finset.univ) ↔ x.1 < N
  simp

/-- Any enumeration of the points provides the required natural-number component labels. -/
def crowdedSingletonEnumeration : CrowdedSingletons ≃ ℕ := Classical.choice inferInstance

instance crowdedSingletonFiber_unique (n : ℕ) : Unique {x // crowdedSingletonEnumeration x = n} where
  default := ⟨crowdedSingletonEnumeration.symm n, crowdedSingletonEnumeration.apply_symm_apply n⟩
  uniq x := Subtype.ext (crowdedSingletonEnumeration.injective
    (x.property.trans (crowdedSingletonEnumeration.apply_symm_apply n).symm))

/-- Although many singleton components occur at one scale, bounded scales contain only finitely many. -/
theorem crowdedSingleton_separated (r : ℝ) : ∃ N : ℕ, ∀ x y : CrowdedSingletons,
    crowdedSingletonEnumeration x ≠ crowdedSingletonEnumeration y →
      N ≤ crowdedSingletonEnumeration x + crowdedSingletonEnumeration y → r ≤ dist x y := by
  obtain ⟨k, hk⟩ := exists_nat_gt r
  let M := (crowdedSingletonPrefix k).sup crowdedSingletonEnumeration
  refine ⟨2 * (M + 1), ?_⟩
  intro x y hxy hsum
  by_contra hr
  have hne : x ≠ y := fun he => hxy (congrArg crowdedSingletonEnumeration he)
  have hd : (x.1 : ℝ) + y.1 + 1 < r := by
    simpa only [dist, if_neg hne] using lt_of_not_ge hr
  have hx : x ∈ crowdedSingletonPrefix k := mem_crowdedSingletonPrefix _ _ |>.mpr
    (by exact_mod_cast (show (x.1 : ℝ) < k by linarith [show (0 : ℝ) ≤ y.1 from Nat.cast_nonneg _]))
  have hy : y ∈ crowdedSingletonPrefix k := mem_crowdedSingletonPrefix _ _ |>.mpr
    (by exact_mod_cast (show (y.1 : ℝ) < k by linarith [show (0 : ℝ) ≤ x.1 from Nat.cast_nonneg _]))
  have hMx : crowdedSingletonEnumeration x ≤ M := Finset.le_sup hx
  have hMy : crowdedSingletonEnumeration y ≤ M := Finset.le_sup hy
  omega

/-- A coarse disjoint union of connected singleton graphs, with degree identically zero. -/
def crowdedSingletonGraphUnion : CoarseGraphUnion CrowdedSingletons where
  component := crowdedSingletonEnumeration
  finite n := inferInstance
  graph _ := ⊥
  connected _ := SimpleGraph.connected_bot_iff.mpr ⟨inferInstance, inferInstance⟩
  dist_eq n x y := by
    have hxy : x = y := Subsingleton.elim _ _
    subst y
    simp
  separated := crowdedSingleton_separated

/-- Each graph component has degree zero, so the degree bound is uniform. -/
theorem crowdedSingleton_graph_degree (n : ℕ) :
    letI := @Fintype.ofFinite _ (crowdedSingletonGraphUnion.finite n)
    ∀ x, ((crowdedSingletonGraphUnion.graph n).neighborFinset x).card = 0 := by
  let := @Fintype.ofFinite _ (crowdedSingletonGraphUnion.finite n)
  let : Subsingleton {x // crowdedSingletonGraphUnion.component x = n} :=
    ⟨fun x y => Subtype.ext (crowdedSingletonEnumeration.injective (x.property.trans y.property.symm))⟩
  intro x
  exact SimpleGraph.degree_eq_zero_of_subsingleton (G := crowdedSingletonGraphUnion.graph n) x

/-- The very large finite level sets do not prevent uniform local finiteness. -/
theorem crowdedSingleton_uniformlyLocallyFinite : UniformlyLocallyFinite CrowdedSingletons := by
  intro R hR
  obtain ⟨k, hk⟩ := exists_nat_gt R
  let S := crowdedSingletonPrefix k
  refine ⟨S.card + 1, fun x => ?_⟩
  have hsub : Metric.closedBall x R ⊆ {x} ∪ (S : Set CrowdedSingletons) := by
    intro y hy
    by_cases hxy : y = x
    · exact Or.inl hxy
    apply Or.inr
    apply (mem_crowdedSingletonPrefix k y).mpr
    have hd : (y.1 : ℝ) + x.1 + 1 ≤ R := by
      simpa only [Metric.mem_closedBall, dist, if_neg hxy] using hy
    exact_mod_cast (show (y.1 : ℝ) < k by
      linarith [show (0 : ℝ) ≤ x.1 from Nat.cast_nonneg _])
  have hfin : ({x} ∪ (S : Set CrowdedSingletons)).Finite :=
    (Set.finite_singleton x).union S.finite_toSet
  refine ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans ?_⟩
  simpa only [Set.ncard_singleton, Set.ncard_coe_finset, Nat.add_comm] using
    Set.ncard_union_le ({x} : Set CrowdedSingletons) (S : Set CrowdedSingletons)

/-- At radius 2n+1, a ball contains all 2^(n²) points at level n. -/
theorem crowdedSingleton_ball_large (n : ℕ) :
    ∃ x : CrowdedSingletons, 2 ^ (n * n) ≤ (Metric.closedBall x (2 * n + 1)).ncard := by
  let x : CrowdedSingletons := ⟨n, ⟨0, Nat.pow_pos (by decide)⟩⟩
  let S : Finset CrowdedSingletons := Finset.univ.map ⟨Sigma.mk n, sigma_mk_injective⟩
  have hS : S.card = 2 ^ (n * n) := by simp [S]
  have hsub : (S : Set CrowdedSingletons) ⊆ Metric.closedBall x (2 * n + 1) := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hy
    simp only [Metric.mem_closedBall, dist, x, Function.Embedding.coeFn_mk]
    split_ifs
    · positivity
    · linarith
  refine ⟨x, ?_⟩
  rw [← hS]
  simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub
    (crowdedSingleton_uniformlyLocallyFinite.finite_closedBall _ _)

/-- This uniformly locally finite coarse disjoint union of degree-zero graphs does not have exponential growth. -/
theorem crowdedSingleton_not_exponentialGrowth : ¬ AtMostExponentialGrowth CrowdedSingletons := by
  rintro ⟨L, hL, hbound⟩
  obtain ⟨k, hk⟩ := exists_nat_gt (max L 1)
  have hkone : 1 ≤ k := by
    have : (1 : ℝ) < k := lt_of_le_of_lt (le_max_right _ _) hk
    exact_mod_cast this.le
  have hLk : L < (2 : ℝ) ^ k := by
    exact (lt_of_le_of_lt (le_max_left _ _) hk).trans (by exact_mod_cast Nat.lt_two_pow_self)
  let n := 3 * k
  obtain ⟨x, hx⟩ := crowdedSingleton_ball_large n
  have hb := (hbound (2 * n + 1) (by omega) x).2
  have hc : ((2 ^ (n * n) : ℕ) : ℝ) ≤ L ^ (2 * n + 1) := by
    exact (Nat.cast_le.mpr hx).trans (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hb)
  have hexp : k * (2 * n + 1) ≤ n * n := by dsimp [n]; nlinarith
  have hg : L ^ (2 * n + 1) < (2 : ℝ) ^ (n * n) := calc
    _ < ((2 : ℝ) ^ k) ^ (2 * n + 1) := by gcongr
    _ = (2 : ℝ) ^ (k * (2 * n + 1)) := by rw [pow_mul]
    _ ≤ (2 : ℝ) ^ (n * n) := pow_le_pow_right₀ (by norm_num) hexp
  exact (not_lt_of_ge (by simpa using hc)) hg

/-- Counterexample to the unqualified growth sentence at paper/main.tex:922.
The singleton components are connected, uniformly degree bounded, and form a literal coarse graph union. -/
theorem singletonGraphUnion_growth_counterexample :
    ∃ D : CoarseGraphUnion CrowdedSingletons, Function.Injective D.component ∧
      UniformlyLocallyFinite CrowdedSingletons ∧
      (∀ n, letI := @Fintype.ofFinite _ (D.finite n)
        ∀ x, ((D.graph n).neighborFinset x).card = 0) ∧
      ¬ AtMostExponentialGrowth CrowdedSingletons :=
  ⟨crowdedSingletonGraphUnion, crowdedSingletonEnumeration.injective,
    crowdedSingleton_uniformlyLocallyFinite, crowdedSingleton_graph_degree,
    crowdedSingleton_not_exponentialGrowth⟩

end DynamicalCStarAlgebras
