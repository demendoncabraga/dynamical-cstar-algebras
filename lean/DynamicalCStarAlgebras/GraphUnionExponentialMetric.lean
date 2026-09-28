import DynamicalCStarAlgebras.CoarseRemetrization

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

lemma finite_component_prefix {X : Type*} (π : X → ℕ)
    (hf : ∀ n, Finite {x : X // π x = n}) (n : ℕ) :
    {x : X | π x ≤ n}.Finite := by
  have hF := (Finset.range (n + 1)).finite_toSet.biUnion
    (fun j _ => @Set.toFinite X {x | π x = j} (hf j))
  apply hF.subset
  intro x hx
  change π x ≤ n at hx
  exact Set.mem_iUnion.mpr ⟨π x, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), rfl⟩⟩

/-- A finite set has at most M points if each of its vertices belongs to a
component prefix containing at most M points. -/
lemma finite_card_le_component_prefix_bound {X : Type*} (π : X → ℕ)
    (hf : ∀ n, Finite {x : X // π x = n}) (s : Finset X) {M : ℝ} (hM : 0 ≤ M)
    (hs : ∀ x ∈ s, ({y : X | π y ≤ π x}.ncard : ℝ) ≤ M) : (s.card : ℝ) ≤ M := by
  by_cases hne : s.Nonempty
  · obtain ⟨x, hx, hmax⟩ := s.exists_max_image π hne
    have hsub : (s : Set X) ⊆ {y : X | π y ≤ π x} := fun y hy => hmax y hy
    have hc : s.card ≤ {y : X | π y ≤ π x}.ncard := by
      simpa only [Set.ncard_coe_finset] using
        Set.ncard_le_ncard hsub (finite_component_prefix π hf (π x))
    exact (Nat.cast_le.mpr hc).trans (hs x hx)
  · simpa only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero] using hM

/-- Bounded-degree coarse graph unions admit a coarsely equivalent metric of
at most exponential growth, retaining every component's graph metric. -/
theorem CoarseGraphUnion.exists_exponentialGrowth_metric
    {X : Type*} [m₀ : MetricSpace X] (D : CoarseGraphUnion X) (k : ℕ)
    (hdeg : ∀ n, letI := @Fintype.ofFinite {x : X // D.component x = n} (D.finite n)
      ∀ x, ((D.graph n).neighborFinset x).card ≤ k) :
    let π := D.component
    ∃ m : MetricSpace X,
      (∀ x y, π x = π y → @dist X m.toDist x y = @dist X m₀.toDist x y) ∧
      @AtMostExponentialGrowth X m.toPseudoMetricSpace ∧
      AreBijectivelyCoarselyEquivalent (@CoarseStructure.ofPseudoMetric X m₀.toPseudoMetricSpace)
        (@CoarseStructure.ofPseudoMetric X m.toPseudoMetricSpace) := by
  let π := D.component
  have hfinite := D.finite
  have hseparated := D.separated
  have hX := D.uniformlyLocallyFinite k hdeg
  have hballold := hX.finite_closedBall
  let D' : CoarseDisjointUnion X := {
    component := π
    finite := hfinite
    separated := hseparated }
  let G := D.graph
  have hconn := D.connected
  have hdistG := D.dist_eq
  let : ∀ n, Fintype {x : X // π x = n} := fun n => @Fintype.ofFinite _ (hfinite n)
  let d := @dist X m₀.toDist
  have hdnon : ∀ x y, 0 ≤ d x y := fun _ _ => dist_nonneg
  have hdcomm : ∀ x y, d x y = d y x := fun x y => dist_comm x y
  let w (n : ℕ) : ℝ := {x : X | π x ≤ n}.ncard
  have hw : ∀ n, 0 ≤ w n := fun _ => Nat.cast_nonneg _
  let m : MetricSpace X := partitionWeightedMetric π w hw
  have hdist (x y : X) : @dist X m.toDist x y =
      d x y + if π x = π y then 0 else w (π x) + w (π y) := rfl
  have hle (x y : X) : d x y ≤ @dist X m.toDist x y := by
    rw [hdist]
    apply le_add_of_nonneg_right
    split_ifs
    · exact le_rfl
    · exact add_nonneg (hw _) (hw _)
  have hinternal (x y : X) (hxy : π x = π y) : @dist X m.toDist x y = d x y := by
    simp only [hdist, hxy, if_true, add_zero]
  refine ⟨m, hinternal, ?_, ?_⟩
  · let K := max k 2
    refine ⟨((2 * K ^ 2 : ℕ) : ℝ), ?_, ?_⟩
    · have hK : 2 ≤ K := Nat.le_max_right _ _
      exact_mod_cast (show 1 < 2 * K ^ 2 by nlinarith)
    intro r hr x
    let B := @Metric.closedBall X m.toPseudoMetricSpace x (r : ℝ)
    have hB : B.Finite := by
      apply (hballold x (r : ℝ)).subset
      intro y hy
      exact (hle y x).trans hy
    let z : {y : X // π y = π x} := ⟨x, rfl⟩
    let A : Finset {y : X // π y = π x} :=
      Finset.univ.filter fun y => (G (π x)).dist z y ≤ r
    let S : Set X := (fun y : {y : X // π y = π x} => (y : X)) '' (A : Set _)
    let T : Set X := B ∩ {y | π y ≠ π x}
    have hS : S.Finite := A.finite_toSet.image _
    have hT : T.Finite := hB.subset Set.inter_subset_left
    have hsub : B ⊆ S ∪ T := by
      intro y hy
      by_cases he : π y = π x
      · apply Or.inl
        refine ⟨⟨y, he⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
        have hd : d y x ≤ r := (hle y x).trans hy
        have hd' : d x y ≤ r := (hdcomm x y).trans_le hd
        have heq : d x y = ((G (π x)).dist z ⟨y, he⟩ : ℝ) := hdistG (π x) z ⟨y, he⟩
        rw [heq] at hd'
        exact_mod_cast hd' 
      · exact Or.inr ⟨hy, he⟩
    have hScard : S.ncard ≤ K ^ (r + 1) := by
      rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]
      exact graph_ball_card_le_power (G (π x)) (hconn _) K (Nat.le_max_right _ _)
        (fun y => (hdeg _ y).trans (Nat.le_max_left _ _)) r z
    have hTcard : T.ncard ≤ r := by
      have hc := finite_card_le_component_prefix_bound π hfinite hT.toFinset
        (Nat.cast_nonneg r) (fun y hy => ?_)
      · simpa only [Set.ncard_eq_toFinset_card T hT] using (Nat.cast_le.mp hc)
      · have hy' : y ∈ T := by simpa using hy
        have hd := hy'.1
        change @dist X m.toDist y x ≤ r at hd
        rw [hdist, if_neg hy'.2] at hd
        change w (π y) ≤ (r : ℝ)
        linarith [hdnon y x, hw (π x)]
    refine ⟨hB, ?_⟩
    have hcard : B.ncard ≤ K ^ (r + 1) + r :=
      (Set.ncard_le_ncard hsub (hS.union hT)).trans
        ((Set.ncard_union_le S T).trans (Nat.add_le_add hScard hTcard))
    have hK : 2 ≤ K := Nat.le_max_right _ _
    have hfirst : K ^ (r + 1) ≤ (K ^ 2) ^ r := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hsecond : r ≤ (K ^ 2) ^ r :=
      Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by nlinarith) r)
    have hmain : K ^ (r + 1) + r ≤ (2 * K ^ 2) ^ r := by
      calc
        _ ≤ 2 * (K ^ 2) ^ r := by omega
        _ ≤ 2 ^ r * (K ^ 2) ^ r := Nat.mul_le_mul_right _ (Nat.le_pow hr)
        _ = _ := (mul_pow 2 (K ^ 2) r).symm
    exact_mod_cast hcard.trans hmain
  · let F : @CoarseDisjointUnion X m.toPseudoMetricSpace := {
      component := π
      finite := hfinite
      separated := fun r => (hseparated r).imp fun N hN x y hxy hsum =>
        (hN x y hxy hsum).trans (hle x y) }
    exact (@CoarseDisjointUnion.bijectivelyCoarselyEquivalent X X
      m₀.toPseudoMetricSpace m.toPseudoMetricSpace D' F (Equiv.refl X)
      (fun _ => rfl) hinternal).1

end DynamicalCStarAlgebras
