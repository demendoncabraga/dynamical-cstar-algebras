import DynamicalCStarAlgebras.PermutationExpanderNumerics
import DynamicalCStarAlgebras.PermutationCount
import DynamicalCStarAlgebras.PermutationExpanders

/-!
Adapted from the checked finite counting construction in
the same-author sibling paper-formalization project, specifically
`propertyH_lean/lean/PropertyH/ExpanderExistence.lean`. The proofs below are included in full and checked with this repository's
Lean/Mathlib pins; no declaration from the sibling project is imported.
-/

noncomputable section
namespace DynamicalCStarAlgebras.PermutationExpanders

lemma choose_mono_below_half (n a t : ℕ) (hta : t ≤ a) (ha : a ≤ n/2) :
    n.choose t ≤ n.choose a := by
  induction a, hta using Nat.le_induction with
  | base => rfl
  | succ a hta ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

lemma card_small_subsets_le {V : Type*} [Fintype V] [DecidableEq V]
    (a : ℕ) (ha : a ≤ Fintype.card V / 2) :
    (Finset.univ.filter fun D : Finset V => D.card ≤ a).card ≤
      (a+1) * (Fintype.card V).choose a := by
  classical
  have hsub : (Finset.univ.filter fun D : Finset V => D.card ≤ a) ⊆
      (Finset.range (a+1)).biUnion (fun t => Finset.univ.powersetCard t) := by
    intro D hD
    exact Finset.mem_biUnion.mpr ⟨D.card, Finset.mem_range.mpr (by simpa using (Finset.mem_filter.mp hD).2),
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ t ∈ Finset.range (a+1), (Finset.univ.powersetCard t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ Finset.range (a+1), (Fintype.card V).choose a := by
      apply Finset.sum_le_sum
      intro t ht
      simp only [Finset.card_powersetCard, Finset.card_univ]
      exact choose_mono_below_half _ a t (by simpa using Finset.mem_range.mp ht) ha
    _ = _ := by simp [mul_comm]

def badCuts (V : Type*) [Fintype V] [DecidableEq V] : Finset (Finset V × Finset V) :=
  Finset.univ.filter fun P => 0 < P.1.card ∧ 2*P.1.card ≤ Fintype.card V ∧
    P.1 ⊆ P.2 ∧ 2*P.2.card < 3*P.1.card

lemma card_badCuts_fiber_le {V : Type*} [Fintype V] [DecidableEq V]
    (a : ℕ) (ha : a ≤ Fintype.card V / 2) :
    ((badCuts V).filter fun P => P.1.card = a).card ≤
      (a+1) * ((Fintype.card V).choose a)^2 := by
  classical
  let T := ((Finset.univ : Finset V).powersetCard a).product
    (Finset.univ.filter fun D : Finset V => D.card ≤ a)
  have hinj : Set.InjOn (fun P : Finset V × Finset V => (P.1, P.2 \ P.1))
      (↑((badCuts V).filter fun P => P.1.card = a)) := by
    intro P hP Q hQ heq
    dsimp only at heq
    have hp := (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).2
    have hq := (Finset.mem_filter.mp (Finset.mem_filter.mp hQ).1).2
    have hfst := congrArg Prod.fst heq
    change P.1 = Q.1 at hfst
    apply Prod.ext hfst
    have hdiff := congrArg Prod.snd heq
    dsimp only at hdiff
    rw [← Finset.union_sdiff_of_subset hp.2.2.1, ← Finset.union_sdiff_of_subset hq.2.2.1]
    rw [hdiff, hfst]
  have hmap : Set.MapsTo (fun P : Finset V × Finset V => (P.1, P.2 \ P.1))
      (↑((badCuts V).filter fun P => P.1.card = a)) (↑T) := by
    intro P hP
    have hp := (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).2
    have hpa := (Finset.mem_filter.mp hP).2
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hpa⟩, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hp.2.2.1]
    omega
  have hcard := Finset.card_le_card_of_injOn _ hmap hinj
  have hsmall := card_small_subsets_le (V := V) a ha
  dsimp only [T] at hcard
  simp only [Finset.card, Finset.product, Multiset.card_product] at hcard
  change ((badCuts V).filter fun P => P.1.card = a).card ≤
    (Finset.univ.powersetCard a).card * (Finset.univ.filter fun D : Finset V => D.card ≤ a).card at hcard
  rw [Finset.card_powersetCard, Finset.card_univ] at hcard
  nlinarith [Nat.mul_le_mul_left ((Fintype.card V).choose a) hsmall]

lemma trapped_count_real_le {V : Type*} [Fintype V] [DecidableEq V]
    (A B : Finset V) (hn : 0 < Fintype.card V) :
    ((Finset.univ.filter fun σ : Equiv.Perm V => ∀ u ∈ A, σ u ∈ B).card : ℝ) ≤
      (Fintype.card V).factorial * ((B.card : ℝ) / Fintype.card V)^A.card := by
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hi : ((Finset.univ.filter fun σ : Equiv.Perm V => ∀ u ∈ A, σ u ∈ B).card : ℝ) *
      (Fintype.card V : ℝ)^A.card ≤ (Fintype.card V).factorial * (B.card : ℝ)^A.card := by
    exact_mod_cast card_perms_into_mul_pow_le A B
  calc
    _ ≤ ((Fintype.card V).factorial * (B.card : ℝ)^A.card) /
        (Fintype.card V : ℝ)^A.card := (le_div_iff₀ (pow_pos hnR _)).mpr hi
    _ = _ := by rw [div_pow]; ring

lemma badCut_weight_le {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finset V × Finset V) (hP : P ∈ badCuts V) :
    (((Finset.univ.filter fun σ : Equiv.Perm V => ∀ u ∈ P.1, σ u ∈ P.2).card : ℝ))^32 ≤
      ((Fintype.card V).factorial : ℝ)^32 *
        (3*(P.1.card : ℝ)/(2*Fintype.card V))^(32*P.1.card) := by
  have hp := (Finset.mem_filter.mp hP).2
  have hn : 0 < Fintype.card V := by omega
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hr : (P.2.card : ℝ) / Fintype.card V ≤
      3*(P.1.card : ℝ)/(2*Fintype.card V) := by
    have hb : (2 : ℝ)*P.2.card < 3*P.1.card := by exact_mod_cast hp.2.2.2
    apply (div_le_div_iff₀ hnR (by positivity)).mpr
    nlinarith
  have hc := trapped_count_real_le P.1 P.2 hn
  have hc' := hc.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hr P.1.card) (by positivity))
  have hpow := pow_le_pow_left₀ (by positivity) hc' 32
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm P.1.card 32] using hpow

lemma badCuts_count_lt {V : Type*} [Fintype V] [DecidableEq V] :
    (∑ P ∈ badCuts V, (Finset.univ.filter fun σ : Equiv.Perm V =>
      ∀ u ∈ P.1, σ u ∈ P.2).card ^ 32) < (Fintype.card V).factorial ^ 32 := by
  classical
  let w := fun P : Finset V × Finset V =>
    (((Finset.univ.filter fun σ : Equiv.Perm V => ∀ u ∈ P.1, σ u ∈ P.2).card : ℝ))^32
  have hmap : ∀ P ∈ badCuts V, P.1.card ∈ Finset.Icc 1 (Fintype.card V / 2) := by
    intro P hP
    have hp := (Finset.mem_filter.mp hP).2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hfiber : ∀ a ∈ Finset.Icc 1 (Fintype.card V / 2),
      (∑ P ∈ (badCuts V).filter (fun P => P.1.card = a), w P) ≤
      ((Fintype.card V).factorial : ℝ)^32 *
        (((a : ℝ)+1) * ((Fintype.card V).choose a : ℝ)^2 *
          (3*(a : ℝ)/(2*Fintype.card V))^(32*a)) := by
    intro a ha
    have hp : ∀ P ∈ (badCuts V).filter (fun P => P.1.card = a), w P ≤
        ((Fintype.card V).factorial : ℝ)^32 *
          (3*(a : ℝ)/(2*Fintype.card V))^(32*a) := by
      intro P hP
      have hc := badCut_weight_le P (Finset.mem_filter.mp hP).1
      simpa only [(Finset.mem_filter.mp hP).2] using hc
    have hs := Finset.sum_le_card_nsmul _ w _ hp
    have hcard : (((badCuts V).filter (fun P => P.1.card = a)).card : ℝ) ≤
        ((a : ℝ)+1) * ((Fintype.card V).choose a : ℝ)^2 := by
      exact_mod_cast card_badCuts_fiber_le (V := V) a (Finset.mem_Icc.mp ha).2
    simp only [nsmul_eq_mul] at hs
    calc
      _ ≤ _ := hs
      _ ≤ (((a : ℝ)+1) * ((Fintype.card V).choose a : ℝ)^2) *
          (((Fintype.card V).factorial : ℝ)^32 *
            (3*(a : ℝ)/(2*Fintype.card V))^(32*a)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  have hsum := Finset.sum_le_sum hfiber
  rw [Finset.sum_fiberwise_of_maps_to hmap w, ← Finset.mul_sum] at hsum
  have hpos : (0 : ℝ) < ((Fintype.card V).factorial : ℝ)^32 := by positivity
  have htotal := hsum.trans_lt (mul_lt_mul_of_pos_left
    (permutation_union_total_lt_one (Fintype.card V)) hpos)
  simp only [mul_one] at htotal
  dsimp only [w] at htotal
  exact_mod_cast htotal

/-- Every finite vertex set admits a graph with degree bound 64 and vertex expansion 1/2. -/
theorem exists_expander_on (V : Type*) [Fintype V] :
    ∃ G : SimpleGraph V, IsVertexExpander G 64 (1/2) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_permutation_family_avoiding 32 (badCuts V) (badCuts_count_lt (V := V))
  refine ⟨permutationGraph σ, ?_⟩
  have hg := isVertexExpander_of_escape σ (fun A B hA hhalf hsub hsmall =>
    hσ (A, B) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA, hhalf, hsub, hsmall⟩))
  simpa only [Fintype.card_fin] using hg

end DynamicalCStarAlgebras.PermutationExpanders
