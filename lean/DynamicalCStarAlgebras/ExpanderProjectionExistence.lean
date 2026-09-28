import DynamicalCStarAlgebras.ExpanderGraphUnion
import DynamicalCStarAlgebras.BlockStrongSum
import DynamicalCStarAlgebras.GoodSubspaces

/-! The actual projections of `Assumption.1` and the strict inclusions in
`Thm.Inclusion.QL.Algebras` from paper/main.tex. The logarithmic-rank subspaces
are supplied by the checked frame construction, with exponent `2 * α` and
constant 32. Earlier components are zero and the sum is strong. -/

noncomputable section
open Classical Filter
namespace DynamicalCStarAlgebras

lemma eventually_logarithmic_rank_admissible {u : ℕ → ℝ}
    (hu : Tendsto u atTop atTop) {α : ℝ} (hα : 0 < α) :
    ∀ᶠ n in atTop, 1 ≤ Real.log (u n) ^ α ∧ Real.log (u n) ^ α < u n := by
  have hlarge := ((tendsto_rpow_atTop hα).comp (Real.tendsto_log_atTop.comp hu)).eventually
    (eventually_ge_atTop (1 : ℝ))
  have hsmall := hu.eventually
    ((isLittleO_log_rpow_rpow_atTop α (by norm_num : (0 : ℝ) < 1)).bound
      (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hlarge, hsmall, hu.eventually (eventually_gt_atTop (0 : ℝ))]
    with n hn hs hpos
  refine ⟨hn, ?_⟩
  rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos] at hs
  have hbound := (le_abs_self (Real.log (u n) ^ α)).trans hs
  linarith


/-- The projections of Assumption.1 exist, with universal constant 32, and their
coordinate blocks sum strongly to the ambient orthogonal projection. -/
theorem CoarseGraphUnion.exists_assumption_one_projection
    {X : Type*} [PseudoMetricSpace X] (D : CoarseGraphUnion X)
    (hN : Tendsto (fun n => (Nat.card {x : X // D.component x = n} : ℝ)) atTop atTop)
    {α : ℝ} (hα : 0 < α) :
    ∃ (p : Operator X) (n₀ : ℕ), IsStarProjection p ∧
      (∀ x y, D.component x ≠ D.component y → matrixEntry p x y = 0) ∧
      (∀ n, n₀ ≤ n →
        1 ≤ Real.log (Nat.card {x : X // D.component x = n}) ^ (2 * α) ∧
        Real.log (Nat.card {x : X // D.component x = n}) ^ (2 * α) <
          Nat.card {x : X // D.component x = n}) ∧
      (∀ n < n₀, componentOperator
        (fun x : {x : X // D.component x = n} => (x : X)) Subtype.val_injective p = 0) ∧
      (∀ n, n₀ ≤ n →
        let q := componentOperator (fun x : {x : X // D.component x = n} => (x : X))
          Subtype.val_injective p
        IsStarProjection q ∧ Module.finrank ℂ (LinearMap.range q.toLinearMap) =
          ⌊(Nat.card {x : X // D.component x = n} : ℝ) /
            Real.log (Nat.card {x : X // D.component x = n}) ^ (2 * α)⌋₊ ∧
        ∀ A : Finset {x : X // D.component x = n}, A.Nonempty →
          ‖coordinateProjection (A : Set {x : X // D.component x = n}) * q‖ ≤
            32 * Real.sqrt (1 / Real.log (Nat.card {x : X // D.component x = n}) ^ (2 * α) +
              (A.card : ℝ) / Nat.card {x : X // D.component x = n} *
                Real.log (Real.exp 1 * Nat.card {x : X // D.component x = n} / A.card))) ∧
      ∀ v : HilbertSpace X, HasSum (fun n => liftComponentOperator
        (fun x : {x : X // D.component x = n} => (x : X)) Subtype.val_injective
        (componentOperator (fun x : {x : X // D.component x = n} => (x : X))
          Subtype.val_injective p) v) (p v) := by
  let : ∀ n, Fintype {x : X // D.component x = n} :=
    fun n => @Fintype.ofFinite _ (D.finite n)
  obtain ⟨n₀, hthreshold⟩ := Filter.eventually_atTop.mp
    (eventually_logarithmic_rank_admissible hN (show 0 < 2 * α by positivity))
  have hsubspaces : ∀ n : {n : ℕ // n₀ ≤ n},
      ∃ W : ClosedSubmodule ℂ (HilbertSpace {x : X // D.component x = n}),
        Module.finrank ℂ W.toSubmodule =
          ⌊(Nat.card {x : X // D.component x = n} : ℝ) /
            Real.log (Nat.card {x : X // D.component x = n}) ^ (2 * α)⌋₊ ∧
        ∀ A : Finset {x : X // D.component x = n}, A.Nonempty →
          ‖coordinateProjection (A : Set {x : X // D.component x = n}) * W.toSubmodule.starProjection‖ ≤
            32 * Real.sqrt (1 / Real.log (Nat.card {x : X // D.component x = n}) ^ (2 * α) +
              (A.card : ℝ) / Nat.card {x : X // D.component x = n} *
                Real.log (Real.exp 1 * Nat.card {x : X // D.component x = n} / A.card)) := by
    intro n
    have hn := hthreshold n n.property
    simpa only [Nat.card_eq_fintype_card] using
      (exists_logarithmic_rank_subspace (X := {x : X // D.component x = n})
        (show 0 < 2 * α by positivity)
        (by simpa only [Nat.card_eq_fintype_card] using hn.1)
        (by simpa only [Nat.card_eq_fintype_card] using hn.2))
  choose W hdim hbound using hsubspaces
  let q (n : ℕ) : Operator {x : X // D.component x = n} :=
    if h : n₀ ≤ n then (W ⟨n, h⟩).toSubmodule.starProjection else 0
  have hq (n : ℕ) : IsStarProjection (q n) := by
    dsimp [q]
    split_ifs with hn
    · exact ⟨(W ⟨n, hn⟩).toSubmodule.isIdempotentElem_starProjection,
        isSelfAdjoint_starProjection _⟩
    · exact ⟨by simp [IsIdempotentElem], by simp [IsSelfAdjoint]⟩
  obtain ⟨p, hp, hb, hcomponent, hsum⟩ := exists_projection_strong_sum D.component q hq
  refine ⟨p, n₀, hp, hb, hthreshold, ?_, ?_, ?_⟩
  · intro n hn
    rw [hcomponent]
    simp [q, not_le.mpr hn]
  · intro n hn
    dsimp only
    rw [hcomponent]
    refine ⟨hq n, ?_, ?_⟩
    · have hqn : q n = (W ⟨n, hn⟩).toSubmodule.starProjection := by simp [q, hn]
      rw [hqn]
      change Module.finrank ℂ (W ⟨n, hn⟩).toSubmodule.starProjection.range = _
      rw [Submodule.range_starProjection]
      exact hdim ⟨n, hn⟩
    · simpa only [q, dif_pos hn] using hbound ⟨n, hn⟩
  · intro v
    simpa only [hcomponent] using hsum v


/-- The strict decay-algebra chain on every coarse disjoint union of expanders.
All required finite projections and their strong sums are constructed. -/
theorem ExpanderGraphUnion.strict_decay_inclusions
    {X : Type*} [PseudoMetricSpace X] (D : ExpanderGraphUnion X)
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    (exponentialQuasiLocal : Set (Operator X)) ⊂ polynomialQuasiLocal β ∧
      (polynomialQuasiLocal β : Set (Operator X)) ⊂ polynomialQuasiLocal α ∧
      polynomialQuasiLocal α ⊂ quasiLocal (CoarseStructure.ofPseudoMetric X) := by
  have h (a b : ℝ) (ha : 0 < a) (hab : a < b) :
      (exponentialQuasiLocal : Set (Operator X)) ⊂ polynomialQuasiLocal a ∧
      (polynomialQuasiLocal b : Set (Operator X)) ⊂ polynomialQuasiLocal a ∧
      polynomialQuasiLocal b ⊂ quasiLocal (CoarseStructure.ofPseudoMetric X) := by
    obtain ⟨p, n₀, hp, hb, _, hz, hd, _⟩ :=
      D.toCoarseGraphUnion.exists_assumption_one_projection D.card_tendsto ha
    exact D.strict_decay_inclusions_of_projection_data p hp.isSelfAdjoint hb ha hab
      (by norm_num : (0 : ℝ) < 32) n₀ hz hd
  exact ⟨(h β (β + 1) (hα.trans hαβ) (by linarith)).1,
    (h α β hα hαβ).2.1, (h (α / 2) α (by linarith) (by linarith)).2.2⟩

end DynamicalCStarAlgebras
