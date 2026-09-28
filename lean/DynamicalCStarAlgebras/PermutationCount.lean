import Mathlib
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Set

/-!
Adapted from the checked finite counting construction in
the same-author sibling paper-formalization project, specifically
`propertyH_lean/lean/PropertyH/PermutationCount.lean`. The proofs below are included in full and checked with this repository's
Lean/Mathlib pins; no declaration from the sibling project is imported.
-/

noncomputable section
namespace DynamicalCStarAlgebras.PermutationExpanders

/-- Every injection on A has exactly (N-|A|)! permutation extensions. -/
theorem card_perm_extensions {V : Type*} [Fintype V] [DecidableEq V]
    (A : Finset V) (e : A ↪ V) :
    Fintype.card {σ : Equiv.Perm V // ∀ u : A, σ u = e u} =
      (Fintype.card V - A.card).factorial := by
  classical
  let e₀ : (A : Set V) ≃ Set.range e := Equiv.ofInjective e e.injective
  have hcard := Fintype.card_congr (Equiv.Set.compl e₀)
  have he : Fintype.card ((↑(A : Set V)ᶜ) ≃ (↑(Set.range e)ᶜ)) =
      (Fintype.card V - A.card).factorial := by
    let ec : (↑(A : Set V)ᶜ) ≃ (↑(Set.range e)ᶜ) := e₀.toCompl
    have hc := Fintype.card_equiv ec
    rw [hc]
    congr 1
    exact (Fintype.card_subtype_compl (fun x => x ∈ A)).trans (by simp)
  exact hcard.trans he

/-- Restrict a permutation mapping A into B to an embedding between the subtypes. -/
def permRestriction {V : Type*} [DecidableEq V] (A B : Finset V)
    (σ : {σ : Equiv.Perm V // ∀ u ∈ A, σ u ∈ B}) : A ↪ B where
  toFun u := ⟨σ.1 u, σ.2 u u.2⟩
  inj' _u _v huv := Subtype.ext (σ.1.injective (congrArg Subtype.val huv))

/-- The fiber of restriction is the set of permutation extensions of that injection. -/
def restrictionFiberEquiv {V : Type*} [DecidableEq V] (A B : Finset V) (e : A ↪ B) :
    {σ : {σ : Equiv.Perm V // ∀ u ∈ A, σ u ∈ B} // permRestriction A B σ = e} ≃
      {σ : Equiv.Perm V // ∀ u : A, σ u = (e u : V)} where
  toFun σ := ⟨σ.1.1, fun u => congrArg (fun f : A ↪ B => (f u : V)) σ.2⟩
  invFun σ := ⟨⟨σ.1, fun u hu => by rw [σ.2 ⟨u, hu⟩]; exact (e ⟨u, hu⟩).2⟩, by
    ext u
    exact σ.2 u⟩
  left_inv σ := by rfl
  right_inv σ := by rfl

/-- Exact trapped-permutation count, in falling-factorial form valid even when |B|<|A|. -/
theorem card_perms_into {V : Type*} [Fintype V] [DecidableEq V] (A B : Finset V) :
    (Finset.univ.filter fun σ : Equiv.Perm V => ∀ u ∈ A, σ u ∈ B).card =
      B.card.descFactorial A.card * (Fintype.card V - A.card).factorial := by
  classical
  have hfib : ∀ e : A ↪ B,
      Fintype.card {σ : {σ : Equiv.Perm V // ∀ u ∈ A, σ u ∈ B} // permRestriction A B σ = e} =
        (Fintype.card V - A.card).factorial := by
    intro e
    rw [Fintype.card_congr (restrictionFiberEquiv A B e)]
    exact card_perm_extensions A (e.trans (Function.Embedding.subtype _))
  have htotal := Fintype.card_congr (Equiv.sigmaFiberEquiv (permRestriction A B))
  rw [Fintype.card_sigma] at htotal
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Fintype.card_embedding_eq, Fintype.card_coe] at htotal
  simpa only [Fintype.card_subtype] using htotal.symm

/-- Sampling without replacement is no more likely to stay in B than independent sampling. -/
theorem descFactorial_ratio_bound (a b n : ℕ) (hbn : b ≤ n) :
    b.descFactorial a * n^a ≤ n.descFactorial a * b^a := by
  induction a with
  | zero => simp
  | succ a ih =>
    by_cases hab : b < a + 1
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hab, zero_mul]
      exact Nat.zero_le _
    · have hab' : a ≤ b := by omega
      have han : a ≤ n := hab'.trans hbn
      have hc : (b-a) * n ≤ (n-a) * b := by
        have hb : b-a+a=b := Nat.sub_add_cancel hab'
        have hn : n-a+a=n := Nat.sub_add_cancel han
        nlinarith
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
      nlinarith [Nat.mul_le_mul ih hc]

/-- Integer form of P[σ(A)⊆B] ≤ (|B|/N)^|A|, without denominator side conditions. -/
theorem card_perms_into_mul_pow_le {V : Type*} [Fintype V] [DecidableEq V]
    (A B : Finset V) :
    (Finset.univ.filter fun σ : Equiv.Perm V => ∀ u ∈ A, σ u ∈ B).card *
        (Fintype.card V)^A.card ≤ (Fintype.card V).factorial * B.card^A.card := by
  rw [card_perms_into]
  have hr := descFactorial_ratio_bound A.card B.card (Fintype.card V) (Finset.card_le_univ B)
  calc
    _ = (Fintype.card V - A.card).factorial *
        (B.card.descFactorial A.card * (Fintype.card V)^A.card) := by ring
    _ ≤ (Fintype.card V - A.card).factorial *
        ((Fintype.card V).descFactorial A.card * B.card^A.card) := Nat.mul_le_mul_left _ hr
    _ = _ := by rw [← mul_assoc, Nat.factorial_mul_descFactorial (Finset.card_le_univ A)]
end DynamicalCStarAlgebras.PermutationExpanders
