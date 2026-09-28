import DynamicalCStarAlgebras.OzawaAmplification
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

noncomputable section
open Classical

namespace DynamicalCStarAlgebras

universe u v

variable {J : Type u} {H : Type v} [Fintype J] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] (b : OrthonormalBasis J ℂ H)

/-- The signed basis is preserved by a finite group of unitary operators. -/
def signedBasisSet : Set H := Set.range b ∪ Set.range (fun j => -b j)

lemma signedBasisSet_neg {x : H} : -x ∈ signedBasisSet b ↔ x ∈ signedBasisSet b := by
  simp only [signedBasisSet, Set.mem_union, Set.mem_range]
  constructor <;> rintro (⟨j, hj⟩ | ⟨j, hj⟩)
  · exact Or.inr ⟨j, by simpa using congrArg Neg.neg hj⟩
  · exact Or.inl ⟨j, by simpa using congrArg Neg.neg hj⟩
  · exact Or.inr ⟨j, by simpa using congrArg Neg.neg hj⟩
  · exact Or.inl ⟨j, by simpa using congrArg Neg.neg hj⟩

/-- The finite signed-permutation group associated to an orthonormal basis. -/
def signedBasisGroup : Subgroup (H ≃ₗᵢ[ℂ] H) where
  carrier := {g | ∀ x, x ∈ signedBasisSet b ↔ g x ∈ signedBasisSet b}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh x
    exact (hh x).trans (hg (h x))
  inv_mem' := by
    intro g hg x
    simpa using (hg (g.symm x)).symm

instance signedBasisGroup_finite : Finite (signedBasisGroup b) := by
  let : Finite (signedBasisSet b) :=
    (Set.finite_range b |>.union (Set.finite_range (fun j => -b j))).to_subtype
  apply Finite.of_injective
    (fun g : signedBasisGroup b => fun j : J =>
      (⟨g.val (b j), (g.property (b j)).mp (Or.inl ⟨j, rfl⟩)⟩ : signedBasisSet b))
  intro g h hgh
  apply Subtype.ext
  apply b.toBasis.ext_linearIsometryEquiv
  intro j
  exact congrArg Subtype.val (congrFun hgh j)

def signedBasisRepresentation : Representation ℂ (signedBasisGroup b) H where
  toFun g := g.val.toLinearEquiv.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

lemma signedBasisRepresentation_norm (g : signedBasisGroup b) (x : H) :
    ‖signedBasisRepresentation b g x‖ = ‖x‖ := g.val.norm_map x

lemma mem_signedBasisGroup_of_basis (g : H ≃ₗᵢ[ℂ] H)
    (hg : ∀ j, g (b j) ∈ signedBasisSet b)
    (hg' : ∀ j, g.symm (b j) ∈ signedBasisSet b) : g ∈ signedBasisGroup b := by
  have hmap : ∀ (f : H ≃ₗᵢ[ℂ] H), (∀ j, f (b j) ∈ signedBasisSet b) →
      ∀ x ∈ signedBasisSet b, f x ∈ signedBasisSet b := by
    intro f hf x hx
    rcases hx with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact hf j
    · simpa only [map_neg, signedBasisSet_neg] using hf j
  intro x
  exact ⟨hmap g hg x, fun hx => by simpa using hmap g.symm hg' (g x) hx⟩

lemma reflection_mem_signedBasisGroup (j : J) :
    (Submodule.reflection (ℂ ∙ b j)) ∈ signedBasisGroup b := by
  have hf (i : J) : Submodule.reflection (ℂ ∙ b j) (b i) ∈ signedBasisSet b := by
    rw [Submodule.reflection_singleton_apply, b.norm_eq_one, b.inner_eq_ite]
    by_cases h : j = i
    · subst i
      simp only [ite_true, map_one, one_pow, div_one, one_smul,
        two_smul, add_sub_cancel_right]
      exact Or.inl ⟨j, rfl⟩
    · simp only [if_neg h, map_one, one_pow, div_one, smul_zero,
        zero_smul, zero_sub]
      exact Or.inr ⟨i, rfl⟩
  exact mem_signedBasisGroup_of_basis b _ hf (by simpa using hf)

lemma basisPermutation_mem_signedBasisGroup (e : Equiv.Perm J) :
    b.equiv b e ∈ signedBasisGroup b := by
  apply mem_signedBasisGroup_of_basis
  · intro j
    exact Or.inl ⟨e j, (b.equiv_apply_basis b e j).symm⟩
  · intro j
    rw [OrthonormalBasis.equiv_symm]
    exact Or.inl ⟨e.symm j, (b.equiv_apply_basis b e.symm j).symm⟩

/-- Signed coordinate reflections and coordinate permutations make the natural
finite unitary representation irreducible. -/
theorem signedBasisRepresentation_irreducible [Nonempty J] :
    (signedBasisRepresentation b).IsIrreducible := by
  have hnt : (⊥ : Subrepresentation (signedBasisRepresentation b)) ≠ ⊤ := by
    intro h
    let j : J := Classical.choice inferInstance
    have hj : b j ∈ (⊥ : Subrepresentation (signedBasisRepresentation b)) := by
      rw [h]
      trivial
    have hz : b j = 0 := hj
    exact b.toBasis.ne_zero j hz
  let : Nontrivial (Subrepresentation (signedBasisRepresentation b)) :=
    ⟨⟨⊥, ⊤, hnt⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro W hW
  have hW' : W.toSubmodule ≠ ⊥ := by
    intro h
    exact hW (Subrepresentation.toSubmodule_injective h)
  obtain ⟨v, hvW, hv⟩ := W.toSubmodule.ne_bot_iff.mp hW'
  have hi : ∃ i, inner ℂ (b i) v ≠ 0 := by
    by_contra! h
    apply hv
    apply b.repr.injective
    ext i
    simpa [OrthonormalBasis.repr_apply_apply] using h i
  obtain ⟨i, hi⟩ := hi
  have hreflection : Submodule.reflection (ℂ ∙ b i) v ∈ W.toSubmodule :=
    W.apply_mem_toSubmodule ⟨_, reflection_mem_signedBasisGroup b i⟩ hvW
  have hcoord : (2 * inner ℂ (b i) v) • b i ∈ W.toSubmodule := by
    have hadd := W.toSubmodule.add_mem hreflection hvW
    simpa [Submodule.reflection_singleton_apply, b.norm_eq_one, two_smul, two_mul,
      add_smul] using hadd
  have hbi : b i ∈ W.toSubmodule :=
    (W.toSubmodule.smul_mem_iff (mul_ne_zero two_ne_zero hi)).mp hcoord
  have hbj (j : J) : b j ∈ W.toSubmodule := by
    have h := W.apply_mem_toSubmodule
      ⟨_, basisPermutation_mem_signedBasisGroup b (Equiv.swap i j)⟩ hbi
    change b.equiv b (Equiv.swap i j) (b i) ∈ W.toSubmodule at h
    simpa using h
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  rw [← b.toBasis.span_eq]
  exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hbj j)

end DynamicalCStarAlgebras
