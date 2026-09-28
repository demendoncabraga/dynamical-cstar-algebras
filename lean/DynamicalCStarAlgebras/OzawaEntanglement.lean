import DynamicalCStarAlgebras.FiniteUnitaryRepresentations
import Mathlib.Analysis.InnerProductSpace.TensorProduct

noncomputable section
open Classical TensorProduct

namespace DynamicalCStarAlgebras

variable {J H : Type*} [Fintype J] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] (b : OrthonormalBasis J ℂ H)

instance signedBasisSet_fintype : Fintype (signedBasisSet b) :=
  (Set.finite_range b |>.union (Set.finite_range (fun j => -b j))).fintype

/-- An unnormalized maximally entangled vector; summing over both signs makes
its invariance under the signed-permutation group immediate. -/
def signedEntangledVector : H ⊗[ℂ] H :=
  ∑ v : signedBasisSet b, v.val ⊗ₜ[ℂ] v.val

lemma signedEntangledVector_ne_zero [Nonempty J] : signedEntangledVector b ≠ 0 := by
  let j : J := Classical.choice inferInstance
  have hnonneg (v : signedBasisSet b) :
      0 ≤ (inner ℂ (b j ⊗ₜ[ℂ] b j) (v.val ⊗ₜ[ℂ] v.val)).re := by
    rcases v.property with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [← hk, TensorProduct.inner_tmul, b.inner_eq_ite]
      split_ifs <;> norm_num
    · rw [← hk, TensorProduct.inner_tmul, inner_neg_right, b.inner_eq_ite]
      split_ifs <;> norm_num
  have h := Finset.single_le_sum (fun v _ => hnonneg v)
    (Finset.mem_univ (⟨b j, Or.inl ⟨j, rfl⟩⟩ : signedBasisSet b))
  have hpos : 1 ≤ (inner ℂ (b j ⊗ₜ[ℂ] b j) (signedEntangledVector b)).re := by
    simpa [signedEntangledVector, inner_sum, TensorProduct.inner_tmul, b.inner_eq_ite] using h
  intro hz
  norm_num [hz] at hpos

lemma signedEntangledVector_fixed (g : signedBasisGroup b) :
    TensorProduct.mapL g.val.toLinearIsometry.toContinuousLinearMap g.val.toLinearIsometry.toContinuousLinearMap
      (signedEntangledVector b) = signedEntangledVector b := by
  let e : signedBasisSet b ≃ signedBasisSet b :=
    { toFun v := ⟨g.val v.val, (g.property v.val).mp v.property⟩
      invFun v := ⟨g.val.symm v.val, (g.property (g.val.symm v.val)).mpr (by simpa only [LinearIsometryEquiv.apply_symm_apply] using v.property)⟩
      left_inv v := by ext; simp
      right_inv v := by ext; simp }
  simp only [signedEntangledVector, map_sum, TensorProduct.mapL_tmul,
    LinearIsometry.coe_toContinuousLinearMap]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- The invariant vector survives every isometric copy of the defining
representation inside another Hilbert space. -/
theorem signed_unitary_amplification_norm_lower_bound
    [Nonempty J] [Fintype (signedBasisGroup b)]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (e : H →ₗᵢ[ℂ] K) (A : signedBasisGroup b → K →L[ℂ] K)
    (hA : ∀ g x, A g (e x) = e (g.val x)) :
    1 ≤ ‖(Fintype.card (signedBasisGroup b) : ℂ)⁻¹ •
      ∑ g : signedBasisGroup b,
        TensorProduct.mapL (A g) g.val.toLinearIsometry.toContinuousLinearMap‖ := by
  let f := TensorProduct.mapIsometry e (LinearIsometry.id (R := ℂ) (E := H))
  let v := f (signedEntangledVector b)
  have hv : v ≠ 0 := by
    exact fun h => signedEntangledVector_ne_zero b (f.injective (by simpa using h))
  have hfixed (g : signedBasisGroup b) :
      TensorProduct.mapL (A g) g.val.toLinearIsometry.toContinuousLinearMap v = v := by
    have he : (TensorProduct.mapL (A g) g.val.toLinearIsometry.toContinuousLinearMap).comp
        f.toContinuousLinearMap = f.toContinuousLinearMap.comp
        (TensorProduct.mapL g.val.toLinearIsometry.toContinuousLinearMap
          g.val.toLinearIsometry.toContinuousLinearMap) := by
      apply ContinuousLinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [f, hA]
      | add x y hx hy => simp_all only [map_add]
    change (TensorProduct.mapL (A g) g.val.toLinearIsometry.toContinuousLinearMap)
      (f.toContinuousLinearMap (signedEntangledVector b)) = f (signedEntangledVector b)
    rw [← ContinuousLinearMap.comp_apply, he, ContinuousLinearMap.comp_apply,
      signedEntangledVector_fixed]
    rfl
  have hcard : (Fintype.card (signedBasisGroup b) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  let T := (Fintype.card (signedBasisGroup b) : ℂ)⁻¹ •
    ∑ g : signedBasisGroup b,
      TensorProduct.mapL (A g) g.val.toLinearIsometry.toContinuousLinearMap
  have hTv : T v = v := by
    simp [T, sum_apply, hfixed, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hcard]
  have hn := T.le_opNorm v
  rw [hTv] at hn
  exact (le_mul_iff_one_le_left (norm_pos_iff.mpr hv)).mp hn

end DynamicalCStarAlgebras
