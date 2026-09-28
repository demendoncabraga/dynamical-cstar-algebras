import DynamicalCStarAlgebras.ExpanderMatrixEmbedding
import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.Order.Chebyshev

noncomputable section

namespace DynamicalCStarAlgebras

open Representation

/-- The finite conjugation average underlying Schur orthogonality in Ozawa's
Lemma 3 (arXiv:2310.03677v3, Section 2). -/
theorem irreducible_conjugation_average {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (T : V →ₗ[ℂ] V) :
    (Fintype.card G : ℂ)⁻¹ • (∑ g : G, ρ g * T * ρ g⁻¹) =
      (LinearMap.trace ℂ V T / Module.finrank ℂ V) • (1 : V →ₗ[ℂ] V) := by
  have hG : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  let := invertibleOfNonzero hG
  have havg : (Representation.linHom ρ ρ).averageMap T =
      (Fintype.card G : ℂ)⁻¹ • (∑ g : G, ρ g * T * ρ g⁻¹) := by
    simp [Representation.averageMap, GroupAlgebra.average, map_sum,
      Module.End.mul_eq_comp, LinearMap.comp_assoc]
  let f : Representation.IntertwiningMap ρ ρ :=
    Representation.invariantsEquivIntertwiningMap ρ ρ
      ⟨(Representation.linHom ρ ρ).averageMap T,
        (Representation.linHom ρ ρ).averageMap_invariant T⟩
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective f
  have he : (Fintype.card G : ℂ)⁻¹ • (∑ g : G, ρ g * T * ρ g⁻¹) =
      c • (1 : V →ₗ[ℂ] V) := by
    have he := congrArg Representation.IntertwiningMap.toLinearMap hc
    change c • (1 : V →ₗ[ℂ] V) = (Representation.linHom ρ ρ).averageMap T at he
    exact havg ▸ he.symm
  have htr (g : G) : LinearMap.trace ℂ V (ρ g * T * ρ g⁻¹) = LinearMap.trace ℂ V T := by
    rw [LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have htrace : LinearMap.trace ℂ V
      ((Fintype.card G : ℂ)⁻¹ • (∑ g : G, ρ g * T * ρ g⁻¹)) = LinearMap.trace ℂ V T := by
    simp only [map_smul, map_sum, htr, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, smul_eq_mul]
    exact inv_mul_cancel_left₀ hG _
  rw [he, map_smul, LinearMap.trace_one, smul_eq_mul] at htrace
  by_cases hn : Module.finrank ℂ V = 0
  · have : Subsingleton V := (Module.finrank_zero_iff.mp hn)
    exact Subsingleton.elim _ _
  · rw [he]
    congr 1
    exact (eq_div_iff (by exact_mod_cast hn : (Module.finrank ℂ V : ℂ) ≠ 0)).mpr htrace

/-- Schur orthogonality for arbitrary vector coefficients, the equality in the
proof of Ozawa's Lemma 3. Unitarity and irreducibility are explicit hypotheses. -/
theorem irreducible_unitary_coefficient_average {G H : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (ρ : Representation ℂ G H) [ρ.IsIrreducible]
    (hu : ∀ g x, ‖ρ g x‖ = ‖x‖) (ξ η : H) :
    (Fintype.card G : ℝ)⁻¹ * (∑ g : G, ‖inner ℂ (ρ g ξ) η‖ ^ 2) =
      ‖ξ‖ ^ 2 * ‖η‖ ^ 2 / Module.finrank ℂ H := by
  have hinner (g : G) (z : H) : inner ℂ ξ (ρ g⁻¹ z) = inner ℂ (ρ g ξ) z := by
    have h := (LinearMap.norm_map_iff_inner_map_map (ρ g)).mp (hu g) ξ (ρ g⁻¹ z)
    simpa only [ρ.self_inv_apply] using h.symm
  have hconj (g : G) :
      ρ g * (InnerProductSpace.rankOne ℂ ξ ξ).toLinearMap * ρ g⁻¹ =
        (InnerProductSpace.rankOne ℂ (ρ g ξ) (ρ g ξ)).toLinearMap := by
    ext z
    simp only [Module.End.mul_apply, ContinuousLinearMap.coe_coe,
      InnerProductSpace.rankOne_apply, map_smul, hinner]
  have havg := irreducible_conjugation_average ρ (InnerProductSpace.rankOne ℂ ξ ξ).toLinearMap
  simp_rw [hconj] at havg
  have he := congrArg (fun T : H →ₗ[ℂ] H => inner ℂ η (T η)) havg
  have hdiag (z : H) : inner ℂ η (InnerProductSpace.rankOne ℂ z z η) =
      ((‖inner ℂ z η‖ ^ 2 : ℝ) : ℂ) := by
    rw [InnerProductSpace.inner_right_rankOne_apply, ← inner_conj_symm η z,
      Complex.conj_mul', Complex.ofReal_pow]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, inner_smul_right,
    inner_sum, ContinuousLinearMap.coe_coe, hdiag, InnerProductSpace.trace_rankOne,
    Module.End.one_apply, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow] at he
  have he' : (((Fintype.card G : ℝ)⁻¹ * (∑ g : G, ‖inner ℂ (ρ g ξ) η‖ ^ 2) : ℝ) : ℂ) =
      ((‖ξ‖ ^ 2 * ‖η‖ ^ 2 / Module.finrank ℂ H : ℝ) : ℂ) := by
    push_cast
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using! he
  exact Complex.ofReal_injective he'

/-- Ozawa's Lemma 3: bounded scalar combinations of a finite irreducible unitary
representation have norm at most the reciprocal square root of its dimension. -/
theorem irreducible_unitary_average_norm_le {G H : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (ρ : Representation ℂ G H) [ρ.IsIrreducible]
    (hu : ∀ g x, ‖ρ g x‖ = ‖x‖) (α : G → ℂ) (hα : ∀ g, ‖α g‖ ≤ 1) :
    ‖(Fintype.card G : ℂ)⁻¹ • (∑ g : G, α g • (ρ g).toContinuousLinearMap)‖ ≤
      1 / Real.sqrt (Module.finrank ℂ H) := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity)
  intro ξ η hξ hη
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hsq := irreducible_unitary_coefficient_average ρ hu ξ η
  rw [hξ, hη] at hsq
  norm_num only [one_pow, one_mul] at hsq
  have hCS := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := fun g : G => ‖inner ℂ (ρ g ξ) η‖)
  simp only [Finset.card_univ] at hCS
  have havg : (Fintype.card G : ℝ)⁻¹ * (∑ g : G, ‖inner ℂ (ρ g ξ) η‖) ≤
      1 / Real.sqrt (Module.finrank ℂ H) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [div_pow, one_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Module.finrank ℂ H)]
    rw [← hsq]
    have hh := mul_le_mul_of_nonneg_left hCS (sq_nonneg ((Fintype.card G : ℝ)⁻¹))
    convert hh using 1 <;> field_simp
  apply (Complex.re_le_norm _).trans
  apply le_trans _ havg
  simp only [smul_apply, inner_smul_left, norm_mul, RCLike.norm_conj,
    norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simp only [sum_apply, sum_inner, smul_apply, inner_smul_left]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro g _
  rw [norm_mul, RCLike.norm_conj]
  exact mul_le_of_le_one_left (norm_nonneg _) (hα g)

end DynamicalCStarAlgebras
