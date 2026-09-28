import DynamicalCStarAlgebras.CoordinateGaussian
import DynamicalCStarAlgebras.FrameConsequences

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- Relabel finite complex l2 coordinates. -/
def finiteCoordinateEquiv {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) :
    HilbertSpace X ≃ₗᵢ[ℂ] HilbertSpace Y :=
  (finiteHilbertEuclideanEquiv X).trans
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).trans (finiteHilbertEuclideanEquiv Y).symm)

lemma finiteCoordinateEquiv_apply {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (v : HilbertSpace X) (y : Y) : finiteCoordinateEquiv e v y = v (e.symm y) := rfl

/-- Finite-coordinate relabeling preserves dimensions and every coordinate
compression bound of a closed subspace. -/
theorem closed_subspace_relabel {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (W : ClosedSubmodule ℂ (HilbertSpace X)) :
    ∃ V : ClosedSubmodule ℂ (HilbertSpace Y),
      Module.finrank ℂ V.toSubmodule = Module.finrank ℂ W.toSubmodule ∧
      ∀ A : Finset Y,
      ‖coordinateProjection (A : Set Y) * V.toSubmodule.starProjection‖ ≤
        ‖coordinateProjection (A.image e.symm : Set X) * W.toSubmodule.starProjection‖ := by
  let f := finiteCoordinateEquiv e
  let V := W.mapEquiv f.toContinuousLinearEquiv
  refine ⟨V, ?_, ?_⟩
  · exact f.toLinearEquiv.finrank_map_eq W.toSubmodule
  · intro A
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have hm : V.toSubmodule.starProjection x = f (W.toSubmodule.starProjection (f.symm x)) :=
      Submodule.starProjection_map_apply f W.toSubmodule x
    have he : (coordinateProjection (A : Set Y) * V.toSubmodule.starProjection) x =
        f ((coordinateProjection (A.image e.symm : Set X) * W.toSubmodule.starProjection)
          (f.symm x)) := by
      ext y
      simp only [mul_apply_eq_comp, hm, coordinateProjection_apply_ite,
        finiteCoordinateEquiv_apply, Finset.mem_coe, f]
      have hi : e.symm y ∈ A.image e.symm ↔ y ∈ A := by simp
      simp only [hi]
    rw [he, f.norm_map]
    simpa only [f.symm.norm_map] using
      (coordinateProjection (A.image e.symm : Set X) * W.toSubmodule.starProjection).le_opNorm
        (f.symm x)

/-- The universal complex frame-subspace theorem on any finite coordinate set. -/
theorem exists_frame_subspace_finite {X : Type*} [Fintype X] (r : ℕ)
    (hr : 1 ≤ r) (hrd : r ≤ Fintype.card X) :
    ∃ W : ClosedSubmodule ℂ (HilbertSpace X),
      Module.finrank ℂ W.toSubmodule = r ∧ ∀ A : Finset X, A.Nonempty →
      ‖coordinateProjection (A : Set X) * W.toSubmodule.starProjection‖ ≤
        32 * Real.sqrt ((r : ℝ) / Fintype.card X + (A.card : ℝ) / Fintype.card X *
          Real.log (Real.exp 1 * Fintype.card X / A.card)) := by
  obtain ⟨W, hW, hg⟩ := exists_frame_subspace (Fintype.card X) r hr hrd
  obtain ⟨V, hV, hcomp⟩ := closed_subspace_relabel (Fintype.equivFin X).symm W
  refine ⟨V, hV.trans hW, ?_⟩
  intro A hA
  exact (hcomp A).trans (by
    simpa only [Equiv.symm_symm, Finset.coe_image, Finset.card_image_of_injective _ (Fintype.equivFin X).injective]
      using! hg (A.image (Fintype.equivFin X)) (hA.image _))

/-- LemmaGoodSubspacesQuarterPower with the universal constant 96. -/
theorem exists_quarter_power_subspace {X : Type*} [Fintype X] :
    ∃ W : ClosedSubmodule ℂ (HilbertSpace X),
      Module.finrank ℂ W.toSubmodule = ⌈(Fintype.card X : ℝ) ^ (1 / 4 : ℝ)⌉₊ ∧
      ∀ (A : Finset X) (δ : ℝ),
      1 / (Module.finrank ℂ W.toSubmodule : ℝ) ≤ δ → δ ≤ 1 / 2 →
      (A.card : ℝ) ≤ δ * Fintype.card X →
      ‖coordinateProjection (A : Set X) * W.toSubmodule.starProjection‖ ≤
        96 * Real.sqrt (δ * Real.log (1 / δ)) := by
  by_cases hn : Fintype.card X = 0
  · refine ⟨⊥, ?_, ?_⟩
    · simp [hn]
    · intro A δ _ _ _
      change ‖coordinateProjection (A : Set X) *
        (⊥ : Submodule ℂ (HilbertSpace X)).starProjection‖ ≤ _
      simp only [Submodule.starProjection_bot, mul_zero, norm_zero]
      positivity
  · obtain ⟨hr, hrd, _⟩ := ceil_quarter_rank_bounds (Nat.one_le_iff_ne_zero.mpr hn)
    obtain ⟨W, hW, hg⟩ := exists_frame_subspace_finite _ hr hrd
    refine ⟨W, hW, ?_⟩
    intro A δ hδ hhalf hcard
    rw [hW] at hδ
    have he := quarter_power_compression_of_frame_bound W.toSubmodule.starProjection
      (by norm_num : (0 : ℝ) ≤ 32) hg hδ hhalf A (by simpa only [mul_comm] using hcard)
    norm_num only [show (3 : ℝ) * 32 = 96 by norm_num] at he
    exact he

/-- LemmaGoodSubspacesQuarterPower.LARGEDIM with universal constant 32. -/
theorem exists_logarithmic_rank_subspace {X : Type*} [Fintype X] {α : ℝ}
    (_hα : 0 < α) (hq : 1 ≤ Real.log (Fintype.card X) ^ α)
    (hqn : Real.log (Fintype.card X) ^ α < Fintype.card X) :
    ∃ W : ClosedSubmodule ℂ (HilbertSpace X),
      Module.finrank ℂ W.toSubmodule =
        ⌊(Fintype.card X : ℝ) / Real.log (Fintype.card X) ^ α⌋₊ ∧
      ∀ A : Finset X, A.Nonempty →
      ‖coordinateProjection (A : Set X) * W.toSubmodule.starProjection‖ ≤
        32 * Real.sqrt (1 / Real.log (Fintype.card X) ^ α +
          (A.card : ℝ) / Fintype.card X *
            Real.log (Real.exp 1 * Fintype.card X / A.card)) := by
  obtain ⟨hr, hrd, _⟩ := floor_ratio_rank_bounds hq hqn
  obtain ⟨W, hW, hg⟩ := exists_frame_subspace_finite _ hr hrd
  exact ⟨W, hW, logarithmic_rank_compression_of_frame_bound W.toSubmodule.starProjection
    (by norm_num : (0 : ℝ) ≤ 32) hq hqn hg⟩

end DynamicalCStarAlgebras
