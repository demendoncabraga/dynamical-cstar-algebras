import DynamicalCStarAlgebras.FrameNetUnionBound
import Mathlib.Analysis.Normed.Lp.LpEquiv

/-! Subspace and orthogonal-projection assembly for Li--Zhang--Zhu,
Proposition 6.3, https://arxiv.org/html/2608.22439v2#S6.SS2.
The final source implication uses the explicit, still separate concentration
premise (6.6). All coordinate inclusions, Haar frames, exact dimensions, and
orthogonal-projection estimates are constructed and checked here. -/

noncomputable section
open Classical MeasureTheory
open scoped ENNReal
namespace DynamicalCStarAlgebras

/-- The coordinate-preserving identification between finite l2 and Euclidean space. -/
def finiteHilbertEuclideanEquiv (X : Type*) [Fintype X] :
    HilbertSpace X ≃ₗᵢ[ℂ] EuclideanSpace ℂ X :=
  lpPiLpₗᵢ (fun _ : X => ℂ) ℂ

/-- The isometric inclusion of the first r coordinates into d coordinates. -/
def euclideanFinInclusion {r d : ℕ} (h : r ≤ d) :
    EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d) :=
  (finiteHilbertEuclideanEquiv (Fin d)).toLinearIsometry.comp
    ((coordinateEmbedding (Fin.castLE h) (Fin.castLE_injective h)).comp
      (finiteHilbertEuclideanEquiv (Fin r)).symm.toLinearIsometry)

/-- The first r columns of a Haar unitary, expressed as a linear isometry. -/
def haarFrame {r d : ℕ} (h : r ≤ d) (W : EuclideanUnitary (Fin d)) :
    EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d) :=
  (Unitary.linearIsometryEquiv W).toLinearIsometry.comp (euclideanFinInclusion h)

lemma norm_coordinateProjection_eq_restriction {X : Type*} [Fintype X]
    (A : Finset X) (v : HilbertSpace X) :
    ‖coordinateProjection (A : Set X) v‖ =
      ‖euclideanCoordinateRestriction A (finiteHilbertEuclideanEquiv X v)‖ := by
  have hsq : ‖coordinateProjection (A : Set X) v‖ ^ 2 =
      ‖euclideanCoordinateRestriction A (finiteHilbertEuclideanEquiv X v)‖ ^ 2 := by
    rw [← (finiteHilbertEuclideanEquiv X).norm_map (coordinateProjection (A : Set X) v),
      EuclideanSpace.norm_sq_eq, norm_sq_euclideanCoordinateRestriction]
    change (∑ i : X, ‖coordinateProjection (A : Set X) v i‖ ^ 2) = ∑ i ∈ A, ‖v i‖ ^ 2
    simp only [coordinateProjection_apply_ite, Finset.mem_coe, apply_ite norm, norm_zero,
      ite_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    simp
  nlinarith [norm_nonneg (coordinateProjection (A : Set X) v),
    norm_nonneg (euclideanCoordinateRestriction A (finiteHilbertEuclideanEquiv X v))]


/-- An isometric frame yields a closed subspace of the exact dimension, and
coordinate projection onto its range has no larger norm than frame restriction. -/
theorem closed_subspace_of_isometric_frame {r d : ℕ}
    (J : EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d)) :
    ∃ W : ClosedSubmodule ℂ (HilbertSpace (Fin d)),
      Module.finrank ℂ W.toSubmodule = r ∧ ∀ A : Finset (Fin d),
      ‖coordinateProjection (A : Set (Fin d)) * W.toSubmodule.starProjection‖ ≤
        ‖(euclideanCoordinateRestrictionCLM A).comp J.toContinuousLinearMap‖ := by
  let V := (finiteHilbertEuclideanEquiv (Fin d)).symm.toLinearIsometry.comp J
  let W : ClosedSubmodule ℂ (HilbertSpace (Fin d)) :=
    { V.toLinearMap.range with isClosed' := V.isometry.isClosedEmbedding.isClosed_range }
  refine ⟨W, ?_, ?_⟩
  · change Module.finrank ℂ V.toLinearMap.range = r
    simpa using LinearMap.finrank_range_of_inj V.injective
  · intro A
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    obtain ⟨y, hy⟩ := W.toSubmodule.starProjection_apply_mem x
    have hy' : V y = W.toSubmodule.starProjection x := hy
    have hnorm : ‖y‖ ≤ ‖x‖ := by
      rw [← V.norm_map y, hy']
      exact W.toSubmodule.norm_starProjection_apply_le x
    change ‖coordinateProjection (A : Set (Fin d)) (W.toSubmodule.starProjection x)‖ ≤ _
    rw [← hy', norm_coordinateProjection_eq_restriction]
    have hcoord : finiteHilbertEuclideanEquiv (Fin d) (V y) = J y := by simp [V]
    rw [hcoord]
    exact (((euclideanCoordinateRestrictionCLM A).comp J.toContinuousLinearMap).le_opNorm y).trans
      (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))


/-- The cited frame-subspace theorem reduced solely to its Haar coordinate
concentration estimate. This is an implication, not an assertion that the
concentration premise has been proved. -/
theorem exists_frame_subspace_of_haar_coordinate_tails {d r : ℕ}
    (hr : 0 < r) (hrd : r ≤ d)
    (htail : ∀ (v : EuclideanSpace ℂ (Fin d)), ‖v‖ = 1 →
      ∀ (A : Finset (Fin d)), A.Nonempty → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (unitaryOrbitLaw v) {z | Real.sqrt ((A.card : ℝ) / d) +
        12 / Real.sqrt (2 * d) + t < ‖euclideanCoordinateRestriction A z‖} ≤
          ENNReal.ofReal (2 * Real.exp (-(d : ℝ) * t ^ 2))) :
    ∃ W : ClosedSubmodule ℂ (HilbertSpace (Fin d)),
      Module.finrank ℂ W.toSubmodule = r ∧ ∀ (A : Finset (Fin d)), A.Nonempty →
      ‖coordinateProjection (A : Set (Fin d)) * W.toSubmodule.starProjection‖ ≤
        32 * Real.sqrt ((r : ℝ) / d + (A.card : ℝ) / d *
          Real.log (Real.exp 1 * d / A.card)) := by
  have hframe : ∀ (A : Finset (Fin d)), A.Nonempty →
      ∀ (v : EuclideanSpace ℂ (Fin r)), ‖v‖ = 1 → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      euclideanUnitaryHaar {ω | Real.sqrt ((A.card : ℝ) / d) + 12 / Real.sqrt (2 * d) + t <
        ‖euclideanCoordinateRestriction A (haarFrame hrd ω v)‖} ≤
          ENNReal.ofReal (2 * Real.exp (-(d : ℝ) * t ^ 2)) := by
    intro A hA v hv t ht ht1
    have h := htail (euclideanFinInclusion hrd v)
      (by simpa only [LinearIsometry.norm_map] using hv) A hA t ht ht1
    rw [unitaryOrbitLaw, Measure.map_apply (measurable_unitary_apply _) ?_] at h
    · exact h
    · exact measurableSet_lt measurable_const
        (euclideanCoordinateRestrictionCLM A).continuous.norm.measurable
  obtain ⟨ω, hω⟩ := exists_frame_bound_of_coordinate_tails euclideanUnitaryHaar hr hrd
    (haarFrame hrd) hframe
  obtain ⟨W, hdim, hnorm⟩ := closed_subspace_of_isometric_frame (haarFrame hrd ω)
  exact ⟨W, hdim, fun A hA => (hnorm A).trans (hω A hA)⟩

end DynamicalCStarAlgebras
