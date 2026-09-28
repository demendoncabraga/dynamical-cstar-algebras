import DynamicalCStarAlgebras.PropertyAApproximation
import DynamicalCStarAlgebras.PropertyADefinition
import DynamicalCStarAlgebras.RoeAlgebra

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- The exact quantitative approximation in the property-A proof: tolerance t^4
for quasi-locality yields a finite-propagation contraction within 18t. -/
theorem HasPropertyA.exists_finitePropagation_approximation {X : Type*} [PseudoMetricSpace X]
    (hX : HasPropertyA X) {t : ℝ} (ht : 0 < t) (a : Operator X) (ha : ‖a‖ ≤ 1)
    {E : Set (X × X)} (hE : E ∈ (CoarseStructure.ofPseudoMetric X).controlled)
    (haE : IsQuasiLocalAt a (t ^ 4) E) :
    ∃ b : Operator X, HasFinitePropagation b ∧ ‖b‖ ≤ 1 ∧ ‖a - b‖ ≤ 18 * t := by
  obtain ⟨R, hR⟩ := hE
  obtain ⟨S, hS, μ, hμs, hμv⟩ := hX (t ^ 2) (sq_pos_of_pos ht) (max R 1)
    (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  obtain ⟨T, hT, ν, hνs, hνv⟩ := hX (t ^ 2) (sq_pos_of_pos ht) S hS
  refine ⟨ν.squarePartition.smoothing a, ⟨2 * T, by positivity, ?_⟩,
    (ν.squarePartition.smoothing_norm_le a).trans ha, ?_⟩
  · exact ν.squarePartition_propagation hνs a
  · exact μ.smoothing_error_le ν ht a ha haE
      (fun p hp => (hμv p.1 p.2 ((hR p hp).trans (le_max_left _ _))).le)
      (fun x z hxz => (hνv x z (hμs x z hxz)).le)

lemma HasPropertyA.contraction_mem_uniformRoe {X : Type*} [PseudoMetricSpace X]
    (hX : HasPropertyA X) (a : Operator X) (ha : ‖a‖ ≤ 1)
    (haq : IsQuasiLocal (CoarseStructure.ofPseudoMetric X) a) :
    a ∈ uniformRoe (CoarseStructure.ofPseudoMetric X) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let t := ε / 36
  have ht : 0 < t := div_pos hε (by norm_num)
  obtain ⟨E, hE, haE⟩ := haq (t ^ 4) (pow_pos ht _)
  obtain ⟨b, hb, _, hab⟩ := hX.exists_finitePropagation_approximation ht a ha hE haE
  refine ⟨b, (controlled_iff_finitePropagation b).mpr hb, ?_⟩
  rw [dist_eq_norm]
  have hsmall : 18 * t < ε := by dsimp [t]; linarith
  exact hab.trans_lt hsmall

/-- Property A implies equality of the uniform Roe and quasi-local algebras,
proved from the source's probability kernels and quantitative commutator argument. -/
theorem uniformRoe_eq_quasiLocal_of_propertyA {X : Type*} [PseudoMetricSpace X]
    (hX : HasPropertyA X) :
    uniformRoe (CoarseStructure.ofPseudoMetric X) = quasiLocal (CoarseStructure.ofPseudoMetric X) := by
  apply Set.Subset.antisymm (uniformRoe_subset_quasiLocal _)
  intro a ha
  let C := CoarseStructure.ofPseudoMetric X
  let M : ℝ := ‖a‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let b : Operator X := ((M⁻¹ : ℝ) : ℂ) • a
  have hb : ‖b‖ ≤ 1 := by
    rw [show b = ((M⁻¹ : ℝ) : ℂ) • a from rfl, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM)]
    apply (inv_mul_le_iff₀ hM).mpr
    dsimp [M]
    linarith
  have hbq : IsQuasiLocal C b := (quasiLocalStarSubalgebra C).smul_mem ha _
  have hbr : b ∈ uniformRoe C := hX.contraction_mem_uniformRoe b hb hbq
  have har : (M : ℂ) • b ∈ uniformRoe C := (uniformRoeStarSubalgebra C).smul_mem hbr _
  have he : (M : ℂ) • b = a := by
    dsimp [b]
    exact smul_inv_smul₀ hM.ne' a
  exact he ▸ har

/-- Every intermediate algebra collapses to the uniform Roe algebra on a
property-A space, as asserted in the introduction. -/
theorem intermediate_eq_uniformRoe_of_propertyA {X : Type*} [PseudoMetricSpace X]
    (hX : HasPropertyA X) (S : Set (Operator X))
    (hleft : uniformRoe (CoarseStructure.ofPseudoMetric X) ⊆ S)
    (hright : S ⊆ quasiLocal (CoarseStructure.ofPseudoMetric X)) :
    S = uniformRoe (CoarseStructure.ofPseudoMetric X) := by
  rw [← uniformRoe_eq_quasiLocal_of_propertyA hX] at hright
  exact Set.Subset.antisymm hright hleft

end DynamicalCStarAlgebras
