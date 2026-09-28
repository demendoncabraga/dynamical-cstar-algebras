import DynamicalCStarAlgebras.StripDecayOutsideFinite

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

/-- Multiplication of coordinate projections corresponds to intersection. -/
theorem coordinateProjection_mul_inter {X : Type*} (A B : Set X) :
    coordinateProjection A * coordinateProjection B = coordinateProjection (A ∩ B) := by
  refine ContinuousLinearMap.ext fun v => lp.ext (funext fun x => ?_)
  simp only [mul_apply_eq_comp, coordinateProjection_apply_ite, Set.mem_inter_iff]
  split_ifs <;> simp_all

/-- Analyticity for the negative distance function gives exponential decay of one row. -/
theorem strip_single_row_decay {X : Type*} [PseudoMetricSpace X] (a : Operator X) (x : X)
    (ha : ∀ h : X → ℝ, LipschitzWith 1 h →
      ∃ δ : ℝ, 0 < δ ∧ ∃ F, IsStripExtension h a δ F) :
    HasExponentialDecay (coordinateProjection {x} * a) := by
  obtain ⟨δ, hδ, F, hF⟩ := ha (fun y => -dist y x) (LipschitzWith.dist_left x |>.neg)
  obtain ⟨n, hn⟩ := hF.exists_weighted_bound hδ
  have hN : 0 < (n : ℝ) + 1 := by positivity
  obtain ⟨b, hb, he⟩ := (hasWeightedOperatorBound_iff a _ _ hN.le).mp hn
  refine ⟨((n : ℝ) + 1)⁻¹, inv_pos.mpr hN, (n : ℝ) + 1, hN, fun r hr => ?_⟩
  refine (quasiLocalModulus_le_iff _ _ _).mpr fun A B hAB => ?_
  rw [← mul_assoc, coordinateProjection_mul_inter]
  by_cases hx : x ∈ A
  · have hlow : ∀ y ∈ A ∩ {x}, 0 ≤ -dist y x := by
      intro y hy
      simpa only [Set.mem_singleton_iff.mp hy.2, dist_self, neg_zero] using le_refl (0 : ℝ)
    have hupp : ∀ y ∈ B, -dist y x ≤ -r := by
      intro y hy
      simpa only [dist_comm] using neg_le_neg (hAB x hx y hy)
    have hg := gapEstimate_of_bounds (fun y => -dist y x) (inv_nonneg.mpr hN.le)
      a b he (A ∩ {x}) B 0 (-r) hlow hupp
    simpa only [sub_neg_eq_add, zero_add, mul_comm] using
      hg.trans (mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _))
  · have hz : A ∩ {x} = ∅ := Set.eq_empty_iff_forall_notMem.mpr
      (fun y hy => hx (Set.mem_singleton_iff.mp hy.2 ▸ hy.1))
    rw [hz, compression_eq_zero_of_entries a ∅ B (fun _ hx _ _ => hx.elim), norm_zero]
    positivity

/-- Analyticity for the distance function gives exponential decay of one column. -/
theorem strip_single_column_decay {X : Type*} [PseudoMetricSpace X] (a : Operator X) (x : X)
    (ha : ∀ h : X → ℝ, LipschitzWith 1 h →
      ∃ δ : ℝ, 0 < δ ∧ ∃ F, IsStripExtension h a δ F) :
    HasExponentialDecay (a * coordinateProjection {x}) := by
  obtain ⟨δ, hδ, F, hF⟩ := ha (fun y => dist y x) (LipschitzWith.dist_left x)
  obtain ⟨n, hn⟩ := hF.exists_weighted_bound hδ
  have hN : 0 < (n : ℝ) + 1 := by positivity
  obtain ⟨b, hb, he⟩ := (hasWeightedOperatorBound_iff a _ _ hN.le).mp hn
  refine ⟨((n : ℝ) + 1)⁻¹, inv_pos.mpr hN, (n : ℝ) + 1, hN, fun r hr => ?_⟩
  refine (quasiLocalModulus_le_iff _ _ _).mpr fun A B hAB => ?_
  rw [mul_assoc, mul_assoc, coordinateProjection_mul_inter, ← mul_assoc]
  by_cases hx : x ∈ B
  · have hlow : ∀ y ∈ A, r ≤ dist y x := fun y hy => hAB y hy x hx
    have hupp : ∀ y ∈ {x} ∩ B, dist y x ≤ 0 := by
      intro y hy
      simpa only [Set.mem_singleton_iff.mp hy.1, dist_self] using le_refl (0 : ℝ)
    simpa only [sub_zero, mul_comm] using
      (gapEstimate_of_bounds (fun y => dist y x) (inv_nonneg.mpr hN.le)
        a b he A ({x} ∩ B) r 0 hlow hupp).trans
        (mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _))
  · have hz : {x} ∩ B = ∅ := Set.eq_empty_iff_forall_notMem.mpr
      (fun y hy => hx (Set.mem_singleton_iff.mp hy.1 ▸ hy.2))
    rw [hz, compression_eq_zero_of_entries a A ∅ (fun _ _ _ hy => hy.elim), norm_zero]
    positivity

/-- A finite coordinate projection is the sum of its singleton projections. -/
theorem coordinateProjection_finset_eq_sum {X : Type*} (S : Finset X) :
    coordinateProjection (S : Set X) = ∑ x ∈ S, coordinateProjection {x} := by
  have hS : (⋃ x ∈ S, ({x} : Set X)) = (S : Set X) := by ext; simp
  simpa only [hS] using (sum_coordinateProjection S (fun x => {x})
    (fun x _ y _ hxy => Set.disjoint_singleton.mpr hxy)).symm

/-- Finitely many exceptional rows retain exponential decay. -/
theorem strip_finite_rows_decay {X : Type*} [PseudoMetricSpace X] (a : Operator X)
    {S : Set X} (hS : S.Finite)
    (ha : ∀ h : X → ℝ, LipschitzWith 1 h →
      ∃ δ : ℝ, 0 < δ ∧ ∃ F, IsStripExtension h a δ F) :
    HasExponentialDecay (coordinateProjection S * a) := by
  rw [← hS.coe_toFinset, coordinateProjection_finset_eq_sum, Finset.sum_mul]
  exact (exponentialDecayStarSubalgebra (X := X)).sum_mem
    (fun x _ => strip_single_row_decay a x ha)

/-- Finitely many exceptional columns retain exponential decay. -/
theorem strip_finite_columns_decay {X : Type*} [PseudoMetricSpace X] (a : Operator X)
    {S : Set X} (hS : S.Finite)
    (ha : ∀ h : X → ℝ, LipschitzWith 1 h →
      ∃ δ : ℝ, 0 < δ ∧ ∃ F, IsStripExtension h a δ F) :
    HasExponentialDecay (a * coordinateProjection S) := by
  rw [← hS.coe_toFinset, coordinateProjection_finset_eq_sum, Finset.mul_sum]
  exact (exponentialDecayStarSubalgebra (X := X)).sum_mem
    (fun x _ => strip_single_column_decay a x ha)

end DynamicalCStarAlgebras
