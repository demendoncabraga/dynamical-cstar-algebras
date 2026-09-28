import DynamicalCStarAlgebras.StripFiniteRows
import DynamicalCStarAlgebras.QuasiLocalFlow
import DynamicalCStarAlgebras.QuasiLocalContinuity

noncomputable section

namespace DynamicalCStarAlgebras

open MeasureTheory Filter

/-- Weak orbit averaging commutes with compression by arbitrary coordinate sets. -/
theorem averagingOperator_compression {X : Type*} (h : X → ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) (a : Operator X) (A B : Set X) :
    averagingOperator h hf (coordinateProjection A * a * coordinateProjection B) =
      coordinateProjection A * averagingOperator h hf a * coordinateProjection B := by
  classical
  refine operator_ext fun x y => ?_
  rw [matrixEntry_averagingOperator, matrixEntry_compression, matrixEntry_compression,
    matrixEntry_averagingOperator]
  split_ifs <;> simp

/-- A weak average multiplies every quasi-local error bound by the kernel's L1 norm. -/
theorem IsQuasiLocalAt.averagingOperator {X : Type*} {a : Operator X} {ε : ℝ}
    {E : Set (X × X)} (ha : IsQuasiLocalAt a ε E) (h : X → ℝ) {f : ℝ → ℂ}
    (hf : Integrable f) :
    IsQuasiLocalAt (averagingOperator h hf a) ((∫ t, ‖f t‖) * ε) E := by
  intro A B hAB
  rw [← averagingOperator_compression]
  exact (averagingOperator_norm_le h hf _).trans
    (mul_le_mul_of_nonneg_left (ha A B hAB) (integral_nonneg fun _ => norm_nonneg _))

/-- Positive-scale Fejér averaging preserves the same error and entourage. -/
theorem IsQuasiLocalAt.fejerAverage {X : Type*} {a : Operator X} {ε : ℝ}
    {E : Set (X × X)} (ha : IsQuasiLocalAt a ε E) (h : X → ℝ)
    {s : ℝ} (hs : 0 < s) : IsQuasiLocalAt (fejerAverage h s a) ε E := by
  have havg := ha.averagingOperator h (integrable_fejerKernel_all s).ofReal
  have hn : (∫ t : ℝ, ‖(fejerKernel s t : ℂ)‖) = 1 := by
    simpa only [Complex.norm_real, Real.norm_of_nonneg (fejerKernel_nonneg hs.le _)] using
      integral_fejerKernel hs
  change IsQuasiLocalAt (DynamicalCStarAlgebras.fejerAverage h s a)
    ((∫ t : ℝ, ‖(fejerKernel s t : ℂ)‖) * ε) E at havg
  rw [hn, one_mul] at havg
  exact havg

lemma floor_mesh_gap_le_one {s u v : ℝ} (hs : 0 < s) (huv : |u - v| ≤ s) :
    |⌊u / s⌋ - ⌊v / s⌋| ≤ (1 : ℤ) := by
  have hp : u / s ≤ v / s + 1 := by
    apply (div_le_iff₀ hs).mpr
    rw [add_mul, div_mul_cancel₀ _ hs.ne', one_mul]
    linarith [(abs_le.mp huv).2]
  have hm : v / s ≤ u / s + 1 := by
    apply (div_le_iff₀ hs).mpr
    rw [add_mul, div_mul_cancel₀ _ hs.ne', one_mul]
    linarith [(abs_le.mp huv).1]
  have hp' : ⌊u / s⌋ ≤ ⌊v / s⌋ + 1 := by simpa using Int.floor_mono hp
  have hm' : ⌊v / s⌋ ≤ ⌊u / s⌋ + 1 := by simpa using Int.floor_mono hm
  exact abs_le.mpr ⟨by omega, by omega⟩

lemma abs_sub_le_two_mul_of_floor_mesh_gap {s u v : ℝ} (hs : 0 < s)
    (huv : |⌊u / s⌋ - ⌊v / s⌋| ≤ (1 : ℤ)) : |u - v| ≤ 2 * s := by
  have hu₀ := (le_div_iff₀ hs).mp (Int.floor_le (u / s))
  have hv₀ := (le_div_iff₀ hs).mp (Int.floor_le (v / s))
  have hu₁ := (div_lt_iff₀ hs).mp (Int.lt_floor_add_one (u / s))
  have hv₁ := (div_lt_iff₀ hs).mp (Int.lt_floor_add_one (v / s))
  have hdiff : |(⌊u / s⌋ : ℝ) - ⌊v / s⌋| ≤ 1 := by exact_mod_cast huv
  apply abs_le.mpr
  constructor <;> nlinarith [(abs_le.mp hdiff).1, (abs_le.mp hdiff).2]

lemma matrixEntry_integerBand_all {X : Type*} (φ : X → ℤ) (s : Finset ℤ)
    (a : Operator X) (k : ℤ) (x y : X) :
    matrixEntry (integerBand φ s a k) x y =
      if φ y ∈ s ∧ φ x - φ y = k then matrixEntry a x y else 0 := by
  classical
  change (matrixEntryCLM x y) (∑ j ∈ s, _) = _
  simp only [map_sum, matrixEntryCLM_apply, matrixEntry_compression, Set.mem_ofPred_eq,
    and_comm, ite_and, Finset.sum_ite_eq, sub_eq_iff_eq_add, add_comm]
  split_ifs <;> rfl

lemma eq_sum_integerBands_of_support {X : Type*} (φ : X → ℤ) (s t : Finset ℤ)
    (a : Operator X)
    (hsupp : ∀ x y, matrixEntry a x y ≠ 0 → φ y ∈ s ∧ φ x - φ y ∈ t) :
    a = ∑ k ∈ t, integerBand φ s a k := by
  classical
  refine operator_ext fun x y => ?_
  change _ = (matrixEntryCLM x y) (∑ k ∈ t, _)
  simp only [map_sum, matrixEntryCLM_apply, matrixEntry_integerBand_all]
  by_cases hxy : matrixEntry a x y = 0
  · simp [hxy]
  · simp [(hsupp x y hxy).1, (hsupp x y hxy).2]

/-- The three-band estimate in the proof of the quasi-local substructure theorem. -/
theorem IsQuasiLocalAt.restrict_height {X : Type*} {a : Operator X} {ε s : ℝ}
    {E : Set (X × X)} (ha : IsQuasiLocalAt a ε E) (hε : 0 ≤ ε)
    (h : X → ℝ) (hs : 0 < s)
    (hprop : ∀ x y, s < |h x - h y| → matrixEntry a x y = 0) :
    IsQuasiLocalAt a (3 * ε) (E ∩ {p | dist (h p.1) (h p.2) ≤ 2 * s}) := by
  classical
  intro A B hAB
  refine compression_norm_le_of_finite_subsets a A B (by positivity) ?_
  intro S T _ hT hSA hTB
  let φ : X → ℤ := fun x => ⌊h x / s⌋
  let t : Finset ℤ := hT.toFinset.image φ
  let q : Operator X := coordinateProjection S * a * coordinateProjection T
  have hdecomp : q = ∑ k ∈ Finset.Icc (-1 : ℤ) 1, integerBand φ t q k := by
    apply eq_sum_integerBands_of_support
    intro x y hxy
    have hst : x ∈ S ∧ y ∈ T := by
      by_contra hn
      exact hxy (by simp only [q, matrixEntry_compression, if_neg hn])
    have ha0 : matrixEntry a x y ≠ 0 := by
      simpa only [q, matrixEntry_compression, if_pos hst] using hxy
    refine ⟨Finset.mem_image.mpr ⟨y, hT.mem_toFinset.mpr hst.2, rfl⟩, ?_⟩
    exact Finset.mem_Icc.mpr (abs_le.mp (floor_mesh_gap_le_one hs
      (le_of_not_gt fun hgt => ha0 (hprop x y hgt))))
  change ‖q‖ ≤ 3 * ε
  rw [hdecomp]
  refine (norm_sum_le _ _).trans
    ((Finset.sum_le_sum (g := fun _ => ε) fun k hk => ?_).trans ?_)
  · refine norm_integerBand_le φ t q k hε fun j _ => ?_
    have hcmp : coordinateProjection {x | φ x = j + k} * q *
        coordinateProjection {x | φ x = j} =
        coordinateProjection ({x | φ x = j + k} ∩ S) * a *
          coordinateProjection (T ∩ {x | φ x = j}) := by
      dsimp [q]
      calc
        _ = (coordinateProjection {x | φ x = j + k} * coordinateProjection S) * a *
            (coordinateProjection T * coordinateProjection {x | φ x = j}) := by
          simp only [mul_assoc]
        _ = _ := by rw [coordinateProjection_mul_inter, coordinateProjection_mul_inter]
    rw [hcmp]
    apply ha
    apply Set.disjoint_left.mpr
    rintro ⟨x, y⟩ ⟨hx, hy⟩ hxy
    apply Set.disjoint_left.mp hAB ⟨hSA hx.2, hTB hy.1⟩
    refine ⟨hxy, ?_⟩
    change dist (h x) (h y) ≤ 2 * s
    rw [Real.dist_eq]
    apply abs_sub_le_two_mul_of_floor_mesh_gap hs
    change |φ x - φ y| ≤ 1
    rw [hx.1, hy.2, add_sub_cancel_left]
    exact abs_le.mpr (Finset.mem_Icc.mp hk)
  · norm_num [Int.toNat]

lemma fejerAverage_mem_quasiLocal_restrictReal {X : Type*} (C : CoarseStructure X)
    (h : X → ℝ) {s : ℝ} (hs : 0 < s) (a : Operator X) (ha : a ∈ quasiLocal C) :
    fejerAverage h s a ∈ quasiLocal (C.restrictReal h) := by
  intro ε hε
  obtain ⟨E, hE, haE⟩ := ha (ε / 3) (by positivity)
  refine ⟨E ∩ {p | dist (h p.1) (h p.2) ≤ 2 * s},
    ⟨C.subset Set.inter_subset_left hE, ⟨2 * s, fun _ hp => hp.2⟩⟩, ?_⟩
  have hh := (haE.fejerAverage h hs).restrict_height (by positivity) h hs
    (matrixEntry_fejerAverage_eq_zero h hs a)
  simpa only [mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0)] using hh

/-- Theorem `Thm.qla.h.Points.Cont.Substructure`, for arbitrary coarse spaces. -/
theorem quasiLocal_inter_continuityPoints {X : Type*} (C : CoarseStructure X) (h : X → ℝ) :
    quasiLocal C ∩ continuityPoints h = quasiLocal (C.restrictReal h) := by
  apply Set.Subset.antisymm
  · intro a ha
    exact (isClosed_quasiLocal (C.restrictReal h)).mem_of_tendsto
      (tendsto_fejerAverage h a ha.2) ((eventually_gt_atTop 0).mono fun _s hs =>
        fejerAverage_mem_quasiLocal_restrictReal C h hs a ha.1)
  · intro a ha
    refine ⟨?_, quasiLocal_subset_coarseContinuityPoints (C.restrictReal h) ha h
      (C.restrictReal_largest h).2.1⟩
    intro ε hε
    obtain ⟨E, hE, haE⟩ := ha ε hε
    exact ⟨E, hE.1, haE⟩

end DynamicalCStarAlgebras
