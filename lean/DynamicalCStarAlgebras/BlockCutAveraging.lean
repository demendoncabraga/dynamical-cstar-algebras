import DynamicalCStarAlgebras.GraphBlockAnalyticity
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

/-- Exactly one quarter of coordinate cuts separate two specified distinct indices in one direction. -/
theorem sum_cut_coefficient {I : Type*} (s : Finset I) (i j : I)
    (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j) (z : ℂ) :
    (∑ t ∈ (insert i (insert j s)).powerset, if i ∈ t ∧ j ∉ t then z else 0) =
      (2 : ℂ) ^ s.card * z := by
  rw [Finset.sum_powerset_insert (by simp [hi, hij])]
  rw [Finset.sum_powerset_insert hj, Finset.sum_powerset_insert hj]
  simp only [← Finset.sum_add_distrib]
  trans ∑ _ ∈ s.powerset, z
  · apply Finset.sum_congr rfl
    intro t ht
    have hit := Finset.notMem_of_mem_powerset_of_notMem ht hi
    have hjt := Finset.notMem_of_mem_powerset_of_notMem ht hj
    simp [hit, hjt, hij, Ne.symm hij]
  · simp

/-- The cut sum identity with its normalization written without division. -/
theorem four_mul_sum_cut {I : Type*} (s : Finset I) (i j : I)
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) (z : ℂ) :
    4 * (∑ t ∈ s.powerset, if i ∈ t ∧ j ∉ t then z else 0) =
      (2 : ℂ) ^ s.card * z := by
  let u := (s.erase i).erase j
  have hiu : i ∉ u := fun h => Finset.notMem_erase i s (Finset.mem_of_mem_erase h)
  have hju : j ∉ u := Finset.notMem_erase j (s.erase i)
  have hs : s = insert i (insert j u) := by
    rw [Finset.insert_erase (Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩), Finset.insert_erase hi]
  rw [hs, sum_cut_coefficient u i j hiu hju hij z]
  simp only [Finset.card_insert_of_notMem (show i ∉ insert j u by simp [hiu, hij]),
    Finset.card_insert_of_notMem hju, pow_succ]
  ring

/-- Finite coordinate cuts recover an operator with zero diagonal blocks. -/
theorem finite_cut_operator_identity {X I : Type*} (π : X → I) (a : Operator X)
    (s : Finset I) (hs : ∀ x y, matrixEntry a x y ≠ 0 → π x ∈ s ∧ π y ∈ s)
    (hdiag : ∀ x y, π x = π y → matrixEntry a x y = 0) :
    (4 : ℂ) • (∑ t ∈ s.powerset,
      coordinateProjection {x | π x ∈ t} * a * coordinateProjection {x | π x ∉ t}) =
      ((2 : ℂ) ^ s.card) • a := by
  apply operator_ext
  intro x y
  simp only [← matrixEntryCLM_apply, map_smul, map_sum]
  simp only [matrixEntryCLM_apply, matrixEntry_compression,
    Set.mem_ofPred_eq, smul_eq_mul]
  by_cases hzero : matrixEntry a x y = 0
  · simp only [hzero, ite_self, Finset.sum_const_zero, mul_zero]
  · rw [← four_mul_sum_cut s (π x) (π y) (hs x y hzero).1 (hs x y hzero).2
      (fun he => hzero (hdiag x y he)) (matrixEntry a x y)]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> rfl


/-- A cut bound controls the whole finite-block operator, independently of the number of blocks. -/
theorem norm_le_four_mul_of_finite_cuts {X I : Type*} (π : X → I) (a : Operator X)
    (s : Finset I) (hs : ∀ x y, matrixEntry a x y ≠ 0 → π x ∈ s ∧ π y ∈ s)
    (hdiag : ∀ x y, π x = π y → matrixEntry a x y = 0) {ε : ℝ}
    (hcut : ∀ t ∈ s.powerset,
      ‖coordinateProjection {x | π x ∈ t} * a * coordinateProjection {x | π x ∉ t}‖ ≤ ε) :
    ‖a‖ ≤ 4 * ε := by
  have he := congrArg norm (finite_cut_operator_identity π a s hs hdiag)
  norm_num [norm_smul, norm_pow] at he
  have hsum : ‖∑ t ∈ s.powerset,
      coordinateProjection {x | π x ∈ t} * a * coordinateProjection {x | π x ∉ t}‖ ≤
      (2 : ℝ) ^ s.card * ε := by
    exact (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum hcut)
  have hp : 0 < (2 : ℝ) ^ s.card := pow_pos (by norm_num) _
  nlinarith

/-- Two coordinate compressions commute as operations on operators. -/
theorem coordinate_compressions_commute {X : Type*} (a : Operator X) (A B S T : Set X) :
    coordinateProjection A * (coordinateProjection S * a * coordinateProjection T) *
      coordinateProjection B =
    coordinateProjection S * (coordinateProjection A * a * coordinateProjection B) *
      coordinateProjection T := by
  apply operator_ext
  intro x y
  simp only [matrixEntry_compression]
  split_ifs <;> rfl

/-- A uniform cut bound controls operators on arbitrarily many coordinate blocks. -/
theorem norm_le_four_mul_of_cuts {X I : Type*} (π : X → I) (a : Operator X)
    (hdiag : ∀ x y, π x = π y → matrixEntry a x y = 0) {ε : ℝ} (hε : 0 ≤ ε)
    (hcut : ∀ t : Finset I,
      ‖coordinateProjection {x | π x ∈ t} * a * coordinateProjection {x | π x ∉ t}‖ ≤ ε) :
    ‖a‖ ≤ 4 * ε := by
  refine norm_le_of_finiteMatrixForm_bound _ (by positivity) fun v w => ?_
  let d := coordinateProjection (v.support : Set X) * a * coordinateProjection (w.support : Set X)
  have hs : ∀ x y, matrixEntry d x y ≠ 0 →
      π x ∈ (v.support ∪ w.support).image π ∧ π y ∈ (v.support ∪ w.support).image π := by
    intro x y hxy
    have hmem : x ∈ v.support ∧ y ∈ w.support := by
      by_contra hn
      exact hxy (by simp only [d, matrixEntry_compression, Finset.mem_coe, if_neg hn])
    exact ⟨Finset.mem_image.mpr ⟨x, Finset.mem_union_left _ hmem.1, rfl⟩,
      Finset.mem_image.mpr ⟨y, Finset.mem_union_right _ hmem.2, rfl⟩⟩
  have hd : ‖d‖ ≤ 4 * ε := by
    apply norm_le_four_mul_of_finite_cuts π d _ hs
    · intro x y he
      simp only [d, matrixEntry_compression, hdiag x y he, ite_self]
    · intro t _
      rw [show d = _ from rfl, coordinate_compressions_commute]
      exact (compression_norm_le _ _ _).trans (hcut t)
  have he : finiteMatrixForm (matrixEntry a) v w = finiteMatrixForm (matrixEntry d) v w := by
    simp only [finiteMatrixForm_apply]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    simp only [d, matrixEntry_compression, Finset.mem_coe, hx, hy, and_self, if_true]
  rw [he]
  exact (norm_finiteMatrixForm_matrixEntry_le d v w).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (norm_nonneg _)) (norm_nonneg _))

end DynamicalCStarAlgebras
