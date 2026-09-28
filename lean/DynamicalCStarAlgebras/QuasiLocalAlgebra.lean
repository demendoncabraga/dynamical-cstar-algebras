import DynamicalCStarAlgebras.ModulusAlgebra

noncomputable section

namespace DynamicalCStarAlgebras

universe u

theorem IsQuasiLocalAt.mul {X : Type u} {a b : Operator X} {ε δ : ℝ}
    {E F : Set (X × X)} (ha : IsQuasiLocalAt a ε E) (hb : IsQuasiLocalAt b δ F) :
    IsQuasiLocalAt (a * b) (ε * ‖b‖ + ‖a‖ * δ)
      {p | ∃ z, (p.1, z) ∈ E ∧ (z, p.2) ∈ F} := by
  intro A B hAB
  let S : Set X := {z | ∃ y ∈ B, (z, y) ∈ F}
  have hSB : Disjoint (Sᶜ ×ˢ B) F := Set.disjoint_left.mpr
    fun p hp hF => hp.1 ⟨p.2, hp.2, hF⟩
  have hAS : Disjoint (A ×ˢ S) E := Set.disjoint_left.mpr fun p hp hE =>
    hp.2.elim fun y hy => Set.disjoint_left.mp hAB
      (show (p.1, y) ∈ A ×ˢ B from ⟨hp.1, hy.1⟩) ⟨p.2, hE, hy.2⟩
  exact (compression_mul_norm_le_split a b A B S).trans (add_le_add
    (mul_le_mul_of_nonneg_right (ha A S hAS) (norm_nonneg b))
    (mul_le_mul_of_nonneg_left (hb Sᶜ B hSB) (norm_nonneg a)))

theorem IsQuasiLocal.mul {X : Type u} {C : CoarseStructure X} {a b : Operator X}
    (ha : IsQuasiLocal C a) (hb : IsQuasiLocal C b) : IsQuasiLocal C (a * b) := by
  intro ε hε
  have hd : 0 < ‖a‖ + ‖b‖ + 1 := by positivity
  obtain ⟨E, hE, haE⟩ := ha (ε / (‖a‖ + ‖b‖ + 1)) (div_pos hε hd)
  obtain ⟨F, hF, hbF⟩ := hb (ε / (‖a‖ + ‖b‖ + 1)) (div_pos hε hd)
  refine ⟨_, C.comp hE hF, fun A B hAB => ((haE.mul hbF) A B hAB).trans ?_⟩
  nlinarith [div_mul_cancel₀ ε (ne_of_gt hd), (div_pos hε hd)]

theorem IsQuasiLocalAt.add {X : Type u} {a b : Operator X} {ε δ : ℝ}
    {E F : Set (X × X)} (ha : IsQuasiLocalAt a ε E) (hb : IsQuasiLocalAt b δ F) :
    IsQuasiLocalAt (a + b) (ε + δ) (E ∪ F) := by
  intro A B hAB
  rw [mul_add, add_mul]
  exact (norm_add_le _ _).trans (add_le_add
    (ha A B (hAB.mono_right Set.subset_union_left))
    (hb A B (hAB.mono_right Set.subset_union_right)))

theorem IsQuasiLocal.add {X : Type u} {C : CoarseStructure X} {a b : Operator X}
    (ha : IsQuasiLocal C a) (hb : IsQuasiLocal C b) : IsQuasiLocal C (a + b) :=
  fun ε hε => (ha (ε / 2) (half_pos hε)).elim fun E hE =>
    (hb (ε / 2) (half_pos hε)).elim fun F hF =>
      ⟨E ∪ F, C.union hE.1 hF.1, (add_halves ε) ▸ hE.2.add hF.2⟩

theorem IsQuasiLocalAt.star {X : Type u} {a : Operator X} {ε : ℝ}
    {E : Set (X × X)} (ha : IsQuasiLocalAt a ε E) :
    IsQuasiLocalAt (star a) ε {p | (p.2, p.1) ∈ E} :=
  fun A B hAB => (compression_star_norm a A B).trans_le (ha B A
    (Set.disjoint_left.mpr fun p hp hE => Set.disjoint_left.mp hAB
      (show (p.2, p.1) ∈ A ×ˢ B from ⟨hp.2, hp.1⟩) hE))

theorem IsQuasiLocal.star {X : Type u} {C : CoarseStructure X} {a : Operator X}
    (ha : IsQuasiLocal C a) : IsQuasiLocal C (star a) :=
  fun ε hε => (ha ε hε).elim fun _E hE => ⟨_, C.inverse hE.1, hE.2.star⟩

theorem isQuasiLocal_algebraMap {X : Type u} (C : CoarseStructure X) (c : ℂ) :
    IsQuasiLocal C (algebraMap ℂ (Operator X) c) := by
  have he : diagonalMultiplier (algebraMap ℂ (BoundedDiagonal X) c) =
      algebraMap ℂ (Operator X) c := diagonalMultiplierHom.commutes c
  exact he ▸ (diagonalMultiplier_hasControlledPropagation C _).isQuasiLocal

/-- The quasi-local algebra for an arbitrary coarse structure, with complex scalars. -/
def quasiLocalStarSubalgebra {X : Type u} (C : CoarseStructure X) :
    StarSubalgebra ℂ (Operator X) where
  carrier := quasiLocal C
  zero_mem' := by simpa only [map_zero] using! isQuasiLocal_algebraMap C 0
  one_mem' := by simpa only [map_one] using! isQuasiLocal_algebraMap C 1
  add_mem' := IsQuasiLocal.add
  mul_mem' := IsQuasiLocal.mul
  star_mem' := IsQuasiLocal.star
  algebraMap_mem' := isQuasiLocal_algebraMap C

theorem coe_quasiLocalStarSubalgebra {X : Type u} (C : CoarseStructure X) :
    (quasiLocalStarSubalgebra C : Set (Operator X)) = quasiLocal C := rfl

/-- The full closed C*-subalgebra assertion in the definition of the quasi-local algebra. -/
theorem quasiLocalStarSubalgebra_isClosed {X : Type u} (C : CoarseStructure X) :
    IsClosed (quasiLocalStarSubalgebra C : Set (Operator X)) :=
  (coe_quasiLocalStarSubalgebra C).symm ▸ isClosed_quasiLocal C

end DynamicalCStarAlgebras
