import DynamicalCStarAlgebras.CompressionPowers

noncomputable section

namespace DynamicalCStarAlgebras

universe u

theorem isQuasiLocalAt_zero_support {X : Type u} (a : Operator X) :
    IsQuasiLocalAt a 0 (operatorSupport a) :=
  fun A B hAB => (compression_eq_zero_of_disjoint_support a A B hAB) ▸ (norm_zero.le : ‖(0 : Operator X)‖ ≤ 0)

theorem IsQuasiLocalAt.support_subset {X : Type u} {a : Operator X} {E : Set (X × X)}
    (ha : IsQuasiLocalAt a 0 E) : operatorSupport a ⊆ E := by
  intro p hp
  apply Classical.byContradiction
  intro hn
  have hd : Disjoint ({p.1} ×ˢ {p.2}) E := Set.disjoint_left.mpr fun q hq hE =>
    hn ((Prod.ext (Set.mem_singleton_iff.mp hq.1) (Set.mem_singleton_iff.mp hq.2)) ▸ hE)
  exact hp (matrixEntry_eq_zero_of_compression_eq_zero (norm_le_zero_iff.mp (ha _ _ hd))
    (Set.mem_singleton p.1) (Set.mem_singleton p.2))

theorem operatorSupport_mul_subset {X : Type u} (a b : Operator X) :
    operatorSupport (a * b) ⊆
      {p | ∃ z, (p.1, z) ∈ operatorSupport a ∧ (z, p.2) ∈ operatorSupport b} := by
  apply IsQuasiLocalAt.support_subset
  simpa only [zero_mul, mul_zero, add_zero] using
    (isQuasiLocalAt_zero_support a).mul (isQuasiLocalAt_zero_support b)

theorem HasControlledPropagation.mul {X : Type u} {C : CoarseStructure X}
    {a b : Operator X} (ha : HasControlledPropagation C a) (hb : HasControlledPropagation C b) :
    HasControlledPropagation C (a * b) :=
  C.subset (operatorSupport_mul_subset a b) (C.comp ha hb)

theorem HasControlledPropagation.add {X : Type u} {C : CoarseStructure X}
    {a b : Operator X} (ha : HasControlledPropagation C a) (hb : HasControlledPropagation C b) :
    HasControlledPropagation C (a + b) := by
  refine C.subset (IsQuasiLocalAt.support_subset ?_) (C.union ha hb)
  simpa only [zero_add] using (isQuasiLocalAt_zero_support a).add (isQuasiLocalAt_zero_support b)

theorem HasControlledPropagation.star {X : Type u} {C : CoarseStructure X}
    {a : Operator X} (ha : HasControlledPropagation C a) : HasControlledPropagation C (star a) :=
  C.subset (isQuasiLocalAt_zero_support a).star.support_subset (C.inverse ha)

theorem hasControlledPropagation_algebraMap {X : Type u} (C : CoarseStructure X) (z : ℂ) :
    HasControlledPropagation C (algebraMap ℂ (Operator X) z) := by
  have he : diagonalMultiplier (algebraMap ℂ (BoundedDiagonal X) z) =
      algebraMap ℂ (Operator X) z := diagonalMultiplierHom.commutes z
  exact he ▸ diagonalMultiplier_hasControlledPropagation C _

def controlledPropagationStarSubalgebra {X : Type u} (C : CoarseStructure X) :
    StarSubalgebra ℂ (Operator X) where
  carrier := {a | HasControlledPropagation C a}
  zero_mem' := by simpa only [map_zero] using! hasControlledPropagation_algebraMap C 0
  one_mem' := by simpa only [map_one] using! hasControlledPropagation_algebraMap C 1
  add_mem' := HasControlledPropagation.add
  mul_mem' := HasControlledPropagation.mul
  star_mem' := HasControlledPropagation.star
  algebraMap_mem' := hasControlledPropagation_algebraMap C

def uniformRoeStarSubalgebra {X : Type u} (C : CoarseStructure X) :
    StarSubalgebra ℂ (Operator X) := (controlledPropagationStarSubalgebra C).topologicalClosure

/-- The uniform Roe norm closure is a closed unital complex star-subalgebra for every coarse space. -/
theorem uniformRoe_algebra {X : Type u} (C : CoarseStructure X) :
    (uniformRoeStarSubalgebra C : Set (Operator X)) = uniformRoe C ∧
      IsClosed (uniformRoeStarSubalgebra C : Set (Operator X)) :=
  ⟨rfl, (controlledPropagationStarSubalgebra C).isClosed_topologicalClosure⟩

end DynamicalCStarAlgebras
