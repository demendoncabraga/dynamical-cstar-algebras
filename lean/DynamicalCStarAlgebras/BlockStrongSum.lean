import DynamicalCStarAlgebras.BlockProjectionAssembly

noncomputable section
open Classical Filter
open scoped Topology
namespace DynamicalCStarAlgebras

lemma fiber_cut_finiteVector {X I : Type*} (π : X → I) (w : X →₀ ℂ) (s : Finset I)
    (hs : w.support.image π ⊆ s) :
    coordinateProjection {x | π x ∈ s} (finiteVector w) = finiteVector w := by
  simp only [finiteVector, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [coordinateProjection_delta_of_mem (show x ∈ {x | π x ∈ s} from hs (Finset.mem_image.mpr ⟨x, hx, rfl⟩))]

lemma tendsto_fiber_cuts {X I : Type*} (π : X → I) (v : HilbertSpace X) :
    Tendsto (fun s : Finset I => coordinateProjection {x | π x ∈ s} v) atTop (𝓝 v) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨w, hw⟩ := (denseRange_finiteVector (X := X)).exists_dist_lt v (half_pos hε)
  refine ⟨w.support.image π, fun s hs => ?_⟩
  have hfix := fiber_cut_finiteVector π w s hs
  have hc := (coordinateProjection {x | π x ∈ s}).le_of_opNorm_le
    (coordinateProjection_norm_le _) (v - finiteVector w)
  rw [map_sub, hfix, one_mul] at hc
  have ht := norm_sub_le_norm_sub_add_norm_sub (coordinateProjection {x | π x ∈ s} v)
    (finiteVector w) v
  rw [dist_eq_norm] at hw ⊢
  rw [norm_sub_rev (finiteVector w) v] at ht
  linarith

lemma sum_fiber_compressions_eq_cut {X I : Type*} (π : X → I) (a : Operator X)
    (ha : ∀ x y, π x ≠ π y → matrixEntry a x y = 0) (s : Finset I) :
    ∑ i ∈ s, coordinateProjection {x | π x = i} * a * coordinateProjection {x | π x = i} =
      coordinateProjection {x | π x ∈ s} * a := by
  have hsingle (i : I) : coordinateProjection {x | π x = i} * a * coordinateProjection {x | π x = i} =
      coordinateProjection {x | π x = i} * a := by
    rw [(blockDiagonal_commute_projection π a ha i).eq, mul_assoc,
      show coordinateProjection {x | π x = i} * coordinateProjection {x | π x = i} =
        coordinateProjection {x | π x = i} from
          (coordinateSubspace {x | π x = i}).toSubmodule.isIdempotentElem_starProjection]
  simp_rw [hsingle]
  rw [← Finset.sum_mul, sum_coordinateProjection s (fun i => {x | π x = i})
    (fun i _ j _ hij => Set.disjoint_left.mpr fun x hxi hxj => hij (hxi.symm.trans hxj))]
  congr 2
  ext x
  simp

/-- The diagonal blocks sum strongly to a block-diagonal operator. -/
theorem hasSum_fiber_compressions {X I : Type*} (π : X → I) (a : Operator X)
    (ha : ∀ x y, π x ≠ π y → matrixEntry a x y = 0) (v : HilbertSpace X) :
    HasSum (fun i => (coordinateProjection {x | π x = i} * a * coordinateProjection {x | π x = i}) v) (a v) := by
  have ht := tendsto_fiber_cuts π (a v)
  change Tendsto (fun s : Finset I => ∑ i ∈ s,
    (coordinateProjection {x | π x = i} * a * coordinateProjection {x | π x = i}) v) atTop (𝓝 (a v))
  convert ht using 1
  funext s
  rw [← sum_apply, sum_fiber_compressions_eq_cut π a ha s]
  rfl

/-- The strong sum of a supplied family of coordinate projections is an orthogonal
projection with exactly those component restrictions. This is the operator
construction in Assumption.1; existence of the prescribed finite subspaces is separate. -/
theorem exists_projection_strong_sum {X I : Type*} (π : X → I)
    (p : ∀ i, Operator {x : X // π x = i}) (hp : ∀ i, IsStarProjection (p i)) :
    ∃ a : Operator X, IsStarProjection a ∧
      (∀ x y, π x ≠ π y → matrixEntry a x y = 0) ∧
      (∀ i, componentOperator (fun x : {x : X // π x = i} => (x : X))
        Subtype.val_injective a = p i) ∧
      ∀ v : HilbertSpace X, HasSum (fun i => liftComponentOperator
        (fun x : {x : X // π x = i} => (x : X)) Subtype.val_injective (p i) v) (a v) := by
  obtain ⟨a, ha, hb, he⟩ := exists_assembled_projection π p hp
  refine ⟨a, ha, hb, he, ?_⟩
  intro v
  have hl (i : I) : liftComponentOperator (fun x : {x : X // π x = i} => (x : X))
      Subtype.val_injective (p i) =
        coordinateProjection {x | π x = i} * a * coordinateProjection {x | π x = i} := by
    rw [← he i, lift_componentOperator_eq_compression]
    simp only [Subtype.range_coe_subtype]
  simpa only [hl] using hasSum_fiber_compressions π a hb v

end DynamicalCStarAlgebras
