import DynamicalCStarAlgebras.PolynomialNonmembership

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- A diagonal operator for a coordinate partition has the common norm bound of its blocks. -/
theorem norm_le_of_component_bounds {X I : Type*} (π : X → I) (a : Operator X)
    {M : ℝ} (hM : 0 ≤ M) (hblock : ∀ x y, π x ≠ π y → matrixEntry a x y = 0)
    (ha : ∀ i, ‖componentOperator (fun x : {x : X // π x = i} => (x : X))
      Subtype.val_injective a‖ ≤ M) : ‖a‖ ≤ M := by
  let b (i : I) : Operator X := liftComponentOperator
    (fun x : {x : X // π x = i} => (x : X)) Subtype.val_injective
      (componentOperator (fun x : {x : X // π x = i} => (x : X)) Subtype.val_injective a)
  have hb (i : I) : ‖b i‖ ≤ M := (norm_liftComponentOperator_le _ _ _).trans (ha i)
  obtain ⟨c, hc, he⟩ := exists_fiber_operator π b hM
    (fun i => (compression_norm_le (b i) _ _).trans (hb i))
  have hac : a = c := by
    apply operator_ext
    intro x y
    rw [he]
    split_ifs with hxy
    · have hh := matrixEntry_liftComponentOperator_image
        (fun z : {z : X // π z = π x} => (z : X)) Subtype.val_injective
        (componentOperator (fun z : {z : X // π z = π x} => (z : X)) Subtype.val_injective a)
        ⟨x, rfl⟩ ⟨y, hxy.symm⟩
      simpa only [matrixEntry_componentOperator] using! hh.symm
    · exact hblock x y hxy
  exact hac ▸ hc

lemma componentOperator_ambient_compression {X Y : Type*} (ι : Y → X)
    (hι : Function.Injective ι) (a : Operator X) (A B : Set X) :
    componentOperator ι hι (coordinateProjection A * a * coordinateProjection B) =
      coordinateProjection (ι ⁻¹' A) * componentOperator ι hι a * coordinateProjection (ι ⁻¹' B) := by
  apply operator_ext
  intro x y
  simp only [matrixEntry_componentOperator, matrixEntry_compression, Set.mem_preimage]

/-- Uniform component modulus bounds give the same bound for a block-diagonal operator. -/
theorem quasiLocalModulus_le_of_component_bounds {X I : Type*} [PseudoMetricSpace X]
    (π : X → I) (a : Operator X) (hblock : ∀ x y, π x ≠ π y → matrixEntry a x y = 0)
    {r M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ i, quasiLocalModulus (componentOperator
      (fun x : {x : X // π x = i} => (x : X)) Subtype.val_injective a) r ≤ M) :
    quasiLocalModulus a r ≤ M := by
  apply (quasiLocalModulus_le_iff a r M).mpr
  intro A B hAB
  apply norm_le_of_component_bounds π _ hM
  · intro x y hxy
    rw [matrixEntry_compression, hblock x y hxy]
    split_ifs <;> rfl
  · intro i
    rw [componentOperator_ambient_compression]
    exact (quasiLocalModulus_le_iff _ r M).mp (ha i) _ _
      (fun x hx y hy => hAB x hx y hy)

end DynamicalCStarAlgebras
