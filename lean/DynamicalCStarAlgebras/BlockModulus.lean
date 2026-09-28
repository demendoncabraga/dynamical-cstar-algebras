import DynamicalCStarAlgebras.BlockAssembly

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

/-- Taking the diagonal blocks of any coordinate partition preserves every modulus bound. -/
theorem exists_blockDiagonal_modulus_le {X I : Type*} [PseudoMetricSpace X]
    (π : X → I) (a : Operator X) :
    ∃ b : Operator X, ‖b‖ ≤ ‖a‖ ∧
      (∀ x y, matrixEntry b x y = if π x = π y then matrixEntry a x y else 0) ∧
      ∀ r : ℝ, quasiLocalModulus b r ≤ quasiLocalModulus a r := by
  obtain ⟨b, hb, he⟩ := exists_fiber_operator π (fun _ => a) (norm_nonneg a)
    (fun i => compression_norm_le a {x | π x = i} {x | π x = i})
  refine ⟨b, hb, he, fun r => (quasiLocalModulus_le_iff _ _ _).mpr ?_⟩
  intro A B hAB
  have hbound : ∀ i, ‖coordinateProjection {x | π x = i} *
      (coordinateProjection A * a * coordinateProjection B) *
      coordinateProjection {x | π x = i}‖ ≤ quasiLocalModulus a r :=
    fun i => (compression_norm_le _ _ _).trans
      ((quasiLocalModulus_le_iff a r _).mp le_rfl A B hAB)
  obtain ⟨d, hd, hde⟩ := exists_fiber_operator π
    (fun _ => coordinateProjection A * a * coordinateProjection B)
    (quasiLocalModulus_nonneg a r) hbound
  have hd_eq : d = coordinateProjection A * b * coordinateProjection B := by
    apply operator_ext
    intro x y
    rw [hde, matrixEntry_compression, matrixEntry_compression, he]
    split_ifs <;> rfl
  exact hd_eq ▸ hd

end DynamicalCStarAlgebras
