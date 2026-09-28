import DynamicalCStarAlgebras.CoarseMetrizability
import DynamicalCStarAlgebras.NonQLFlatRows
import DynamicalCStarAlgebras.TheoremB

namespace DynamicalCStarAlgebras

/-- The strict coarse-space example is genuinely nonmetrizable, as stated in
the introduction: a ULF metric would force equality by Theorem B. -/
theorem maximalULF_not_metrizable :
    ¬ (maximalUniformlyLocallyFinite ℕ).IsMetrizable := by
  rintro ⟨m, hm⟩
  let := m
  have hulf : UniformlyLocallyFinite ℕ := coarse_uniformlyLocallyFinite_iff.mp
    (hm ▸ maximalUniformlyLocallyFinite_ulf ℕ)
  have he := quasiLocal_eq_coarseContinuityPoints hulf
  rw [← hm] at he
  exact quasiLocal_maximalULF_ssubset_continuityPoints.ne he

end DynamicalCStarAlgebras
