import DynamicalCStarAlgebras.QuasiLocalContinuity

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

/-- On a rectangle with constant height difference, the flow difference is scalar multiplication. -/
theorem compression_diagonalFlow_sub_of_constant_gap {X : Type*} (h : X → ℝ)
    (t r : ℝ) (a : Operator X) (A B : Set X)
    (hgap : ∀ x ∈ A, ∀ y ∈ B, h x - h y = r) :
    coordinateProjection A * (diagonalFlow h t a - a) * coordinateProjection B =
      (Complex.exp (((t * r : ℝ) : ℂ) * Complex.I) - 1) •
        (coordinateProjection A * a * coordinateProjection B) := by
  refine operator_ext fun x y => ?_
  change _ = (matrixEntryCLM x y) ((Complex.exp (((t * r : ℝ) : ℂ) * Complex.I) - 1) • _)
  simp only [map_smul, matrixEntryCLM_apply, matrixEntry_compression, smul_eq_mul]
  by_cases hp : x ∈ A ∧ y ∈ B
  · simp only [if_pos hp]
    change (matrixEntryCLM x y) (_ - _) = _
    simp only [map_sub, matrixEntryCLM_apply, matrixEntry_diagonalFlow, hgap x hp.1 y hp.2]
    ring
  · simp only [if_neg hp, mul_zero]

/-- A large compression at a constant height gap gives a lower bound on orbit displacement. -/
theorem compression_gap_flow_lower_bound {X : Type*} (h : X → ℝ) (t r : ℝ)
    (a : Operator X) (A B : Set X) (hgap : ∀ x ∈ A, ∀ y ∈ B, h x - h y = r) :
    ‖Complex.exp (((t * r : ℝ) : ℂ) * Complex.I) - 1‖ *
        ‖coordinateProjection A * a * coordinateProjection B‖ ≤ ‖diagonalFlow h t a - a‖ := by
  simpa only [compression_diagonalFlow_sub_of_constant_gap h t r a A B hgap, norm_smul]
    using compression_norm_le (diagonalFlow h t a - a) A B

/-- The final discontinuity argument in the non-quasi-local detection proposition.
Uniformly large compressions at integer height gaps prevent continuity at zero. -/
theorem not_continuityPoint_of_compression_gaps {X : Type*} (h : X → ℝ)
    (a : Operator X) {ε : ℝ} (hε : 0 < ε)
    (hblocks : ∀ n : ℕ, ∃ A B : Set X,
      ε ≤ ‖coordinateProjection A * a * coordinateProjection B‖ ∧
      ∀ x ∈ A, ∀ y ∈ B, h x - h y = (n : ℝ) + 1) :
    a ∉ continuityPoints h := by
  intro hc
  obtain ⟨δ, hδ, hcδ⟩ := Metric.continuousAt_iff.mp
    ((mem_continuityPoints_iff_continuousAt_zero h a).mp hc) ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.pi / δ)
  obtain ⟨A, B, hab, hgap⟩ := hblocks n
  let t : ℝ := Real.pi / ((n : ℝ) + 1)
  have htpos : 0 < t := div_pos Real.pi_pos (by positivity)
  have ht : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
    have hn' := (div_lt_iff₀ hδ).mp hn
    nlinarith
  have hphase : ‖Complex.exp (((t * ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) - 1‖ = 2 := by
    rw [show t * ((n : ℝ) + 1) = Real.pi from div_mul_cancel₀ _ (by positivity),
      Complex.exp_pi_mul_I]
    norm_num
  have hl := compression_gap_flow_lower_bound h t ((n : ℝ) + 1) a A B hgap
  have hu := hcδ ht
  rw [hphase] at hl
  rw [diagonalFlow_zero, dist_eq_norm] at hu
  linarith

end DynamicalCStarAlgebras
