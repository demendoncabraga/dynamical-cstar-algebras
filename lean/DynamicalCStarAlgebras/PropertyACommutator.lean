import DynamicalCStarAlgebras.PropertyASigns

noncomputable section
open Classical
namespace DynamicalCStarAlgebras
namespace FiniteProbabilityKernel
variable {X : Type*} (μ ν : FiniteProbabilityKernel X)

/-- The clipped convolution as a bounded real diagonal. -/
def smoothedSignDiagonal {t : ℝ} (ht : 0 < t) (s : Finset X) (σ : s → Bool) : BoundedDiagonal X :=
  boundedRealDiagonal (μ.smoothedSign ν s t σ) t⁻¹ (μ.smoothedSign_abs_le ν ht s σ)


/-- The precise uniform commutator bound in Ozawa's property-A argument, with
`t` equal to the fourth root of the quasi-locality error. -/
lemma smoothedSign_commutator_le {t : ℝ} (ht : 0 < t) (s : Finset X) (σ : s → Bool)
    (a : Operator X) (ha : ‖a‖ ≤ 1) {E : Set (X × X)} (haE : IsQuasiLocalAt a (t ^ 4) E)
    (hμ : ∀ p ∈ E, μ.variation p.1 p.2 ≤ t ^ 2) :
    ‖diagonalCommutator (μ.smoothedSignDiagonal ν ht s σ) a‖ ≤ 12 * t := by
  let h := μ.smoothedSign ν s t σ
  let g : X → ℝ := fun x => (h x + t⁻¹) * t / 2
  have hgt (x : X) : 0 ≤ g x ∧ g x ≤ 1 := by
    have hx := abs_le.mp (μ.smoothedSign_abs_le ν ht s σ x)
    have hm := mul_le_mul_of_nonneg_right hx.2 ht.le
    have hm' := mul_le_mul_of_nonneg_right hx.1 ht.le
    dsimp [g, h]
    have hti : t⁻¹ * t = 1 := inv_mul_cancel₀ ht.ne'
    constructor <;> nlinarith
  have hgvar : ∀ p ∈ E, |g p.1 - g p.2| ≤ t ^ 2 / 2 := by
    intro p hp
    have he : g p.1 - g p.2 = (h p.1 - h p.2) * t / 2 := by dsimp [g]; ring
    rw [he, abs_div, abs_mul, abs_of_pos ht, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hv := μ.smoothedSign_variation_le ν ht s σ p.1 p.2 (hμ p hp)
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hv ht.le) (by norm_num)).trans_eq
      (by ring)
  let G := boundedRealDiagonal g 1 (fun x => (abs_of_nonneg (hgt x).1).trans_le (hgt x).2)
  have he : diagonalCommutator (μ.smoothedSignDiagonal ν ht s σ) a =
      ((2 / t : ℝ) : ℂ) • diagonalCommutator G a := by
    refine operator_ext fun x y => ?_
    change _ = (matrixEntryCLM x y) (((2 / t : ℝ) : ℂ) • diagonalCommutator G a)
    simp only [map_smul, matrixEntryCLM_apply, matrixEntry_diagonalCommutator,
      smoothedSignDiagonal, boundedRealDiagonal_apply, boundedRealDiagonal_apply, G, g, h, smul_eq_mul]
    push_cast
    field_simp [ht.ne', Complex.ofReal_ne_zero.mpr ht.ne']
    ring
  have hb := quasiLocal_commutator_bound g hgt (show 0 < t ^ 2 / 2 by positivity)
    (show 0 ≤ t ^ 4 by positivity) a haE hgvar
  have hb' : ‖diagonalCommutator G a‖ ≤ 6 * t ^ 2 := by
    have hz : 4 * (t ^ 2 / 2) * ‖a‖ + 2 * (t ^ 2 / 2)⁻¹ * t ^ 4 ≤ 6 * t ^ 2 := by
      have ht0 := ht.ne'
      field_simp
      nlinarith [mul_le_mul_of_nonneg_right ha (sq_nonneg t)]
    exact hb.trans hz
  rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) ht)]
  exact (mul_le_mul_of_nonneg_left hb' (by positivity)).trans_eq (by field_simp; ring)

end FiniteProbabilityKernel
end DynamicalCStarAlgebras
