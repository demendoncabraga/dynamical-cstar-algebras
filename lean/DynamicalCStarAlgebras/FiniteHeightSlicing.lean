import DynamicalCStarAlgebras.SlicingEstimate

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

/-- Package a real height on a finite set as a bounded diagonal. -/
def finiteRealDiagonal {X : Type*} [Fintype X] (h : X → ℝ) : BoundedDiagonal X :=
  boundedRealDiagonal h (∑ x, |h x|)
    (fun x => Finset.single_le_sum (fun y _ => abs_nonneg (h y)) (Finset.mem_univ x))

@[simp] theorem finiteRealDiagonal_apply {X : Type*} [Fintype X] (h : X → ℝ) (x : X) :
    finiteRealDiagonal h x = (h x : ℂ) := boundedRealDiagonal_apply _ _ _ _

/-- Every operator on a finite pseudometric space has finite propagation. -/
theorem hasFinitePropagation_of_finite {X : Type*} [PseudoMetricSpace X] [Finite X]
    (a : Operator X) : HasFinitePropagation a := by
  refine ⟨max (Metric.diam (Set.univ : Set X)) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x y hxy
  have hd := Metric.dist_le_diam_of_mem (Set.toFinite (Set.univ : Set X)).isBounded
    (Set.mem_univ x) (Set.mem_univ y)
  exact False.elim ((not_lt_of_ge (hd.trans (le_max_left _ _))) hxy)

/-- Finite spaces have summable quasi-locality moments of every order. -/
theorem summable_quasiLocal_moment_of_finite {X : Type*} [PseudoMetricSpace X] [Finite X]
    (a : Operator X) (k : ℕ) :
    Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ k * quasiLocalModulus a (n + 2)) := by
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp
    ((finitePropagation_iff_modulus_eventually_zero a).mp (hasFinitePropagation_of_finite a))
  obtain ⟨N, hN⟩ := exists_nat_gt R
  refine summable_of_ne_finset_zero (s := Finset.range N) fun n hn => ?_
  have hNn : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
  have hh : (N : ℝ) ≤ n := by exact_mod_cast hNn
  rw [hR (n + 2) (by linarith), mul_zero]

/-- The rounding remainder lies in the interval [0,L), hence has diagonal norm at most L. -/
theorem finite_rounding_remainder_norm_le {X : Type*} [Fintype X] (h : X → ℝ)
    {L : ℝ} (hL : 0 < L) :
    ‖finiteRealDiagonal (fun x => h x - L * (⌊h x / L⌋ : ℝ))‖ ≤ L := by
  refine lp.norm_le_of_forall_le hL.le fun x => ?_
  rw [finiteRealDiagonal_apply, Complex.norm_real, Real.norm_eq_abs]
  have hlo : L * (⌊h x / L⌋ : ℝ) ≤ h x := by
    simpa only [mul_comm] using (le_div_iff₀ hL).mp (Int.floor_le (h x / L))
  have hhi : h x < L * ((⌊h x / L⌋ : ℝ) + 1) := by
    simpa only [mul_comm] using (div_lt_iff₀ hL).mp (Int.lt_floor_add_one (h x / L))
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

/-- The exact slicing estimate on finite spaces with integer-valued distances. -/
theorem finite_integer_slicing_estimate_pos {X : Type*} [PseudoMetricSpace X] [Fintype X]
    (hdisc : ∀ x y : X, ∃ n : ℕ, dist x y = n) (h : X → ℝ) {L : NNReal}
    (hL : 0 < L) (hh : LipschitzWith L h) (a : Operator X) (k : ℕ) :
    ‖(diagonalCommutator (finiteRealDiagonal h))^[k] a‖ ≤
      2 * (3 * (L : ℝ)) ^ k *
        (‖a‖ + ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ k * quasiLocalModulus a (n + 2)) := by
  let φ : X → ℤ := fun x => ⌊h x / (L : ℝ)⌋
  let f := finiteRealDiagonal (fun x => (L : ℝ) * (φ x : ℝ))
  let g := finiteRealDiagonal (fun x => h x - (L : ℝ) * (φ x : ℝ))
  have he : finiteRealDiagonal h = f + g := by
    apply lp.ext
    funext x
    simp only [f, g, finiteRealDiagonal_apply, lp.coeFn_add, Pi.add_apply]
    push_cast
    ring
  rw [he]
  refine norm_iterate_sliced_height_le hdisc hL hh f g ?_
    (finite_rounding_remainder_norm_le h hL) (Finset.univ.image φ)
    (Finset.univ.image (fun p : X × X => φ p.1 - φ p.2)) ?_ ?_ a k
    (summable_quasiLocal_moment_of_finite a k)
  · intro x
    simp only [f, finiteRealDiagonal_apply, Complex.ofReal_mul, Complex.ofReal_intCast]
    rfl
  · intro x
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  · intro x y
    exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_univ _, rfl⟩

/-- The finite integer-metric slicing estimate also includes constant heights (L=0). -/
theorem finite_integer_slicing_estimate {X : Type*} [PseudoMetricSpace X] [Fintype X]
    (hdisc : ∀ x y : X, ∃ n : ℕ, dist x y = n) (h : X → ℝ) {L : NNReal}
    (hh : LipschitzWith L h) (a : Operator X) (k : ℕ) (hk : 0 < k) :
    ‖(diagonalCommutator (finiteRealDiagonal h))^[k] a‖ ≤
      2 * (3 * (L : ℝ)) ^ k *
        (‖a‖ + ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ k * quasiLocalModulus a (n + 2)) := by
  rcases eq_or_lt_of_le L.zero_le_coe with hL | hL
  · have he : (diagonalCommutator (finiteRealDiagonal h))^[k] a = 0 := by
      apply operator_ext
      intro x y
      have hc : h x = h y := dist_le_zero.mp (by simpa only [← hL, zero_mul] using hh.dist_le_mul x y)
      rw [matrixEntry_iterate_diagonalCommutator, finiteRealDiagonal_apply,
        finiteRealDiagonal_apply, hc, sub_self, zero_pow hk.ne', zero_mul]
      rfl
    rw [he, norm_zero]
    simp only [← hL, mul_zero, zero_pow hk.ne', zero_mul, le_refl]
  · exact finite_integer_slicing_estimate_pos hdisc h hL hh a k

end DynamicalCStarAlgebras
