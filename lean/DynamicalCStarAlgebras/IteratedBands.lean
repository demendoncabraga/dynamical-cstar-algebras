import DynamicalCStarAlgebras.MomentStrip

noncomputable section

namespace DynamicalCStarAlgebras

/-- The integer-band expansion holds for every iterated commutator, including order zero. -/
theorem iterate_diagonalCommutator_eq_sum_integerBand {X : Type*} (f : BoundedDiagonal X)
    (φ : X → ℤ) (s t : Finset ℤ) (a : Operator X) (L : ℝ)
    (hf : ∀ x, f x = (L : ℂ) * (φ x : ℂ)) (hs : ∀ x, φ x ∈ s)
    (ht : ∀ x y, φ x - φ y ∈ t) (k : ℕ) :
    (diagonalCommutator f)^[k] a =
      ∑ m ∈ t, (((L : ℂ) * (m : ℂ)) ^ k) • integerBand φ s a m := by
  refine operator_ext fun x y => ?_
  change _ = (matrixEntryCLM x y) (∑ m ∈ t, _)
  simp only [map_sum, map_smul, matrixEntryCLM_apply, matrixEntry_integerBand φ s a _ _ _ (hs y),
    smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, ht x y, if_true,
    matrixEntry_iterate_diagonalCommutator, hf, Int.cast_sub, mul_sub]

/-- On integer-valued distances, rounding an L-Lipschitz height in mesh L preserves separation. -/
theorem floor_height_index_le_distance {X : Type*} [PseudoMetricSpace X] {h : X → ℝ}
    {L : NNReal} (hL : 0 < L) (hh : LipschitzWith L h) (x y : X)
    (hd : ∃ n : ℕ, dist x y = n) :
    ((|⌊h x / (L : ℝ)⌋ - ⌊h y / (L : ℝ)⌋| : ℤ) : ℝ) ≤ dist x y := by
  obtain ⟨n, hn⟩ := hd
  have hpos : 0 < (L : ℝ) := hL
  have hb : |h x - h y| ≤ (L : ℝ) * n := by
    simpa only [Real.dist_eq, hn] using hh.dist_le_mul x y
  have hp : h x / (L : ℝ) ≤ h y / (L : ℝ) + n := by
    apply (div_le_iff₀ hpos).mpr
    rw [add_mul, div_mul_cancel₀ _ hpos.ne']
    linarith [(abs_le.mp hb).2]
  have hm : h y / (L : ℝ) ≤ h x / (L : ℝ) + n := by
    apply (div_le_iff₀ hpos).mpr
    rw [add_mul, div_mul_cancel₀ _ hpos.ne']
    linarith [(abs_le.mp hb).1]
  have hp' : ⌊h x / (L : ℝ)⌋ ≤ ⌊h y / (L : ℝ)⌋ + n := by
    simpa only [Int.floor_add_natCast] using Int.floor_mono hp
  have hm' : ⌊h y / (L : ℝ)⌋ ≤ ⌊h x / (L : ℝ)⌋ + n := by
    simpa only [Int.floor_add_natCast] using Int.floor_mono hm
  rw [hn]
  exact_mod_cast (show |⌊h x / (L : ℝ)⌋ - ⌊h y / (L : ℝ)⌋| ≤ (n : ℤ) from
    abs_le.mpr ⟨by omega, by omega⟩)

/-- Integer-metric level bands are bounded by the quasi-locality modulus at their index gap. -/
theorem norm_integer_floor_band_le_modulus {X : Type*} [PseudoMetricSpace X]
    (hdisc : ∀ x y : X, ∃ n : ℕ, dist x y = n) {h : X → ℝ} {L : NNReal}
    (hL : 0 < L) (hh : LipschitzWith L h) (s : Finset ℤ) (a : Operator X) (m : ℤ) :
    ‖integerBand (fun x => ⌊h x / (L : ℝ)⌋) s a m‖ ≤ quasiLocalModulus a |(m : ℝ)| := by
  refine norm_integerBand_le _ s a m (quasiLocalModulus_nonneg _ _) fun j _ => ?_
  refine (quasiLocalModulus_le_iff a |(m : ℝ)| _).mp le_rfl _ _ ?_
  intro x hx y hy
  have hd := floor_height_index_le_distance hL hh x y (hdisc x y)
  change ⌊h x / (L : ℝ)⌋ = j + m at hx
  change ⌊h y / (L : ℝ)⌋ = j at hy
  simpa only [hx, hy, add_sub_cancel_left, Int.cast_abs] using hd

/-- The binomial identity for commuting diagonal derivations, proved entrywise. -/
theorem iterate_diagonalCommutator_add {X : Type*} (f g : BoundedDiagonal X)
    (a : Operator X) (k : ℕ) :
    (diagonalCommutator (f + g))^[k] a =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) •
        (diagonalCommutator f)^[j] ((diagonalCommutator g)^[k - j] a) := by
  refine operator_ext fun x y => ?_
  change _ = (matrixEntryCLM x y) (∑ j ∈ Finset.range (k + 1), _)
  simp only [map_sum, map_smul, matrixEntryCLM_apply, smul_eq_mul,
    matrixEntry_iterate_diagonalCommutator, lp.coeFn_add, Pi.add_apply]
  rw [show f x + g x - (f y + g y) = (f x - f y) + (g x - g y) by ring, add_pow,
    Finset.sum_mul]
  exact Finset.sum_congr rfl (fun j _ => by ring)

end DynamicalCStarAlgebras
