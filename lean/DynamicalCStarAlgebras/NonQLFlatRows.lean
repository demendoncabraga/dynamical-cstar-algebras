import DynamicalCStarAlgebras.MaximalULFCoarse
import DynamicalCStarAlgebras.BlockAssembly
import DynamicalCStarAlgebras.FiniteRankRoe

noncomputable section
namespace DynamicalCStarAlgebras
open Classical

/-- A finite indicator vector in the canonical Hilbert space. -/
def finiteIndicatorVector {X : Type*} (S : Finset X) : HilbertSpace X :=
  ∑ x ∈ S, delta x

set_option backward.isDefEq.respectTransparency false in
lemma finiteIndicatorVector_apply {X : Type*} (S : Finset X) (x : X) :
    finiteIndicatorVector S x = if x ∈ S then 1 else 0 := by
  simp [finiteIndicatorVector, Finset.sum_apply, delta, lp.single_apply, Pi.single_apply]

lemma finiteIndicatorVector_norm_sq {X : Type*} (S : Finset X) :
    ‖finiteIndicatorVector S‖ ^ 2 = (S.card : ℝ) := by
  calc
    _ = ∑' x : X, ‖finiteIndicatorVector S x‖ ^ 2 := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) (finiteIndicatorVector S)
    _ = ∑ x ∈ S, ‖finiteIndicatorVector S x‖ ^ 2 :=
      tsum_eq_sum (fun x hx => by simp [finiteIndicatorVector_apply, hx])
    _ = ∑ _x ∈ S, (1 : ℝ) := Finset.sum_congr rfl fun x hx => by
      rw [finiteIndicatorVector_apply, if_pos hx]; norm_num
    _ = _ := by simp

lemma finiteIndicatorVector_norm {X : Type*} (S : Finset X) :
    ‖finiteIndicatorVector S‖ = Real.sqrt S.card := by
  rw [← finiteIndicatorVector_norm_sq S, Real.sqrt_sq (norm_nonneg _)]

/-- Successively longer, pairwise disjoint sets of coordinates in the natural numbers. -/
def flatRowBlock (n : ℕ) : Finset ℕ := (Finset.range (n + 1)).image (Nat.pair n)

lemma flatRowBlock_card (n : ℕ) : (flatRowBlock n).card = n + 1 := by
  rw [flatRowBlock, Finset.card_image_of_injective]
  · exact Finset.card_range _
  · intro i j hij
    have he := congrArg Nat.unpair hij
    simpa only [Nat.unpair_pair, Prod.mk.injEq, true_and] using he

lemma flatRowBlock_unpair {n x : ℕ} (hx : x ∈ flatRowBlock n) : (Nat.unpair x).1 = n := by
  obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hx
  simp only [Nat.unpair_pair]

/-- A unit vector constant on the nth finite block. -/
def flatRowVector (n : ℕ) : HilbertSpace ℕ :=
  ((Real.sqrt (n + 1))⁻¹ : ℂ) • finiteIndicatorVector (flatRowBlock n)

lemma flatRowVector_apply (n x : ℕ) : flatRowVector n x =
    if x ∈ flatRowBlock n then ((Real.sqrt (n + 1))⁻¹ : ℂ) else 0 := by
  simp only [flatRowVector, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, finiteIndicatorVector_apply,
    mul_ite, mul_one, mul_zero]

lemma flatRowVector_norm (n : ℕ) : ‖flatRowVector n‖ = 1 := by
  rw [flatRowVector, norm_smul, finiteIndicatorVector_norm, flatRowBlock_card]
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Nat.cast_add, Nat.cast_one]
  exact inv_mul_cancel₀ (by positivity : Real.sqrt ((n : ℝ) + 1) ≠ 0)

lemma delta_norm_eq_one {X : Type*} (x : X) : ‖delta x‖ = 1 := by
  simpa only [delta, norm_one] using lp.norm_single (E := fun _ : X => ℂ)
    (by norm_num : (0 : ENNReal) < 2) x (1 : ℂ)

/-- The operator with one uniform unit row in each disjoint block. -/
theorem exists_flat_rows_operator : ∃ a : Operator ℕ, ‖a‖ ≤ 1 ∧ ∀ n y,
    matrixEntry a (Nat.pair n 0) y =
      if y ∈ flatRowBlock n then ((Real.sqrt (n + 1))⁻¹ : ℂ) else 0 := by
  let q (n : ℕ) : Operator ℕ := InnerProductSpace.rankOne ℂ (delta (Nat.pair n 0)) (flatRowVector n)
  have hq (n : ℕ) : ‖q n‖ ≤ 1 := by
    simp only [q, InnerProductSpace.norm_rankOne, delta_norm_eq_one, flatRowVector_norm, one_mul,
      le_refl]
  obtain ⟨a, ha, he⟩ := exists_fiber_operator (fun x : ℕ => (Nat.unpair x).1) q
    (by norm_num : (0 : ℝ) ≤ 1)
    (fun n => (compression_norm_le (q n) _ _).trans (hq n))
  refine ⟨a, ha, fun n y => ?_⟩
  rw [he]
  simp only [Nat.unpair_pair]
  by_cases hy : y ∈ flatRowBlock n
  · rw [if_pos (flatRowBlock_unpair hy).symm, if_pos hy]
    simp [q, matrixEntry_rankOne, flatRowVector_apply, hy, delta, lp.single_apply]
  · rw [if_neg hy]
    split_ifs
    · simp only [q, matrixEntry_rankOne, flatRowVector_apply, hy, if_false, star_zero, mul_zero]
    · rfl

lemma sum_matrixEntry_row_norm_sq_le {X : Type*} (a : Operator X) (x : X) (S : Finset X) :
    ∑ y ∈ S, ‖matrixEntry a x y‖ ^ 2 ≤ ‖a‖ ^ 2 := by
  have hm (y : X) : (star a) (delta x) y = star (matrixEntry a x y) := matrixEntry_star a y x
  have hs : ∑ y ∈ S, ‖matrixEntry a x y‖ ^ 2 ≤ ‖(star a) (delta x)‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hm, norm_star] using
      lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ENNReal).toReal) ((star a) (delta x)) S
  have hn : ‖(star a) (delta x)‖ ≤ ‖a‖ := by
    convert (star a).le_opNorm (delta x) using 1
    rw [norm_star a, delta_norm_eq_one, mul_one]
  exact hs.trans (pow_le_pow_left₀ (norm_nonneg _) hn 2)

/-- Uniformly long flat rows cannot be quasi-local for any uniformly locally finite structure. -/
theorem flat_rows_not_quasiLocal (a : Operator ℕ)
    (hrows : ∀ n y, matrixEntry a (Nat.pair n 0) y =
      if y ∈ flatRowBlock n then ((Real.sqrt (n + 1))⁻¹ : ℂ) else 0)
    (C : CoarseStructure ℕ) (hC : C.UniformlyLocallyFinite) : a ∉ quasiLocal C := by
  intro ha
  obtain ⟨E, hE, hQL⟩ := ha (1 / 2) (by norm_num)
  obtain ⟨N, hN⟩ := hC.fiber_bounds hE
  let n : ℕ := 2 * N + 1
  let x := Nat.pair n 0
  let F := (hN x).1.toFinset
  let T := flatRowBlock n \ F
  have hFN : F.card ≤ N := by
    dsimp [F]
    rw [← Set.ncard_eq_toFinset_card {y | (x, y) ∈ E} (hN x).1]
    exact (hN x).2
  have hcard : n + 1 < 4 * T.card := by
    have hi : ((flatRowBlock n) ∩ F).card ≤ F.card :=
      Finset.card_le_card Finset.inter_subset_right
    have ht := Finset.card_sdiff_add_card_inter (flatRowBlock n) F
    rw [flatRowBlock_card] at ht
    dsimp [T, n] at *
    omega
  have hdisj : Disjoint (({x} : Set ℕ) ×ˢ (T : Set ℕ)) E := by
    apply Set.disjoint_left.mpr
    rintro ⟨u, v⟩ ⟨hu, hv⟩ huv
    have hux : u = x := hu
    subst u
    exact (Finset.mem_sdiff.mp hv).2 ((hN x).1.mem_toFinset.mpr huv)
  let b := coordinateProjection {x} * a * coordinateProjection (T : Set ℕ)
  have hb : ‖b‖ ≤ 1 / 2 := hQL {x} T hdisj
  have he (y : ℕ) (hy : y ∈ T) : matrixEntry b x y = ((Real.sqrt (n + 1))⁻¹ : ℂ) := by
    rw [show matrixEntry b x y = _ from matrixEntry_compression {x} T a x y,
      if_pos ⟨Set.mem_singleton x, hy⟩, hrows]
    exact if_pos (Finset.mem_sdiff.mp hy).1
  have hs : (T.card : ℝ) * (Real.sqrt ((n : ℝ) + 1))⁻¹ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    calc
      _ = ∑ y ∈ T, ‖matrixEntry b x y‖ ^ 2 := by
        rw [Finset.sum_congr rfl (fun y hy => congrArg (fun z : ℂ => ‖z‖ ^ 2) (he y hy))]
        simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), Finset.sum_const, nsmul_eq_mul]
      _ ≤ ‖b‖ ^ 2 := sum_matrixEntry_row_norm_sq_le b x T
      _ ≤ _ := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [inv_pow, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 1)] at hs
  have hh : (T.card : ℝ) ≤ (1 / 2 : ℝ) ^ 2 * ((n : ℝ) + 1) :=
    (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mp (by simpa only [div_eq_mul_inv] using hs)
  have hcardR : (n : ℝ) + 1 < 4 * (T.card : ℝ) := by exact_mod_cast hcard
  linarith

/-- The strictness assertion in Remark `RemarkContPointsCoarseSpaces`. -/
theorem quasiLocal_maximalULF_ssubset_continuityPoints :
    quasiLocal (maximalUniformlyLocallyFinite ℕ) ⊂
      coarseContinuityPoints (maximalUniformlyLocallyFinite ℕ) := by
  rw [coarseContinuityPoints_maximalUniformlyLocallyFinite]
  obtain ⟨a, _ha, hrows⟩ := exists_flat_rows_operator
  apply Set.ssubset_iff_subset_ne.mpr
  refine ⟨Set.subset_univ _, ?_⟩
  intro he
  have hm : a ∈ quasiLocal (maximalUniformlyLocallyFinite ℕ) := he ▸ Set.mem_univ a
  exact flat_rows_not_quasiLocal a hrows _ (maximalUniformlyLocallyFinite_ulf ℕ) hm

/-- The complete coarse-space counterexample in Remark `RemarkContPointsCoarseSpaces`. -/
theorem maximalULF_counterexample :
    (maximalUniformlyLocallyFinite ℕ).UniformlyLocallyFinite ∧
    (∀ C : CoarseStructure ℕ, C.UniformlyLocallyFinite →
      C.IsSubstructure (maximalUniformlyLocallyFinite ℕ)) ∧
    (∀ h : ℕ → ℝ, IsCoarseReal (maximalUniformlyLocallyFinite ℕ) h ↔
      ∃ M : ℝ, ∀ x, |h x| ≤ M) ∧
    coarseContinuityPoints (maximalUniformlyLocallyFinite ℕ) = Set.univ ∧
    quasiLocal (maximalUniformlyLocallyFinite ℕ) ⊂
      coarseContinuityPoints (maximalUniformlyLocallyFinite ℕ) :=
  ⟨maximalUniformlyLocallyFinite_ulf ℕ, maximalUniformlyLocallyFinite_maximal,
    isCoarseReal_maximalUniformlyLocallyFinite_iff,
    coarseContinuityPoints_maximalUniformlyLocallyFinite ℕ,
    quasiLocal_maximalULF_ssubset_continuityPoints⟩

end DynamicalCStarAlgebras
