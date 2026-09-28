import DynamicalCStarAlgebras.OzawaFiniteObstruction

noncomputable section
open Classical
open scoped ENNReal

namespace DynamicalCStarAlgebras

/-- A single matrix factor inside the bounded matrix product. -/
def matrixFactorHom (n : ℕ) : Operator (Fin n) →⋆ₙₐ[ℂ] BoundedMatrixProduct where
  toFun a := lp.single ∞ n a
  map_zero' := lp.single_zero (E := fun n : ℕ => Operator (Fin n)) ∞ n
  map_add' a b := lp.single_add (E := fun n : ℕ => Operator (Fin n)) ∞ n a b
  map_smul' c a := lp.single_smul (𝕜 := ℂ) (E := fun n : ℕ => Operator (Fin n)) ∞ n c a
  map_mul' a b := by
    apply lp.ext
    funext k
    by_cases h : k = n
    · subst k; simp
    · simp [Pi.single_eq_of_ne h]
  map_star' a := by
    apply lp.ext
    funext k
    by_cases h : k = n
    · subst k; simp
    · simp [Pi.single_eq_of_ne h]

lemma matrixFactorHom_injective (n : ℕ) : Function.Injective (matrixFactorHom n) := by
  intro a b hab
  have h := congrArg (fun v : BoundedMatrixProduct => v n) hab
  simpa [matrixFactorHom] using h

/-- A bounded family of matrix coordinates can be prescribed on an injective
subsequence, setting the other coordinates to zero. -/
lemma exists_bounded_matrix_family (s : ℕ → ℕ) (hs : Function.Injective s)
    (a : ∀ k, Operator (Fin (s k))) (ha : ∀ k, ‖a k‖ ≤ 1) :
    ∃ A : BoundedMatrixProduct, ‖A‖ ≤ 1 ∧ ∀ k, A (s k) = a k := by
  let f (n : ℕ) : Operator (Fin n) :=
    if h : ∃ k, s k = n then h.choose_spec ▸ a h.choose else 0
  have hf (n : ℕ) : ‖f n‖ ≤ 1 := by
    dsimp [f]
    split_ifs with h
    · have hcast : ∀ {m n : ℕ} (he : m = n) (T : Operator (Fin m)),
          ‖he ▸ T‖ = ‖T‖ := by
        intro m n he T
        cases he
        rfl
      rw [hcast]
      exact ha h.choose
    · simp
  let A : BoundedMatrixProduct := ⟨f, memℓp_infty ⟨1, by rintro _ ⟨n, rfl⟩; exact hf n⟩⟩
  refine ⟨A, lp.norm_le_of_forall_le (by norm_num) hf, ?_⟩
  intro k
  change f (s k) = a k
  dsimp [f]
  split_ifs with h
  · have he : h.choose = k := hs h.choose_spec
    have hcast : ∀ {i k : ℕ} (he : i = k) (he' : s i = s k), he' ▸ a i = a k := by
      intro i k he he'
      cases he
      rfl
    exact hcast he h.choose_spec
  · exact (h ⟨k, rfl⟩).elim

set_option maxHeartbeats 800000 in
/-- Ozawa's bounded matrix product cannot embed in a uniformly locally finite
uniform Roe algebra having a countable cofinal family of controlled relations. -/
theorem boundedMatrixProduct_not_range_subset_uniformRoe_of_cofinal
    {X : Type*} (C : CoarseStructure X) (hC : C.UniformlyLocallyFinite)
    (E : ℕ → Set (X × X)) (hE : ∀ k, E k ∈ C.controlled)
    (hcofinal : ∀ F ∈ C.controlled, ∃ k, F ⊆ E k)
    (Φ : BoundedMatrixProduct →⋆ₙₐ[ℂ] Operator X) (hΦ : Function.Injective Φ) :
    ¬ ∀ A, Φ A ∈ uniformRoe C := by
  let : NonUnitalCStarAlgebra BoundedMatrixProduct := inferInstance
  intro hroe
  choose N hN using fun k => controlled_finite_matrix_obstruction C hC (E k) (hE k)
  obtain ⟨s, hs, hdim⟩ := Filter.extraction_forall_of_eventually
    (fun k : ℕ => Filter.eventually_gt_atTop ((6 * (N k) ^ 2) ^ 2))
  have hspos (k : ℕ) : 0 < s k := lt_of_le_of_lt (Nat.zero_le _) (hdim k)
  let Ψ (k : ℕ) := Φ.comp (matrixFactorHom (s k))
  have hΨ (k : ℕ) : Function.Injective (Ψ k) := hΦ.comp (matrixFactorHom_injective _)
  have hsize (k : ℕ) : 6 * (N k : ℝ) ^ 2 < Real.sqrt (Fintype.card (Fin (s k))) := by
    rw [Fintype.card_fin, Real.lt_sqrt (by positivity)]
    exact_mod_cast hdim k
  have ha (k : ℕ) := @hN k (Fin (s k)) inferInstance ⟨⟨0, hspos k⟩⟩ (hsize k) (Ψ k) (hΨ k)
  choose a ha hsep using ha
  obtain ⟨A, hA, hAs⟩ := exists_bounded_matrix_family s hs.injective a ha
  obtain ⟨c, hc, hdist⟩ := (Metric.mem_closure_iff.mp (hroe A)) (1 / 2) (by norm_num)
  obtain ⟨k, hk⟩ := hcofinal (operatorSupport c) hc
  let B := Φ (A - matrixFactorHom (s k) (a k))
  have hBnorm : ‖B‖ ≤ 1 := by
    rw [show B = Φ (A - matrixFactorHom (s k) (a k)) from rfl,
      NonUnitalStarAlgHom.norm_map Φ hΦ]
    apply lp.norm_le_of_forall_le (by norm_num)
    intro n
    by_cases hn : n = s k
    · subst n
      simp [matrixFactorHom, hAs]
    · simpa [matrixFactorHom, lp.coeFn_sub, Pi.single_eq_of_ne hn] using
        (lp.norm_apply_le_norm ENNReal.top_ne_zero A n).trans hA
  have hBunit : B * Ψ k 1 = 0 := by
    change Φ (A - matrixFactorHom (s k) (a k)) * Φ (matrixFactorHom (s k) 1) = 0
    rw [← map_mul]
    suffices (A - matrixFactorHom (s k) (a k)) * matrixFactorHom (s k) 1 = 0 by
      rw [this]
      exact Φ.map_zero
    apply lp.ext
    funext n
    change (A n - (matrixFactorHom (s k) (a k)) n) * (matrixFactorHom (s k) 1) n = 0
    by_cases hn : n = s k
    · subst n
      simp [matrixFactorHom, hAs]
    · simp [matrixFactorHom, Pi.single_eq_of_ne hn]
  have hcE (x y : X) (hxy : (x, y) ∉ E k) : matrixEntry c x y = 0 := by
    by_contra hne
    exact hxy (hk hne)
  have hfar := hsep k B hBnorm hBunit c hcE
  have heq : Ψ k (a k) + B = Φ A := by
    change Φ (matrixFactorHom (s k) (a k)) + Φ (A - matrixFactorHom (s k) (a k)) = Φ A
    exact (Φ.map_add' (matrixFactorHom (s k) (a k)) (A - matrixFactorHom (s k) (a k))).symm.trans
      (congrArg Φ (by abel_nf))
  rw [heq] at hfar
  have hclose : ‖Φ A - c‖ < (1 / 2 : ℝ) := by
    simpa [dist_eq_norm, norm_sub_rev] using hdist
  exact (not_lt_of_ge hfar) hclose

/-- Ozawa's nonembedding theorem: the bounded product of the complex matrix
algebras does not embed into the uniform Roe algebra of any uniformly locally
finite metric space. The statement permits nonunital embeddings. -/
theorem boundedMatrixProduct_not_range_subset_uniformRoe
    {X : Type*} [PseudoMetricSpace X] (hX : UniformlyLocallyFinite X)
    (Φ : BoundedMatrixProduct →⋆ₙₐ[ℂ] Operator X) (hΦ : Function.Injective Φ) :
    ¬ ∀ A, Φ A ∈ uniformRoe (CoarseStructure.ofPseudoMetric X) := by
  apply boundedMatrixProduct_not_range_subset_uniformRoe_of_cofinal
    (CoarseStructure.ofPseudoMetric X) (coarse_uniformlyLocallyFinite_iff.mpr hX)
    (fun n : ℕ => {p : X × X | dist p.1 p.2 ≤ (n : ℝ)})
    (fun n => ⟨n, fun _ hp => hp⟩) ?_ Φ hΦ
  intro F hF
  obtain ⟨R, hR⟩ := hF
  obtain ⟨n, hn⟩ := exists_nat_ge R
  exact ⟨n, fun p hp => (hR p hp).trans hn⟩

end DynamicalCStarAlgebras
