import DynamicalCStarAlgebras.LipschitzBaire

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

/-- The cross-boundary estimate behind the finite-set Lipschitz gluing construction. -/
theorem lipschitz_gluing_gap {X : Type*} [PseudoMetricSpace X]
    (h g : X → ℝ) (hh : LipschitzWith 1 h) (hg : LipschitzWith 1 g)
    (S : Finset X) {D : ℝ} (hD : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D)
    {z : X} (hz : z ∈ S) (hmax : ∀ y ∈ S, h y - g y / 2 ≤ h z - g z / 2)
    {x y : X} (hy : y ∈ S) (hfar : 3 * D ≤ dist x y) :
    |g x / 2 + (h z - g z / 2) - h y| ≤ dist x y := by
  have hgz : |g x - g z| ≤ dist x z := by simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hg.dist_le_mul x z
  have hgy : |g x - g y| ≤ dist x y := by simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hg.dist_le_mul x y
  have hhz : |h z - h y| ≤ dist z y := by simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hh.dist_le_mul z y
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hgy).1, hmax y hy, dist_nonneg (x := x) (y := y)],
    by linarith [(abs_le.mp hgz).2, (abs_le.mp hhz).2, hD z hz y hy,
      hD y hy z hz, dist_triangle x y z]⟩

/-- Glue prescribed finite values to a half-speed Lipschitz map outside a separated region. -/
theorem exists_lipschitz_gluing {X : Type*} [PseudoMetricSpace X]
    (h g : X → ℝ) (hh : LipschitzWith 1 h) (hg : LipschitzWith 1 g)
    (S : Finset X) (hS : S.Nonempty) (G : Set X) {D : ℝ}
    (hD : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D)
    (hfar : ∀ x ∉ G, ∀ y ∈ S, 3 * D ≤ dist x y) :
    ∃ (f : X → ℝ) (c : ℝ), LipschitzWith 1 f ∧
      (∀ x ∈ S, f x = h x) ∧ ∀ x ∉ G, f x = g x / 2 + c := by
  obtain ⟨z, hz, hmax⟩ := S.exists_max_image (fun x => h x - g x / 2) hS
  let c := h z - g z / 2
  let I := {x // x ∈ S} ⊕ {x // x ∉ G}
  let A : I → Set X := Sum.elim (fun x => {x.val}) (fun x => {x.val})
  let v : I → ℝ := Sum.elim (fun x => h x.val) (fun x => g x.val / 2 + c)
  have hv : ∀ i j, ∀ x ∈ A i, ∀ y ∈ A j, dist (v i) (v j) ≤ dist x y := by
    rintro (i | i) (j | j) x hx y hy
    · obtain rfl : x = i.val := hx
      obtain rfl : y = j.val := hy
      simpa only [v, Sum.elim_inl, NNReal.coe_one, one_mul] using hh.dist_le_mul i.val j.val
    · obtain rfl : x = i.val := hx
      obtain rfl : y = j.val := hy
      change dist (h i.val) (g j.val / 2 + c) ≤ dist i.val j.val
      rw [dist_comm, Real.dist_eq, dist_comm i.val j.val]
      exact lipschitz_gluing_gap h g hh hg S hD hz hmax i.property
        (hfar j.val j.property i.val i.property)
    · obtain rfl : x = i.val := hx
      obtain rfl : y = j.val := hy
      exact lipschitz_gluing_gap h g hh hg S hD hz hmax j.property
        (hfar i.val i.property j.val j.property)
    · obtain rfl : x = i.val := hx
      obtain rfl : y = j.val := hy
      change |(g i.val / 2 + c) - (g j.val / 2 + c)| ≤ _
      rw [add_sub_add_right_eq_sub, ← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hb := hg.dist_le_mul i.val j.val
      simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hb
      linarith [dist_nonneg (x := i.val) (y := j.val)]
  obtain ⟨f, hf, he⟩ := exists_lipschitz_prescribed_on_sets A v hv
  exact ⟨f, c, hf, fun x hx => he (.inl ⟨x, hx⟩) x rfl,
    fun x hx => he (.inr ⟨x, hx⟩) x rfl⟩

/-- Uniform weighted gluing outside a finite exceptional region, the gluing claim
in the proof of Theorem Band.In.Led. -/
theorem exists_uniform_weighted_gluing {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) (x₀ : X) (a : Operator X)
    (ha : ∀ h : X → ℝ, LipschitzWith 1 h →
      ∃ δ : ℝ, 0 < δ ∧ ∃ F, IsStripExtension h a δ F) :
    ∃ (n : ℕ) (G : Set X), G.Finite ∧ ∀ g : X → ℝ, LipschitzWith 1 g →
      ∃ (f : X → ℝ) (c : ℝ), LipschitzWith 1 f ∧
        HasWeightedOperatorBound a f ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) ∧
        ∀ x ∉ G, f x = g x / 2 + c := by
  obtain ⟨n, h₀, S, hx₀, hbound⟩ := weightedBound_finite_neighborhood x₀ a ha
  let D := Metric.diam (S : Set X)
  let G : Set X := ⋃ z ∈ (S : Set X), Metric.ball z (3 * D)
  have hG : G.Finite := S.finite_toSet.biUnion fun z _ =>
    (hX.finite_closedBall z (3 * D)).subset Metric.ball_subset_closedBall
  refine ⟨n, G, hG, fun g hg => ?_⟩
  have hD : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D := fun x hx y hy =>
    Metric.dist_le_diam_of_mem S.finite_toSet.isBounded hx hy
  have hfar : ∀ x ∉ G, ∀ y ∈ S, 3 * D ≤ dist x y := by
    intro x hx y hy
    exact le_of_not_gt fun hxy => hx (Set.mem_iUnion₂.mpr ⟨y, hy, hxy⟩)
  obtain ⟨f, c, hf, hS, he⟩ := exists_lipschitz_gluing h₀.val g h₀.property.1 hg S ⟨x₀, hx₀⟩ G hD hfar
  refine ⟨f, c, hf, ?_, he⟩
  exact hbound ⟨f, hf, (hS x₀ hx₀).trans h₀.property.2⟩ hS

end DynamicalCStarAlgebras
