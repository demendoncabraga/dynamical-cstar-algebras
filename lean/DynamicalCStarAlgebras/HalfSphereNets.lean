import DynamicalCStarAlgebras.GeodesicGrowth
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- The volumetric bound for a half-separated unit-sphere set, used in the
half-net argument of Li--Zhang--Zhu, Proposition 6.3 (arXiv:2608.22439v2). -/
lemma halfSeparated_sphere_card_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (s : Finset E)
    (hs : ∀ x ∈ s, ‖x‖ = 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1 / 2 : ℝ) < ‖x - y‖) :
    s.card ≤ 5 ^ Module.finrank ℝ E := by
  have hinj : Function.Injective (fun x : E => (2 : ℝ) • x) :=
    smul_right_injective E (by norm_num : (2 : ℝ) ≠ 0)
  have hbound := Besicovitch.card_le_of_separated (s.image fun x => (2 : ℝ) • x) ?_ ?_
  · simpa only [Finset.card_image_of_injective _ hinj] using hbound
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simp [norm_smul, hs y hy]
  · intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have huv : u ≠ v := fun h => hxy (congrArg (fun z => (2 : ℝ) • z) h)
    rw [← smul_sub, norm_smul]
    norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [hsep u hu v hv huv]

/-- A half-net in the unit sphere has cardinality at most five to the real dimension. -/
theorem exists_half_net_sphere_real {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ s : Finset E, (∀ x ∈ s, ‖x‖ = 1) ∧ s.card ≤ 5 ^ Module.finrank ℝ E ∧
      ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x - y‖ ≤ (1 / 2 : ℝ) := by
  let P (s : Finset E) : Prop := (∀ x ∈ s, ‖x‖ = 1) ∧
    ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1 / 2 : ℝ) < ‖x - y‖
  let sizes : Set ℕ := {n | ∃ s : Finset E, P s ∧ s.card = n}
  have hnonempty : sizes.Nonempty := ⟨0, ∅, by simp [P], rfl⟩
  have hbounded : BddAbove sizes := by
    refine ⟨5 ^ Module.finrank ℝ E, ?_⟩
    rintro n ⟨s, hs, rfl⟩
    exact halfSeparated_sphere_card_le s hs.1 hs.2
  obtain ⟨n, hn, hmax⟩ := hbounded.exists_isGreatest_of_nonempty hnonempty
  obtain ⟨s, hs, hcard⟩ := hn
  refine ⟨s, hs.1, halfSeparated_sphere_card_le s hs.1 hs.2, ?_⟩
  intro x hx
  by_contra hcover
  push Not at hcover
  have hnot : x ∉ s := by
    intro hmem
    have hh := hcover x hmem
    norm_num at hh
  have hnew : P (insert x s) := by
    constructor
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hs.1 y hy
    · intro u hu v hv huv
      rcases Finset.mem_insert.mp hu with rfl | huS
      · rcases Finset.mem_insert.mp hv with rfl | hvS
        · exact (huv rfl).elim
        · exact hcover v hvS
      · rcases Finset.mem_insert.mp hv with rfl | hvS
        · simpa only [norm_sub_rev] using hcover u huS
        · exact hs.2 u huS v hvS huv
  have hh := hmax (show (insert x s).card ∈ sizes from ⟨insert x s, hnew, rfl⟩)
  rw [Finset.card_insert_of_notMem hnot, hcard] at hh
  omega

/-- The complex half-net of cardinality `5^(2k)` used in the cited frame-subspace proof. -/
theorem exists_half_net_sphere_complex {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] :
    ∃ s : Finset E, (∀ x ∈ s, ‖x‖ = 1) ∧ s.card ≤ 5 ^ (2 * Module.finrank ℂ E) ∧
      ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x - y‖ ≤ (1 / 2 : ℝ) := by
  let := NormedSpace.restrictScalars ℝ ℂ E
  simpa only [finrank_real_of_complex] using (exists_half_net_sphere_real (E := E))

/-- The exact factor-two operator norm reduction for a half-net, as in Eq. (6.7)
of Li--Zhang--Zhu, Proposition 6.3. -/
lemma opNorm_le_two_of_half_net {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (s : Finset E) (hnet : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x - y‖ ≤ (1 / 2 : ℝ))
    (T : E →L[ℂ] F) {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ y ∈ s, ‖T y‖ ≤ M) :
    ‖T‖ ≤ 2 * M := by
  have hnorm : ‖T‖ ≤ M + ‖T‖ / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnet x hx
    calc
      ‖T x‖ ≤ ‖T y‖ + ‖T x - T y‖ := norm_le_norm_add_norm_sub' (T x) (T y)
      _ ≤ M + ‖T‖ * (1 / 2) := by
        apply add_le_add (hbound y hy)
        rw [← map_sub]
        exact (T.le_opNorm (x - y)).trans (mul_le_mul_of_nonneg_left hxy (norm_nonneg _))
      _ = _ := by ring
  linarith

end DynamicalCStarAlgebras
