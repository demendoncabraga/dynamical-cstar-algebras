import DynamicalCStarAlgebras.QuasiLocalSubstructure

noncomputable section
namespace DynamicalCStarAlgebras

/-- The manuscript's half-open height bands `[(i-1)s,is)`. -/
def heightBand {X : Type*} (h : X → ℝ) (s : ℝ) (i : ℤ) : Set X :=
  h ⁻¹' Set.Ico (((i : ℝ) - 1) * s) ((i : ℝ) * s)

lemma mem_heightBand_iff_floor {X : Type*} (h : X → ℝ) {s : ℝ} (hs : 0 < s)
    (i : ℤ) (x : X) : x ∈ heightBand h s i ↔ ⌊h x / s⌋ = i - 1 := by
  rw [Int.floor_eq_iff]
  simp only [heightBand, Set.mem_preimage, Set.mem_Ico, Int.cast_sub, Int.cast_one,
    sub_add_cancel, le_div_iff₀ hs, div_lt_iff₀ hs]

/-- Claim at line 829: a nonzero block joins adjacent height bands, and its
entire input-output rectangle misses the original entourage. -/
theorem height_band_nonzero_compression {X : Type*} (h : X → ℝ) {s : ℝ} (hs : 0 < s)
    (a : Operator X) (hprop : ∀ x y, s < |h x - h y| → matrixEntry a x y = 0)
    (A B : Set X) (F : Set (X × X))
    (hAB : Disjoint (A ×ˢ B) (F ∩ {p | |h p.1 - h p.2| ≤ 2 * s}))
    (i j : ℤ)
    (hne : coordinateProjection (heightBand h s i ∩ A) * a *
      coordinateProjection (heightBand h s j ∩ B) ≠ 0) :
    |i - j| ≤ 1 ∧ Disjoint ((heightBand h s i ∩ A) ×ˢ (heightBand h s j ∩ B)) F := by
  have hex : ∃ x ∈ heightBand h s i ∩ A, ∃ y ∈ heightBand h s j ∩ B,
      matrixEntry a x y ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hne (compression_eq_zero_of_entries a _ _ hn)
  obtain ⟨x, hx, y, hy, hxy⟩ := hex
  have hdist : |h x - h y| ≤ s := le_of_not_gt fun hgt => hxy (hprop x y hgt)
  have hgap : |i - j| ≤ (1 : ℤ) := by
    have hh := floor_mesh_gap_le_one hs hdist
    rw [(mem_heightBand_iff_floor h hs i x).mp hx.1,
      (mem_heightBand_iff_floor h hs j y).mp hy.1] at hh
    simpa only [sub_sub_sub_cancel_right] using hh
  refine ⟨hgap, Set.disjoint_left.mpr ?_⟩
  rintro ⟨u, v⟩ ⟨hu, hv⟩ huv
  apply Set.disjoint_left.mp hAB ⟨hu.2, hv.2⟩
  refine ⟨huv, abs_sub_le_two_mul_of_floor_mesh_gap hs ?_⟩
  rw [(mem_heightBand_iff_floor h hs i u).mp hu.1,
    (mem_heightBand_iff_floor h hs j v).mp hv.1]
  simpa only [sub_sub_sub_cancel_right] using hgap

end DynamicalCStarAlgebras
