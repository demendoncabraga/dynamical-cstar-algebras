import DynamicalCStarAlgebras.StrictDecayInclusions

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- Positive vertex expansion connects every pair of vertices, including the
vacuous statement for an empty vertex set. -/
theorem HasVertexExpansion.preconnected {X : Type*} [Fintype X]
    {G : SimpleGraph X} {γ : ℝ} (hG : HasVertexExpansion G γ) (hγ : 0 < γ) :
    G.Preconnected := by
  intro x y
  by_contra hxy
  let A : Finset X := Finset.univ.filter (G.Reachable x)
  have hx : x ∈ A := by simp [A]
  have hy : y ∈ Aᶜ := by simpa [A] using hxy
  have hbA : graphBoundary G A = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨hzN, hzA⟩ := Finset.mem_sdiff.mp hz
    obtain hzA' | ⟨w, hw, hzw⟩ := (Finset.mem_filter.mp hzN).2
    · exact hzA hzA'
    · apply hzA
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((Finset.mem_filter.mp hw).2).trans hzw.reachable⟩
  have hbAc : graphBoundary G Aᶜ = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨hzN, hzA⟩ := Finset.mem_sdiff.mp hz
    obtain hzA' | ⟨w, hw, hzw⟩ := (Finset.mem_filter.mp hzN).2
    · exact hzA hzA'
    · have hz : z ∈ A := by simpa using hzA
      have hw' : w ∉ A := Finset.mem_compl.mp hw
      apply hw'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((Finset.mem_filter.mp hz).2).trans hzw.symm.reachable⟩
  have hcard : (A.card : ℝ) + (Aᶜ.card : ℝ) = Fintype.card X := by
    exact_mod_cast Finset.card_add_card_compl A
  rcases le_total (A.card : ℝ) (Fintype.card X / 2) with h | h
  · have hb := hG A h
    rw [hbA, Finset.card_empty, Nat.cast_zero] at hb
    have hpos : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr ⟨x, hx⟩
    nlinarith
  · have hb := hG Aᶜ (by linarith)
    rw [hbAc, Finset.card_empty, Nat.cast_zero] at hb
    have hpos : (0 : ℝ) < Aᶜ.card := by exact_mod_cast Finset.card_pos.mpr ⟨y, hy⟩
    nlinarith

/-- The source automatic-connectedness assertion for nonempty finite graphs. -/
theorem HasVertexExpansion.connected {X : Type*} [Fintype X] [Nonempty X]
    {G : SimpleGraph X} {γ : ℝ} (hG : HasVertexExpansion G γ) (hγ : 0 < γ) :
    G.Connected := ⟨hG.preconnected hγ⟩

end DynamicalCStarAlgebras
