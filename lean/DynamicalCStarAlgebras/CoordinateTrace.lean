import DynamicalCStarAlgebras.NonmembershipPowers
noncomputable section
namespace DynamicalCStarAlgebras

def deltaBasis (X : Type*) [Fintype X] : OrthonormalBasis X ℂ (HilbertSpace X) :=
  (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (HilbertSpace X))).toOrthonormalBasis

lemma deltaBasis_apply {X : Type*} [Fintype X] (x : X) : deltaBasis X x = delta x := by
  exact congrFun (HilbertBasis.coe_toOrthonormalBasis _) x

instance finiteDimensional_hilbertSpace {X : Type*} [Fintype X] :
    FiniteDimensional ℂ (HilbertSpace X) := Module.Finite.of_basis (deltaBasis X).toBasis

lemma finrank_hilbertSpace {X : Type*} [Fintype X] :
    Module.finrank ℂ (HilbertSpace X) = Fintype.card X :=
  Module.finrank_eq_card_basis (deltaBasis X).toBasis

/-- The trace comparison expressed in the finite coordinate space of a graph component. -/
theorem coordinate_trace_power_ratio {X : Type*} [Fintype X]
    (a p : Operator X) (ha : IsSelfAdjoint a) (hp : IsStarProjection p)
    {δ α : ℝ} (hδ : δ ∈ Set.Ioo 0 1) (hap : ‖a - p‖ ≤ δ) (m : ℕ)
    (hN : 1 < (Fintype.card X : ℝ))
    (hrank : (Fintype.card X : ℝ) / (2 * Real.log (Fintype.card X) ^ (2 * α)) ≤
      Module.finrank ℂ (LinearMap.range p.toLinearMap))
    (hb : ∀ x, ‖(a ^ m) (delta x)‖ ≤ 2 * (2 * δ) ^ m) :
    ((1 - δ) / (2 * δ)) ^ (2 * m) ≤ 8 * Real.log (Fintype.card X) ^ (2 * α) := by
  let e := (Fintype.equivFin X).trans (finCongr (finrank_hilbertSpace (X := X)).symm)
  have h := trace_power_ratio_bound a p ha hp hδ hap m ((deltaBasis X).reindex e)
    (by simpa only [finrank_hilbertSpace] using hN)
    (by simpa only [finrank_hilbertSpace] using hrank)
    (fun i => by simpa only [OrthonormalBasis.reindex_apply, deltaBasis_apply] using hb (e.symm i))
  simpa only [finrank_hilbertSpace] using h

/-- The floor rank prescribed in Assumption.1 gives the lower bound used in Eq.Trace.Lower.bound. -/
theorem floor_rank_lower_bound {N L : ℝ} (hL : 0 < L) (hNL : L ≤ N) :
    N / (2 * L) ≤ (⌊N / L⌋₊ : ℝ) := by
  have hratio : 1 ≤ N / L := (le_div_iff₀ hL).mpr (by simpa using hNL)
  have hf : (1 : ℝ) ≤ ⌊N / L⌋₊ := by exact_mod_cast Nat.floor_pos.mpr hratio
  have hh := Nat.lt_floor_add_one (N / L)
  have he : N / (2 * L) = (N / L) / 2 := by ring
  rw [he]
  linarith

end DynamicalCStarAlgebras
