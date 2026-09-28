import DynamicalCStarAlgebras.ComponentOperators

noncomputable section

namespace DynamicalCStarAlgebras

open Classical

/-- Exponential decay gives strip analyticity for a block-diagonal operator on finite graph fibers. -/
theorem graph_blockDiagonal_strip {X I : Type*} [PseudoMetricSpace X]
    (π : X → I) [∀ i, Fintype {x : X // π x = i}]
    (G : ∀ i, SimpleGraph {x : X // π x = i}) (hG : ∀ i, (G i).Connected)
    (hmetric : ∀ i (x y : {x : X // π x = i}),
      dist (x : X) (y : X) = ((G i).dist x y : ℝ))
    (a : Operator X) (ha : ‖a‖ ≤ 1)
    (hdiag : ∀ x y, π x ≠ π y → matrixEntry a x y = 0)
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hdecay : ∀ r : ℝ, 0 < r → quasiLocalModulus a r ≤ C * Real.exp (-c * r))
    (h : X → ℝ) (hh : IsCoarseReal (CoarseStructure.ofPseudoMetric X) h) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ F, IsStripExtension h a δ F := by
  obtain ⟨A, hA, B, hB, huniform⟩ := coarse_graph_uniform_moments h hh hc hC
  have hlocal (i : I) : ∃ b : ℕ → Operator {x : X // π x = i},
      IsDiagonalMomentSequence (fun x => h x.val)
        (componentOperator Subtype.val Subtype.val_injective a) b ∧
      ∀ k, ‖b k‖ ≤ A * B ^ k * k.factorial := by
    let inst : PseudoMetricSpace {x : X // π x = i} :=
      (connectedGraphMetric (G i) (hG i)).toPseudoMetricSpace
    have hedge : ∀ x y, (G i).Adj x y → dist (x : X) (y : X) ≤ 1 := by
      intro x y hxy
      rw [hmetric i]
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hxy]
      norm_num
    have hd := Isometry.of_dist_eq (hmetric i)
    obtain ⟨b, hm, hb, _⟩ := huniform (G i) (hG i) Subtype.val hedge
      (componentOperator Subtype.val Subtype.val_injective a)
      ((norm_componentOperator_le _ _ a).trans ha)
      (fun r hr => (quasiLocalModulus_componentOperator_le _ Subtype.val_injective hd a r).trans
        (hdecay r hr))
    exact ⟨b, hm, hb⟩
  choose b hm hb using hlocal
  let d : I → ℕ → Operator X := fun i k =>
    liftComponentOperator Subtype.val Subtype.val_injective (b i k)
  have hdm : ∀ i k x y, π x = i → π y = i → matrixEntry (d i k) x y =
      ((h x - h y : ℝ) : ℂ) ^ k * matrixEntry a x y := by
    intro i k x y hx hy
    have he := matrixEntry_liftComponentOperator_image Subtype.val Subtype.val_injective
      (b i k) ⟨x, hx⟩ ⟨y, hy⟩
    exact he.trans ((hm i k ⟨x, hx⟩ ⟨y, hy⟩).trans (by
      rw [matrixEntry_componentOperator]))
  have hdb : ∀ i k, ‖coordinateProjection {x | π x = i} * d i k *
      coordinateProjection {x | π x = i}‖ ≤ A * B ^ k * k.factorial :=
    fun i k => (compression_norm_le _ _ _).trans
      ((norm_liftComponentOperator_le _ _ _).trans (hb i k))
  have hpos : 0 < B⁻¹ / 2 := half_pos (inv_pos.mpr hB)
  exact ⟨B⁻¹ / 2, hpos, stripExtension_of_fiber_moments π h a d hA.le hB
    hdiag hdm hdb _ hpos (half_lt_self (inv_pos.mpr hB))⟩

/-- The diagonal graph-block part of an exponentially decaying contraction belongs to AP_strip. -/
theorem graph_blockDiagonal_part_mem_stripAnalyticPoints {X I : Type*} [PseudoMetricSpace X]
    (π : X → I) [∀ i, Fintype {x : X // π x = i}]
    (G : ∀ i, SimpleGraph {x : X // π x = i}) (hG : ∀ i, (G i).Connected)
    (hmetric : ∀ i (x y : {x : X // π x = i}),
      dist (x : X) (y : X) = ((G i).dist x y : ℝ))
    (a : Operator X) (ha : ‖a‖ ≤ 1)
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hdecay : ∀ r : ℝ, 0 < r → quasiLocalModulus a r ≤ C * Real.exp (-c * r)) :
    ∃ b : Operator X, ‖b‖ ≤ ‖a‖ ∧
      (∀ x y, matrixEntry b x y = if π x = π y then matrixEntry a x y else 0) ∧
      b ∈ stripAnalyticPoints (CoarseStructure.ofPseudoMetric X) := by
  obtain ⟨b, hb, he, hmod⟩ := exists_blockDiagonal_modulus_le π a
  refine ⟨b, hb, he, subset_closure ?_⟩
  intro h hh
  apply graph_blockDiagonal_strip π G hG hmetric b (hb.trans ha)
    (fun x y hxy => (he x y).trans (if_neg hxy)) hc hC
    (fun r hr => (hmod r).trans (hdecay r hr)) h hh

end DynamicalCStarAlgebras
