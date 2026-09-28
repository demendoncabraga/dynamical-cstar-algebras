import DynamicalCStarAlgebras.WeightedOperatorBounds

noncomputable section

namespace DynamicalCStarAlgebras

/-- The normalized real 1-Lipschitz functions, with the inherited pointwise topology. -/
def normalizedLipschitzMaps {X : Type*} [PseudoMetricSpace X] (x₀ : X) : Set (X → ℝ) :=
  {h | LipschitzWith 1 h ∧ h x₀ = 0}

theorem isClosed_normalizedLipschitzMaps {X : Type*} [PseudoMetricSpace X] (x₀ : X) :
    IsClosed (normalizedLipschitzMaps x₀) :=
  (isClosed_setOfPred_lipschitzWith 1).inter (isClosed_eq (continuous_apply x₀) continuous_const)

/-- Tychonoff compactness of the normalized Lipschitz space, without countability assumptions. -/
theorem isCompact_normalizedLipschitzMaps {X : Type*} [PseudoMetricSpace X] (x₀ : X) :
    IsCompact (normalizedLipschitzMaps x₀) := by
  refine (isCompact_univ_pi (fun x : X =>
    isCompact_Icc (a := -dist x x₀) (b := dist x x₀))).of_isClosed_subset
    (isClosed_normalizedLipschitzMaps x₀) ?_
  intro h hh x _
  exact abs_le.mp (by simpa only [Real.dist_eq, hh.2, sub_zero, NNReal.coe_one, one_mul]
    using hh.1.dist_le_mul x x₀)

/-- The weighted-norm sets are closed and cover the normalized Lipschitz space
under the strip-analytic hypothesis in Theorem Band.In.Led. -/
theorem weightedBound_closed_cover {X : Type*} [PseudoMetricSpace X] (x₀ : X)
    (a : Operator X)
    (ha : ∀ h : X → ℝ, LipschitzWith 1 h →
      ∃ δ : ℝ, 0 < δ ∧ ∃ F, IsStripExtension h a δ F) :
    (∀ n : ℕ, IsClosed {h : normalizedLipschitzMaps x₀ |
      HasWeightedOperatorBound a h.val ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1)}) ∧
    (⋃ n : ℕ, {h : normalizedLipschitzMaps x₀ |
      HasWeightedOperatorBound a h.val ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1)}) = Set.univ := by
  constructor
  · exact fun n => (isClosed_hasWeightedOperatorBound a _ _).preimage continuous_subtype_val
  · apply Set.eq_univ_of_forall
    intro h
    obtain ⟨δ, hδ, F, hF⟩ := ha h.val h.property.1
    exact Set.mem_iUnion.mpr (hF.exists_weighted_bound hδ)

/-- Baire category supplies one weighted norm bound on a nonempty open set of
normalized Lipschitz maps, as required in the proof of Theorem Band.In.Led. -/
theorem weightedBound_has_interior {X : Type*} [PseudoMetricSpace X] (x₀ : X)
    (a : Operator X)
    (ha : ∀ h : X → ℝ, LipschitzWith 1 h →
      ∃ δ : ℝ, 0 < δ ∧ ∃ F, IsStripExtension h a δ F) :
    ∃ n : ℕ, (interior {h : normalizedLipschitzMaps x₀ |
      HasWeightedOperatorBound a h.val ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1)}).Nonempty := by
  let : CompactSpace (normalizedLipschitzMaps x₀) :=
    isCompact_iff_compactSpace.mp (isCompact_normalizedLipschitzMaps x₀)
  let : Nonempty (normalizedLipschitzMaps x₀) :=
    ⟨⟨fun _ => 0, (LipschitzWith.const (0 : ℝ)).weaken (by norm_num), rfl⟩⟩
  exact nonempty_interior_of_iUnion_of_closed (weightedBound_closed_cover x₀ a ha).1
    (weightedBound_closed_cover x₀ a ha).2

/-- Fixing finitely many coordinates suffices for one uniform weighted bound.
This is the consequence of the product-topology neighborhood needed by gluing. -/
theorem weightedBound_finite_neighborhood {X : Type*} [PseudoMetricSpace X] (x₀ : X)
    (a : Operator X)
    (ha : ∀ h : X → ℝ, LipschitzWith 1 h →
      ∃ δ : ℝ, 0 < δ ∧ ∃ F, IsStripExtension h a δ F) :
    ∃ (n : ℕ) (h₀ : normalizedLipschitzMaps x₀) (S : Finset X), x₀ ∈ S ∧
      ∀ h : normalizedLipschitzMaps x₀, (∀ x ∈ S, h.val x = h₀.val x) →
        HasWeightedOperatorBound a h.val ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) := by
  classical
  obtain ⟨n, h₀, hh₀⟩ := weightedBound_has_interior x₀ a ha
  have hn := mem_interior_iff_mem_nhds.mp hh₀
  rw [mem_nhds_subtype] at hn
  obtain ⟨U, hU, hsub⟩ := hn
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨S, V, hV, hVU⟩ := hU
  refine ⟨n, h₀, insert x₀ S, Finset.mem_insert_self _ _, fun h he => hsub (hVU ?_)⟩
  intro x hx
  rw [he x (Finset.mem_insert_of_mem hx)]
  exact mem_of_mem_nhds (hV x)

end DynamicalCStarAlgebras
