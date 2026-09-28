import DynamicalCStarAlgebras.ExponentialMoments

noncomputable section

namespace DynamicalCStarAlgebras

/-- A common bound on edge increments controls increments along every graph walk. -/
theorem graph_walk_height_bound {X : Type*} (G : SimpleGraph X) (h : X → ℝ) {L : ℝ}
    (hL : ∀ x y, G.Adj x y → dist (h x) (h y) ≤ L) {x y : X} (p : G.Walk x y) :
    dist (h x) (h y) ≤ L * p.length := by
  induction p with
  | nil => simp
  | @cons x y z hxy p ih =>
    calc
      _ ≤ dist (h x) (h y) + dist (h y) (h z) := dist_triangle _ _ _
      _ ≤ L + L * p.length := add_le_add (hL x y hxy) ih
      _ = _ := by simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]; ring

/-- Shortest walks convert a common edge bound into a Lipschitz bound. -/
theorem graph_height_lipschitz {X : Type*} (G : SimpleGraph X) (hG : G.Connected)
    (h : X → ℝ) (L : NNReal)
    (hL : ∀ x y, G.Adj x y → dist (h x) (h y) ≤ (L : ℝ)) :
    letI := connectedGraphMetric G hG
    LipschitzWith L h := by
  let inst : MetricSpace X := connectedGraphMetric G hG
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist x y
  simpa only [hp] using! graph_walk_height_bound G h hL p

/-- One coarse height has a common positive Lipschitz bound on all unit-edge graph components. -/
theorem coarse_graph_height_uniform_lipschitz {X : Type*} [PseudoMetricSpace X]
    (h : X → ℝ) (hh : IsCoarseReal (CoarseStructure.ofPseudoMetric X) h) :
    ∃ L : NNReal, 1 ≤ L ∧ ∀ {Y : Type*} (G : SimpleGraph Y) (hG : G.Connected) (ι : Y → X),
      (∀ x y, G.Adj x y → dist (ι x) (ι y) ≤ 1) →
      letI := connectedGraphMetric G hG
      LipschitzWith L (h ∘ ι) := by
  obtain ⟨R, hR⟩ := hh {p | dist p.1 p.2 ≤ 1} ⟨1, fun _ hp => hp⟩
  let L : NNReal := ⟨max 1 R, zero_le_one.trans (le_max_left _ _)⟩
  refine ⟨L, (show (1 : NNReal) ≤ L from le_max_left (1 : ℝ) R), fun G hG ι hι => ?_⟩
  exact graph_height_lipschitz G hG (h ∘ ι) L fun x y hxy =>
    (hR (ι x, ι y) (hι x y hxy)).trans (le_max_right 1 R)

/-- Common factorial bounds and strip widths for every finite graph block of one coarse height. -/
theorem coarse_graph_uniform_moments {X : Type*} [PseudoMetricSpace X]
    (h : X → ℝ) (hh : IsCoarseReal (CoarseStructure.ofPseudoMetric X) h)
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, 0 < B ∧ ∀ {Y : Type*} [Fintype Y] (G : SimpleGraph Y) (hG : G.Connected)
      (ι : Y → X), (∀ x y, G.Adj x y → dist (ι x) (ι y) ≤ 1) →
      ∀ a : Operator Y,
      letI := connectedGraphMetric G hG
      ‖a‖ ≤ 1 →
      (∀ r : ℝ, 0 < r → quasiLocalModulus a r ≤ C * Real.exp (-c * r)) →
      ∃ b : ℕ → Operator Y, IsDiagonalMomentSequence (h ∘ ι) a b ∧
        (∀ k : ℕ, ‖b k‖ ≤ A * B ^ k * k.factorial) ∧
        ∀ δ : ℝ, 0 < δ → δ < B⁻¹ → ∃ F, IsStripExtension (h ∘ ι) a δ F := by
  obtain ⟨L, hL, hLip⟩ := coarse_graph_height_uniform_lipschitz h hh
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let B : ℝ := 3 * (L : ℝ) / min 1 c
  have hB : 0 < B := div_pos (mul_pos (by norm_num) hLpos) (lt_min zero_lt_one hc)
  refine ⟨2 * (1 + C * Real.exp c / c), by positivity, B, hB, ?_⟩
  intro Y _ G hG ι hι a
  let inst : MetricSpace Y := connectedGraphMetric G hG
  intro ha hdecay
  let b : ℕ → Operator Y := fun k => (diagonalCommutator (finiteRealDiagonal (h ∘ ι)))^[k] a
  have hm : IsDiagonalMomentSequence (h ∘ ι) a b := by
    intro k x y
    simpa only [b, finiteRealDiagonal_apply, Complex.ofReal_sub] using
      matrixEntry_iterate_diagonalCommutator (finiteRealDiagonal (h ∘ ι)) a k x y
  have hb (k : ℕ) : ‖b k‖ ≤ (2 * (1 + C * Real.exp c / c)) * B ^ k * k.factorial :=
    finite_integer_factorial_commutator_bound (fun x y => ⟨G.dist x y, rfl⟩)
      (h ∘ ι) hLpos (hLip G hG ι hι) a ha hc hC hdecay k
  exact ⟨b, hm, hb, (stripExtension_of_factorial_moments hm hB hb).2⟩

end DynamicalCStarAlgebras
