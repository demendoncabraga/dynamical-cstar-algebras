import DynamicalCStarAlgebras.ComponentObstruction
noncomputable section
open Classical
namespace DynamicalCStarAlgebras

lemma exists_selfAdjoint_polynomial_approx {X : Type*} [PseudoMetricSpace X]
    {p : Operator X} (hp : IsSelfAdjoint p) {β δ : ℝ} (hβ : 0 < β)
    (hδ : 0 < δ) (hmem : p ∈ polynomialQuasiLocal β) :
    ∃ a : Operator X, IsSelfAdjoint a ∧ HasPolynomialDecay β a ∧ ‖a - p‖ ≤ δ := by
  obtain ⟨a, ha, hap⟩ := Metric.mem_closure_iff.mp hmem δ hδ
  refine ⟨(realPart a : Operator X), (realPart a).property, ?_, ?_⟩
  · rw [realPart_apply_coe, ← Complex.coe_smul]
    exact (polynomialDecayStarSubalgebra β hβ).smul_mem (ha.add ha.star) _
  · have he := realPart.norm_le (a - p)
    have hp' := selfAdjoint.realPart_coe (x := (⟨p, hp⟩ : selfAdjoint (Operator X)))
    rw [map_sub, hp'] at he
    exact he.trans (by simpa only [dist_eq_norm, norm_sub_rev] using hap.le)

lemma componentOperator_sub {X Y : Type*} (ι : Y → X) (hι : Function.Injective ι)
    (a b : Operator X) : componentOperator ι hι (a - b) =
      componentOperator ι hι a - componentOperator ι hι b := by
  ext v
  simp [componentOperator]

lemma componentOperator_selfAdjoint {X Y : Type*} (ι : Y → X) (hι : Function.Injective ι)
    {a : Operator X} (ha : IsSelfAdjoint a) : IsSelfAdjoint (componentOperator ι hι a) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro x y
  change inner ℂ (componentOperator ι hι a x) y = inner ℂ x (componentOperator ι hι a y)
  simp only [componentOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  exact ha.isSymmetric _ _

lemma uniform_degree_of_isometric_graphs {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) {Y : ℕ → Type*}
    [∀ n, Fintype (Y n)] [∀ n, PseudoMetricSpace (Y n)]
    (ι : ∀ n, Y n → X) (hinj : ∀ n, Function.Injective (ι n)) (hi : ∀ n, Isometry (ι n))
    (G : ∀ n, SimpleGraph (Y n))
    (hdist : ∀ n (x y : Y n), dist x y = ((G n).dist x y : ℝ)) :
    ∃ k : ℕ, 2 ≤ k ∧ ∀ n x, ((G n).neighborFinset x).card ≤ k := by
  classical
  obtain ⟨K, hK⟩ := hX 1 zero_lt_one
  refine ⟨max K 2, le_max_right _ _, fun n x => ?_⟩
  have hc : (((G n).neighborFinset x : Set (Y n))).ncard ≤
      (Metric.closedBall (ι n x) 1).ncard := by
    apply Set.ncard_le_ncard_of_injOn (ι n) ?_ (hinj n).injOn (hK (ι n x)).1
    intro y hy
    have hadj : (G n).Adj x y := by simpa using hy
    rw [Metric.mem_closedBall, dist_comm, (hi n).dist_eq, hdist,
      SimpleGraph.dist_eq_one_iff_adj.mpr hadj]
    norm_num
  simp only [Set.ncard_coe_finset] at hc
  exact hc.trans ((hK (ι n x)).2.trans (le_max_left _ _))

end DynamicalCStarAlgebras
