import DynamicalCStarAlgebras.ContinuityPoints

namespace DynamicalCStarAlgebras

universe u

theorem diagonalUnitary_dist_le {X : Type u} (h : X → ℝ) (t : ℝ)
    (v w : HilbertSpace X) : dist (diagonalUnitary h t v) (diagonalUnitary h t w) ≤
      dist v w := by
  simpa only [dist_eq_norm, ← map_sub, one_mul] using
    (diagonalUnitary h t).le_of_opNorm_le (diagonalUnitary_norm_le h t) (v - w)

theorem continuous_diagonalPhase {X : Type u} (h : X → ℝ) (x : X) :
    Continuous (fun t : ℝ => diagonalPhase h t x) :=
  Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).mul continuous_const)

theorem continuous_diagonalUnitary_delta {X : Type u} (h : X → ℝ) (x : X) :
    Continuous (fun t : ℝ => diagonalUnitary h t (delta x)) := by
  simpa only [diagonalUnitary_delta, Pi.smul_def'] using (continuous_diagonalPhase h x).smul
    (continuous_const : Continuous (fun _ : ℝ => delta x))

theorem single_eq_smul_delta {X : Type u} [DecidableEq X] (x : X) (c : ℂ) :
    lp.single 2 x c = c • delta x := by
  apply lp.ext
  funext y
  simp [delta, lp.coeFn_smul, Pi.single_apply, mul_ite]

theorem continuous_diagonalUnitary_single {X : Type u} [DecidableEq X]
    (h : X → ℝ) (x : X) (c : ℂ) :
    Continuous (fun t : ℝ => diagonalUnitary h t (lp.single 2 x c)) := by
  simpa only [single_eq_smul_delta, map_smul, Pi.smul_def] using
    (continuous_diagonalUnitary_delta h x).const_smul c

theorem continuous_diagonalUnitary_finsetSum {X : Type u} [DecidableEq X]
    (h : X → ℝ) (v : HilbertSpace X) (s : Finset X) :
    Continuous (fun t : ℝ => diagonalUnitary h t (∑ x ∈ s, lp.single 2 x (v x))) := by
  simpa only [map_sum] using
    continuous_finsetSum s (fun x _ => continuous_diagonalUnitary_single h x (v x))

/-- Section 3: the diagonal unitary group is strongly continuous, for arbitrary X and h. -/
theorem continuous_diagonalUnitary_apply {X : Type u} (h : X → ℝ) (v : HilbertSpace X) :
    Continuous (fun t : ℝ => diagonalUnitary h t v) := by
  classical
  exact (isClosed_continuousOrbitSet (fun t w => diagonalUnitary h t w)
    (diagonalUnitary_dist_le h)).mem_of_tendsto
    (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) v)
    (Filter.Eventually.of_forall (continuous_diagonalUnitary_finsetSum h v))

theorem continuous_diagonalUnitary_uncurry {X : Type u} (h : X → ℝ) :
    Continuous (fun p : ℝ × HilbertSpace X => diagonalUnitary h p.1 p.2) := by
  exact continuous_prod_of_continuous_lipschitzWith' _ 1
    (fun t => LipschitzWith.of_dist_le_mul (by simpa using diagonalUnitary_dist_le h t))
    (continuous_diagonalUnitary_apply h)

/-- The conjugation orbit is continuous in the strong operator topology. -/
theorem continuous_diagonalFlow_apply {X : Type u} (h : X → ℝ) (a : Operator X)
    (v : HilbertSpace X) : Continuous (fun t : ℝ => diagonalFlow h t a v) := by
  exact (continuous_diagonalUnitary_uncurry h).comp
    (continuous_id.prodMk
      (a.continuous.comp ((continuous_diagonalUnitary_apply h v).comp continuous_neg)))

/-- Section 3: every scalar matrix coefficient of the conjugation orbit is continuous. -/
theorem continuous_inner_diagonalFlow {X : Type u} (h : X → ℝ) (a : Operator X)
    (v w : HilbertSpace X) : Continuous (fun t : ℝ => inner ℂ (diagonalFlow h t a v) w) :=
  (continuous_diagonalFlow_apply h a v).inner continuous_const

end DynamicalCStarAlgebras
