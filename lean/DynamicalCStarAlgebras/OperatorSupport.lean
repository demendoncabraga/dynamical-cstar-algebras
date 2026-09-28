import DynamicalCStarAlgebras.Coarse

/-! Complex Hilbert space, matrix support and the defining closure of the uniform Roe algebra.
No countability, local finiteness or nonemptiness assumption is made here.
-/

noncomputable section

namespace DynamicalCStarAlgebras

universe u

/-- Square-summable complex families on an arbitrary set. -/
abbrev HilbertSpace (X : Type u) := lp (fun _ : X => ℂ) 2

/-- Bounded complex-linear operators, equipped with the operator norm. -/
abbrev Operator (X : Type u) := HilbertSpace X →L[ℂ] HilbertSpace X

/-- The canonical unit vector. -/
def delta {X : Type u} (x : X) : HilbertSpace X :=
  @lp.single X (fun _ => ℂ) _ (Classical.decEq X) 2 x 1

/-- Matrix coefficients use output coordinates, matching the paper's linear-first convention. -/
def matrixEntry {X : Type u} (a : Operator X) (x y : X) : ℂ := a (delta y) x

/-- Mathlib's inner product is linear in the second variable, unlike the paper's notation. -/
theorem matrixEntry_eq_inner {X : Type u} (a : Operator X) (x y : X) :
    matrixEntry a x y = inner ℂ (delta x) (a (delta y)) := by
  simp [matrixEntry, delta, lp.inner_single_left]

/-- Section 2.2: the set of nonzero matrix coefficients. -/
def operatorSupport {X : Type u} (a : Operator X) : Set (X × X) :=
  {p | matrixEntry a p.1 p.2 ≠ 0}

/-- Controlled propagation for an arbitrary coarse structure. -/
def HasControlledPropagation {X : Type u} (C : CoarseStructure X) (a : Operator X) :
    Prop := operatorSupport a ∈ C.controlled

/-- The positive-radius finite-propagation definition from the introduction. -/
def HasFinitePropagation {X : Type u} [PseudoMetricSpace X] (a : Operator X) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ x y, R < dist x y → matrixEntry a x y = 0

/-- The metric and coarse-space propagation definitions agree, including for pseudometrics. -/
theorem controlled_iff_finitePropagation {X : Type u} [PseudoMetricSpace X]
    (a : Operator X) :
    HasControlledPropagation (CoarseStructure.ofPseudoMetric X) a ↔
      HasFinitePropagation a :=
  ⟨fun h => h.elim fun R hR =>
    ⟨max R 0 + 1, lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left (le_max_right R 0)),
      fun x y hxy => Classical.byContradiction fun hne =>
        (not_le_of_gt hxy) ((hR (x, y) hne).trans
          ((le_max_left R 0).trans (le_add_of_nonneg_right zero_le_one)))⟩,
    fun h => h.elim fun R hR =>
      ⟨R, fun p hp => le_of_not_gt fun hxy => hp (hR.2 p.1 p.2 hxy)⟩⟩

/-- The defining norm closure of the uniform Roe algebra in Section 2.2.
Its C*-subalgebra properties are separate proof obligations. -/
def uniformRoe {X : Type u} (C : CoarseStructure X) : Set (Operator X) :=
  closure {a | HasControlledPropagation C a}

/-- The metric definition in the introduction agrees with the coarse-space definition. -/
theorem uniformRoe_metric_eq {X : Type u} [PseudoMetricSpace X] :
    uniformRoe (CoarseStructure.ofPseudoMetric X) =
      closure {a : Operator X | HasFinitePropagation a} := by
  simp only [uniformRoe, controlled_iff_finitePropagation]

/-- The coarse-structure inclusion used in the proof of the continuity-substructure theorem. -/
theorem uniformRoe_mono {X : Type u} {C D : CoarseStructure X}
    (hCD : C.IsSubstructure D) : uniformRoe C ⊆ uniformRoe D :=
  closure_mono (fun _ ha => hCD ha)

/-- Section 4: restricting to entourages controlled by h decreases the uniform Roe algebra. -/
theorem uniformRoe_restrictReal_subset {X : Type u} (C : CoarseStructure X) (h : X → ℝ) :
    uniformRoe (C.restrictReal h) ⊆ uniformRoe C :=
  uniformRoe_mono (C.restrictReal_largest h).1

end DynamicalCStarAlgebras
