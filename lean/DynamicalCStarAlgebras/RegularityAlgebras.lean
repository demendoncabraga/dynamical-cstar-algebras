import DynamicalCStarAlgebras.CoarseDynamicalInvariance
import DynamicalCStarAlgebras.TheoremB

noncomputable section
open Classical
open scoped NNReal
namespace DynamicalCStarAlgebras

/-- A diagonal flow at a fixed time, as a complex linear isometry. -/
def diagonalFlowLinearIsometry {X : Type*} (h : X → ℝ) (t : ℝ) :
    Operator X ≃ₗᵢ[ℂ] Operator X :=
  { (diagonalFlowEquiv h t).toAlgEquiv.toLinearEquiv with
    norm_map' := fun a => by
      change ‖diagonalFlowEquiv h t a‖ = ‖a‖
      rw [diagonalFlowEquiv_apply, diagonalFlow_norm] }

@[simp] theorem diagonalFlowLinearIsometry_apply {X : Type*} (h : X → ℝ) (t : ℝ)
    (a : Operator X) : diagonalFlowLinearIsometry h t a = diagonalFlow h t a :=
  diagonalFlowEquiv_apply h t a

/-- Differentiable diagonal orbits have a uniformly bounded derivative, hence are globally Lipschitz. -/
theorem differentiable_diagonalOrbit_lipschitz {X : Type*} (h : X → ℝ) (a : Operator X)
    (ha : Differentiable ℝ (fun t : ℝ => diagonalFlow h t a)) :
    LipschitzWith ‖deriv (fun t : ℝ => diagonalFlow h t a) 0‖₊
      (fun t : ℝ => diagonalFlow h t a) := by
  apply lipschitzWith_of_nnnorm_deriv_le ha
  intro t
  have hd : HasDerivAt (fun s : ℝ => diagonalFlow h (s - t) a)
      (deriv (fun s : ℝ => diagonalFlow h s a) 0) t := by
    simpa using! ((ha 0).hasDerivAt.scomp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp))
  have hc := ((diagonalFlowLinearIsometry h t).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd
  have he : (fun s : ℝ => diagonalFlow h t (diagonalFlow h (s - t) a)) =
      (fun s : ℝ => diagonalFlow h s a) := by
    funext s
    rw [← diagonalFlow_add]
    congr 1
    ring
  have hL : ⇑((diagonalFlowLinearIsometry h t).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) =
      diagonalFlow h t := funext (diagonalFlowLinearIsometry_apply h t)
  rw [hL] at hc
  simp only [Function.comp_def] at hc
  rw [he] at hc
  rw [hc.deriv]
  exact NNReal.coe_le_coe.mp (diagonalFlow_norm h t _).le

/-- Restricting an entire complex orbit to the real line gives every order of smoothness. -/
theorem IsEntireExtension.contDiff_orbit {X : Type*} {h : X → ℝ} {a : Operator X}
    {F : ℂ → Operator X} (hF : IsEntireExtension h a F) (k : ℕ∞) :
    ContDiff ℝ k (fun t : ℝ => diagonalFlow h t a) := by
  have hc : ContDiff ℝ k (fun t : ℝ => F (Complex.ofRealCLM t)) :=
    (hF.differentiable.contDiff.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, hF.on_real] using hc

/-- The three named orbit regularities in the introductory discussion; smoothness
includes every finite order and infinity. -/
inductive OrbitRegularity where
  | lipschitz
  | differentiable
  | contDiff (k : ℕ∞)

/-- Regularity is measured in operator norm, with real time as the domain. -/
def HasOrbitRegularity {X : Type*} (r : OrbitRegularity) (h : X → ℝ) (a : Operator X) : Prop :=
  match r with
  | .lipschitz => ∃ K : ℝ≥0, LipschitzWith K (fun t : ℝ => diagonalFlow h t a)
  | .differentiable => Differentiable ℝ (fun t : ℝ => diagonalFlow h t a)
  | .contDiff k => ContDiff ℝ k (fun t : ℝ => diagonalFlow h t a)

theorem lipschitz_diagonalOrbit_mul {X : Type*} {h : X → ℝ} {a b : Operator X}
    {K L : ℝ≥0} (ha : LipschitzWith K (fun t : ℝ => diagonalFlow h t a))
    (hb : LipschitzWith L (fun t : ℝ => diagonalFlow h t b)) :
    LipschitzWith (K * ‖b‖₊ + ‖a‖₊ * L) (fun t : ℝ => diagonalFlow h t (a * b)) := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  simp only [← diagonalFlowEquiv_apply, map_mul]
  have hnorm (v : Operator X) (u : ℝ) : ‖diagonalFlowEquiv h u v‖ = ‖v‖ := by
    rw [diagonalFlowEquiv_apply, diagonalFlow_norm]
  have he : diagonalFlowEquiv h t a * diagonalFlowEquiv h t b -
      diagonalFlowEquiv h s a * diagonalFlowEquiv h s b =
      (diagonalFlowEquiv h t a - diagonalFlowEquiv h s a) * diagonalFlowEquiv h t b +
      diagonalFlowEquiv h s a * (diagonalFlowEquiv h t b - diagonalFlowEquiv h s b) := by
    noncomm_ring
  rw [dist_eq_norm, he]
  calc
    _ ≤ ‖diagonalFlowEquiv h t a - diagonalFlowEquiv h s a‖ * ‖b‖ +
        ‖a‖ * ‖diagonalFlowEquiv h t b - diagonalFlowEquiv h s b‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add
      · simpa only [hnorm] using norm_mul_le
          (diagonalFlowEquiv h t a - diagonalFlowEquiv h s a) (diagonalFlowEquiv h t b)
      · simpa only [hnorm] using norm_mul_le
          (diagonalFlowEquiv h s a) (diagonalFlowEquiv h t b - diagonalFlowEquiv h s b)
    _ ≤ ((K : ℝ) * dist t s) * ‖b‖ + ‖a‖ * ((L : ℝ) * dist t s) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (by simpa only [diagonalFlowEquiv_apply, ← dist_eq_norm] using ha.dist_le_mul t s) (norm_nonneg _)
      · exact mul_le_mul_of_nonneg_left (by simpa only [diagonalFlowEquiv_apply, ← dist_eq_norm] using hb.dist_le_mul t s) (norm_nonneg _)
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul, coe_nnnorm]; ring

/-- Each named regularity is preserved by addition. -/
theorem HasOrbitRegularity.add {X : Type*} {r : OrbitRegularity} {h : X → ℝ}
    {a b : Operator X} (ha : HasOrbitRegularity r h a) (hb : HasOrbitRegularity r h b) :
    HasOrbitRegularity r h (a + b) := by
  cases r with
  | lipschitz =>
    obtain ⟨K, hK⟩ := ha
    obtain ⟨L, hL⟩ := hb
    exact ⟨K + L, by simpa only [← diagonalFlowEquiv_apply, map_add] using! hK.add hL⟩
  | differentiable =>
    simpa only [HasOrbitRegularity, ← diagonalFlowEquiv_apply, map_add] using! Differentiable.add ha hb
  | contDiff k =>
    dsimp [HasOrbitRegularity] at ha hb ⊢
    simpa only [HasOrbitRegularity, ← diagonalFlowEquiv_apply, map_add] using! ContDiff.add ha hb

/-- Multiplication preserves the named regularities, since diagonal orbits have constant norm. -/
theorem HasOrbitRegularity.mul {X : Type*} {r : OrbitRegularity} {h : X → ℝ}
    {a b : Operator X} (ha : HasOrbitRegularity r h a) (hb : HasOrbitRegularity r h b) :
    HasOrbitRegularity r h (a * b) := by
  cases r with
  | lipschitz =>
    obtain ⟨K, hK⟩ := ha
    obtain ⟨L, hL⟩ := hb
    exact ⟨_, lipschitz_diagonalOrbit_mul hK hL⟩
  | differentiable =>
    simpa only [HasOrbitRegularity, ← diagonalFlowEquiv_apply, map_mul] using! Differentiable.mul ha hb
  | contDiff k =>
    dsimp [HasOrbitRegularity] at ha hb ⊢
    simpa only [HasOrbitRegularity, ← diagonalFlowEquiv_apply, map_mul] using! ContDiff.mul ha hb

/-- Every entire diagonal extension has all the named real-time regularities. -/
theorem IsEntireExtension.hasOrbitRegularity {X : Type*} {h : X → ℝ} {a : Operator X}
    {F : ℂ → Operator X} (hF : IsEntireExtension h a F) (r : OrbitRegularity) :
    HasOrbitRegularity r h a := by
  have hd : Differentiable ℝ (fun t : ℝ => diagonalFlow h t a) :=
    (hF.contDiff_orbit 1).differentiable (by norm_num)
  cases r with
  | lipschitz => exact ⟨_, differentiable_diagonalOrbit_lipschitz h a hd⟩
  | differentiable => exact hd
  | contDiff k => exact hF.contDiff_orbit k

/-- Adjoint is compatible with restriction of scalars from complex to real operators. -/
local instance operatorRealStarModule {X : Type*} : StarModule ℝ (Operator X) := by
  constructor
  intro r a
  change star (r • a) = r • star a
  rw [← IsScalarTower.algebraMap_smul ℂ r a, star_smul]
  simp
  rfl


/-- Taking adjoints preserves the named real-time regularities. -/
theorem HasOrbitRegularity.star {X : Type*} {r : OrbitRegularity} {h : X → ℝ}
    {a : Operator X} (ha : HasOrbitRegularity r h a) : HasOrbitRegularity r h (star a) := by
  cases r with
  | lipschitz =>
    obtain ⟨K, hK⟩ := ha
    exact ⟨K, by simpa only [← diagonalFlowEquiv_apply, map_star, Function.comp_def, one_mul]
      using! (star_isometry.lipschitz.comp hK)⟩
  | differentiable =>
    simpa only [HasOrbitRegularity, ← diagonalFlowEquiv_apply, map_star] using! Differentiable.star ha
  | contDiff k =>
    dsimp [HasOrbitRegularity] at ha ⊢
    simpa only [← diagonalFlowEquiv_apply, map_star, Function.comp_def, starL'_apply] using!
      (starL' ℝ : Operator X ≃L[ℝ] Operator X).contDiff.comp ha

/-- Each named regularity implies continuity of the orbit. -/
theorem HasOrbitRegularity.continuous {X : Type*} {r : OrbitRegularity} {h : X → ℝ}
    {a : Operator X} (ha : HasOrbitRegularity r h a) :
    Continuous (fun t : ℝ => diagonalFlow h t a) := by
  cases r with
  | lipschitz => exact ha.elim fun _ hK => hK.continuous
  | differentiable => exact Differentiable.continuous ha
  | contDiff k => exact (show ContDiff ℝ k _ from ha).continuous

/-- Common regular points form a unital complex star-subalgebra before taking closure. -/
def coarseRegularityStarSubalgebra {X : Type*} (C : CoarseStructure X) (r : OrbitRegularity) :
    StarSubalgebra ℂ (Operator X) where
  carrier := {a | ∀ h : X → ℝ, IsCoarseReal C h → HasOrbitRegularity r h a}
  zero_mem' h _ := by
    obtain ⟨F, hF, _⟩ := isEntireExponentialType_algebraMap h 0
    simpa only [map_zero] using! hF.hasOrbitRegularity r
  one_mem' h _ := by
    obtain ⟨F, hF, _⟩ := isEntireExponentialType_algebraMap h 1
    simpa only [map_one] using! hF.hasOrbitRegularity r
  add_mem' ha hb h hh := (ha h hh).add (hb h hh)
  mul_mem' ha hb h hh := (ha h hh).mul (hb h hh)
  star_mem' ha h hh := (ha h hh).star
  algebraMap_mem' c h _ := by
    obtain ⟨F, hF, _⟩ := isEntireExponentialType_algebraMap h c
    exact hF.hasOrbitRegularity r

/-- The norm closure is taken after requiring regularity for every coarse real map. -/
def regularityPoints {X : Type*} (C : CoarseStructure X) (r : OrbitRegularity) : Set (Operator X) :=
  closure {a | ∀ h : X → ℝ, IsCoarseReal C h → HasOrbitRegularity r h a}

/-- The closed complex star-subalgebra associated with a named orbit regularity. -/
def regularityPointsStarSubalgebra {X : Type*} (C : CoarseStructure X) (r : OrbitRegularity) :
    StarSubalgebra ℂ (Operator X) := (coarseRegularityStarSubalgebra C r).topologicalClosure

/-- The Lipschitz, differentiable, and C^k constructions give norm-closed unital complex star-algebras. -/
theorem regularityPoints_algebra {X : Type*} (C : CoarseStructure X) (r : OrbitRegularity) :
    (regularityPointsStarSubalgebra C r : Set (Operator X)) = regularityPoints C r ∧
      IsClosed (regularityPoints C r) :=
  ⟨rfl, isClosed_closure⟩

/-- All the named regularity algebras lie between Roe and common continuity, on arbitrary coarse spaces. -/
theorem regularityPoints_inclusions {X : Type*} (C : CoarseStructure X) (r : OrbitRegularity) :
    uniformRoe C ⊆ regularityPoints C r ∧ regularityPoints C r ⊆ coarseContinuityPoints C := by
  constructor
  · apply closure_mono
    intro a ha h hh
    obtain ⟨F, hF, _⟩ := ha.isEntireExponentialType hh
    exact hF.hasOrbitRegularity r
  · apply closure_minimal
    · intro a ha h hh
      exact (ha h hh).continuous
    · rw [← coe_coarseContinuityPointsStarSubalgebra]
      exact coarseContinuityPointsStarSubalgebra_isClosed C

/-- In the uniformly locally finite metric setting of the introduction, the upper endpoint is quasi-locality. -/
theorem regularityPoints_between_Roe_quasiLocal {X : Type*} [PseudoMetricSpace X]
    (hX : UniformlyLocallyFinite X) (r : OrbitRegularity) :
    uniformRoe (CoarseStructure.ofPseudoMetric X) ⊆ regularityPoints (CoarseStructure.ofPseudoMetric X) r ∧
      regularityPoints (CoarseStructure.ofPseudoMetric X) r ⊆ quasiLocal (CoarseStructure.ofPseudoMetric X) := by
  rw [quasiLocal_eq_coarseContinuityPoints hX]
  exact regularityPoints_inclusions _ r

/-- Spatial relabeling preserves each named regularity of an individual orbit. -/
theorem HasOrbitRegularity.relabel {X Y : Type*} (e : X ≃ Y)
    {r : OrbitRegularity} {h : Y → ℝ} {a : Operator X}
    (ha : HasOrbitRegularity r (h ∘ e) a) :
    HasOrbitRegularity r h (operatorRelabel e a) := by
  cases r with
  | lipschitz =>
    obtain ⟨K, hK⟩ := ha
    refine ⟨K, ?_⟩
    have hc := (operatorRelabelIsometry e).isometry.lipschitz.comp hK
    change LipschitzWith (1 * K)
      (fun t => operatorRelabel e (diagonalFlow (h ∘ e) t a)) at hc
    simpa only [one_mul, operatorRelabel_diagonalFlow] using hc
  | differentiable =>
    have hc : Differentiable ℝ (fun t : ℝ => operatorRelabel e (diagonalFlow (h ∘ e) t a)) :=
      ((operatorRelabelIsometry e).toContinuousLinearEquiv.differentiable.restrictScalars ℝ).comp ha
    simpa only [HasOrbitRegularity, operatorRelabel_diagonalFlow] using hc
  | contDiff k =>
    have hc : ContDiff ℝ k (fun t : ℝ => operatorRelabel e (diagonalFlow (h ∘ e) t a)) :=
      ((operatorRelabelIsometry e).toContinuousLinearEquiv.contDiff.restrict_scalars ℝ).comp ha
    simpa only [HasOrbitRegularity, operatorRelabel_diagonalFlow] using hc

/-- Common regularity and its norm closure are preserved by a coarse bijection. -/
theorem operatorRelabel_mem_regularityPoints {X Y : Type*}
    {C : CoarseStructure X} {D : CoarseStructure Y} (e : X ≃ Y)
    (he : IsCoarseMap C D e) (r : OrbitRegularity) {a : Operator X}
    (ha : a ∈ regularityPoints C r) : operatorRelabel e a ∈ regularityPoints D r := by
  refine closure_mono ?_ (mem_closure_image
    (operatorRelabelIsometry e).continuous.continuousAt ha)
  rintro _ ⟨b, hb, rfl⟩ h hh
  exact (hb (h ∘ e) (hh.comp_coarse he)).relabel e

/-- The same spatial isomorphism implements bijective coarse invariance for all three named classes. -/
theorem AreBijectivelyCoarselyEquivalent.regularity_algebras {X Y : Type*}
    {C : CoarseStructure X} {D : CoarseStructure Y}
    (h : AreBijectivelyCoarselyEquivalent C D) :
    ∃ Φ : Operator X ≃⋆ₐ[ℂ] Operator Y, Isometry Φ ∧
      ∀ r : OrbitRegularity, Φ '' regularityPoints C r = regularityPoints D r := by
  obtain ⟨e, he, hei⟩ := h.exists_equiv
  refine ⟨operatorRelabel e, (operatorRelabelIsometry e).isometry, fun r => ?_⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact operatorRelabel_mem_regularityPoints e he r ha
  · intro b hb
    refine ⟨operatorRelabel e.symm b, operatorRelabel_mem_regularityPoints e.symm hei r hb, ?_⟩
    simpa using operatorRelabel_inverse e.symm b

end DynamicalCStarAlgebras
