import DynamicalCStarAlgebras.CoordinateLiftAlgebra
import DynamicalCStarAlgebras.StripCharacterization
import DynamicalCStarAlgebras.ExponentialGrowth
import DynamicalCStarAlgebras.CoarseEquivalence

noncomputable section
open Classical
namespace DynamicalCStarAlgebras

/-- Relabeling arbitrary square-summable coordinate spaces by a bijection. -/
def coordinateRelabel {X Y : Type*} (e : X ≃ Y) :
    HilbertSpace X ≃ₗᵢ[ℂ] HilbertSpace Y :=
  LinearIsometryEquiv.ofSurjective (coordinateEmbedding e e.injective) (by
    intro v
    refine ⟨(coordinateEmbedding e e.injective).toContinuousLinearMap.adjoint v, ?_⟩
    have h := congrArg (fun a : Operator Y => a v)
      (coordinateEmbedding_mul_adjoint e e.injective)
    have hp : coordinateProjection (Set.univ : Set Y) v = v := by
      apply lp.ext
      funext y
      exact coordinateProjection_apply_of_mem _ _ (Set.mem_univ y)
    simpa [e.range_eq_univ, hp] using h)

@[simp] theorem coordinateRelabel_apply {X Y : Type*} (e : X ≃ Y)
    (v : HilbertSpace X) (y : Y) : coordinateRelabel e v y = v (e.symm y) := by
  have h := congrArg (fun w : HilbertSpace X => w (e.symm y))
    (coordinateEmbedding_adjoint_apply e e.injective v)
  change coordinateEmbedding e e.injective v y = _
  simpa only [coordinateEmbedding_adjoint_apply_coord, Equiv.apply_symm_apply] using h

/-- The spatial complex star-algebra isomorphism induced by coordinate relabeling. -/
def operatorRelabel {X Y : Type*} (e : X ≃ Y) : Operator X ≃⋆ₐ[ℂ] Operator Y :=
  (coordinateRelabel e).conjStarAlgEquiv

@[simp] theorem operatorRelabel_matrixEntry {X Y : Type*} (e : X ≃ Y)
    (a : Operator X) (x y : Y) :
    matrixEntry (operatorRelabel e a) x y = matrixEntry a (e.symm x) (e.symm y) := by
  have hf (z : X) : coordinateRelabel e (delta z) = delta (e z) :=
    coordinateEmbedding_delta e e.injective z
  have hd : (coordinateRelabel e).symm (delta y) = delta (e.symm y) := by
    apply (coordinateRelabel e).injective
    simp only [LinearIsometryEquiv.apply_symm_apply, hf, Equiv.apply_symm_apply]
  change (coordinateRelabel e (a ((coordinateRelabel e).symm (delta y)))) x = _
  rw [coordinateRelabel_apply, hd]
  rfl

@[simp] theorem operatorRelabel_inverse {X Y : Type*} (e : X ≃ Y) (a : Operator X) :
    operatorRelabel e.symm (operatorRelabel e a) = a := by
  apply operator_ext
  intro x y
  simp

/-- Spatial conjugation preserves the operator norm. -/
def operatorRelabelIsometry {X Y : Type*} (e : X ≃ Y) :
    Operator X ≃ₗᵢ[ℂ] Operator Y :=
  { (operatorRelabel e).toAlgEquiv.toLinearEquiv with
    norm_map' := NonUnitalStarAlgHom.norm_map (operatorRelabel e) (operatorRelabel e).injective }

@[simp] theorem operatorRelabel_norm {X Y : Type*} (e : X ≃ Y) (a : Operator X) :
    ‖operatorRelabel e a‖ = ‖a‖ := (operatorRelabelIsometry e).norm_map a

/-- Relabeling intertwines the diagonal dynamics with pullback of the real function. -/
theorem operatorRelabel_diagonalFlow {X Y : Type*} (e : X ≃ Y)
    (h : Y → ℝ) (t : ℝ) (a : Operator X) :
    operatorRelabel e (diagonalFlow (h ∘ e) t a) =
      diagonalFlow h t (operatorRelabel e a) := by
  apply operator_ext
  intro x y
  simp [matrixEntry_diagonalFlow]

/-- Pullback along a coarse map preserves coarse real functions. -/
theorem IsCoarseReal.comp_coarse {X Y : Type*} {C : CoarseStructure X}
    {D : CoarseStructure Y} {h : Y → ℝ} (hh : IsCoarseReal D h)
    {f : X → Y} (hf : IsCoarseMap C D f) : IsCoarseReal C (h ∘ f) := by
  intro E hE
  obtain ⟨R, hR⟩ := hh _ (hf E hE)
  exact ⟨R, fun p hp => hR _ ⟨p, hp, rfl⟩⟩

/-- The same strip, with the same boundary regularity, survives spatial relabeling. -/
theorem IsStripExtension.relabel {X Y : Type*} (e : X ≃ Y)
    {h : Y → ℝ} {a : Operator X} {δ : ℝ} {F : ℂ → Operator X}
    (hF : IsStripExtension (h ∘ e) a δ F) :
    IsStripExtension h (operatorRelabel e a) δ (fun z => operatorRelabel e (F z)) where
  continuousOn := (operatorRelabelIsometry e).continuous.comp_continuousOn hF.continuousOn
  differentiableOn := (operatorRelabelIsometry e).toContinuousLinearEquiv.differentiable.comp_differentiableOn
    hF.differentiableOn
  on_real t := by rw [hF.on_real, operatorRelabel_diagonalFlow]

/-- Entire extensions survive the same spatial relabeling. -/
theorem IsEntireExtension.relabel {X Y : Type*} (e : X ≃ Y)
    {h : Y → ℝ} {a : Operator X} {F : ℂ → Operator X}
    (hF : IsEntireExtension (h ∘ e) a F) :
    IsEntireExtension h (operatorRelabel e a) (fun z => operatorRelabel e (F z)) where
  differentiable := (operatorRelabelIsometry e).toContinuousLinearEquiv.differentiable.comp
    hF.differentiable
  on_real t := by rw [hF.on_real, operatorRelabel_diagonalFlow]

/-- Common strip analyticity and its norm closure are functorial for a coarse bijection. -/
theorem operatorRelabel_mem_stripAnalyticPoints {X Y : Type*}
    {C : CoarseStructure X} {D : CoarseStructure Y} (e : X ≃ Y)
    (he : IsCoarseMap C D e) {a : Operator X} (ha : a ∈ stripAnalyticPoints C) :
    operatorRelabel e a ∈ stripAnalyticPoints D := by
  refine closure_mono ?_ (mem_closure_image
    (operatorRelabelIsometry e).continuous.continuousAt ha)
  rintro _ ⟨b, hb, rfl⟩ h hh
  obtain ⟨δ, hδ, F, hF⟩ := hb (h ∘ e) (hh.comp_coarse he)
  exact ⟨δ, hδ, _, hF.relabel e⟩

/-- Common entire analyticity and its norm closure are functorial for a coarse bijection. -/
theorem operatorRelabel_mem_entireAnalyticPoints {X Y : Type*}
    {C : CoarseStructure X} {D : CoarseStructure Y} (e : X ≃ Y)
    (he : IsCoarseMap C D e) {a : Operator X} (ha : a ∈ entireAnalyticPoints C) :
    operatorRelabel e a ∈ entireAnalyticPoints D := by
  refine closure_mono ?_ (mem_closure_image
    (operatorRelabelIsometry e).continuous.continuousAt ha)
  rintro _ ⟨b, hb, rfl⟩ h hh
  obtain ⟨F, hF⟩ := hb (h ∘ e) (hh.comp_coarse he)
  exact ⟨_, hF.relabel e⟩

/-- The exponential growth constants are unchanged by spatial relabeling. -/
theorem operatorRelabel_mem_exponentialAnalyticPoints {X Y : Type*}
    {C : CoarseStructure X} {D : CoarseStructure Y} (e : X ≃ Y)
    (he : IsCoarseMap C D e) {a : Operator X} (ha : a ∈ exponentialAnalyticPoints C) :
    operatorRelabel e a ∈ exponentialAnalyticPoints D := by
  refine closure_mono ?_ (mem_closure_image
    (operatorRelabelIsometry e).continuous.continuousAt ha)
  rintro _ ⟨b, hb, rfl⟩ h hh
  obtain ⟨F, hF, M, hM, K, hK, hb⟩ := hb (h ∘ e) (hh.comp_coarse he)
  exact ⟨_, hF.relabel e, M, hM, K, hK, fun z => by simpa using hb z⟩

/-- Common norm-continuity of the real diagonal orbits is preserved by relabeling. -/
theorem operatorRelabel_mem_coarseContinuityPoints {X Y : Type*}
    {C : CoarseStructure X} {D : CoarseStructure Y} (e : X ≃ Y)
    (he : IsCoarseMap C D e) {a : Operator X} (ha : a ∈ coarseContinuityPoints C) :
    operatorRelabel e a ∈ coarseContinuityPoints D := by
  intro h hh
  have hc := (operatorRelabelIsometry e).continuous.comp (ha (h ∘ e) (hh.comp_coarse he))
  change Continuous (fun t => operatorRelabel e (diagonalFlow (h ∘ e) t a)) at hc
  change Continuous (fun t => diagonalFlow h t (operatorRelabel e a))
  simpa only [operatorRelabel_diagonalFlow] using hc

/-- A bijection coarse in both directions carries all four dynamical algebras exactly. -/
theorem operatorRelabel_dynamical_algebras {X Y : Type*}
    {C : CoarseStructure X} {D : CoarseStructure Y} (e : X ≃ Y)
    (he : IsCoarseMap C D e) (hei : IsCoarseMap D C e.symm) :
    operatorRelabel e '' stripAnalyticPoints C = stripAnalyticPoints D ∧
    operatorRelabel e '' entireAnalyticPoints C = entireAnalyticPoints D ∧
    operatorRelabel e '' exponentialAnalyticPoints C = exponentialAnalyticPoints D ∧
    operatorRelabel e '' coarseContinuityPoints C = coarseContinuityPoints D := by
  have image_eq (S : Set (Operator X)) (T : Set (Operator Y))
      (hf : ∀ a ∈ S, operatorRelabel e a ∈ T)
      (hg : ∀ b ∈ T, operatorRelabel e.symm b ∈ S) : operatorRelabel e '' S = T := by
    apply Set.Subset.antisymm
    · rintro _ ⟨a, ha, rfl⟩
      exact hf a ha
    · intro b hb
      exact ⟨operatorRelabel e.symm b, hg b hb, by simpa using operatorRelabel_inverse e.symm b⟩
  exact ⟨image_eq _ _ (fun _ => operatorRelabel_mem_stripAnalyticPoints e he)
      (fun _ => operatorRelabel_mem_stripAnalyticPoints e.symm hei),
    image_eq _ _ (fun _ => operatorRelabel_mem_entireAnalyticPoints e he)
      (fun _ => operatorRelabel_mem_entireAnalyticPoints e.symm hei),
    image_eq _ _ (fun _ => operatorRelabel_mem_exponentialAnalyticPoints e he)
      (fun _ => operatorRelabel_mem_exponentialAnalyticPoints e.symm hei),
    image_eq _ _ (fun _ => operatorRelabel_mem_coarseContinuityPoints e he)
      (fun _ => operatorRelabel_mem_coarseContinuityPoints e.symm hei)⟩

/-- A map close to a coarse map is coarse, for arbitrary coarse structures. -/
theorem IsCoarseMap.of_close {X Y : Type*} {C : CoarseStructure X}
    {D : CoarseStructure Y} {f g : X → Y} (hf : IsCoarseMap C D f)
    (hfg : CoarseClose D f g) : IsCoarseMap C D g := by
  intro E hE
  refine D.subset ?_ (D.comp (D.inverse hfg) (D.comp (hf E hE) hfg))
  rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
  exact ⟨f x, ⟨x, rfl⟩, f y, ⟨(x, y), hxy, rfl⟩, ⟨y, rfl⟩⟩

/-- The genuine inverse of the bijection in a bijective coarse equivalence is coarse. -/
theorem AreBijectivelyCoarselyEquivalent.exists_equiv {X Y : Type*}
    {C : CoarseStructure X} {D : CoarseStructure Y}
    (h : AreBijectivelyCoarselyEquivalent C D) :
    ∃ e : X ≃ Y, IsCoarseMap C D e ∧ IsCoarseMap D C e.symm := by
  obtain ⟨f, g, hf, hfc, hgc, hclose, _⟩ := h
  let e : X ≃ Y := Equiv.ofBijective f hf
  refine ⟨e, hfc, hgc.of_close ?_⟩
  refine C.subset ?_ (C.inverse hclose)
  rintro _ ⟨y, rfl⟩
  refine ⟨e.symm y, ?_⟩
  change (e.symm y, g (e (e.symm y))) = (e.symm y, g y)
  rw [e.apply_symm_apply]

/-- The dynamical algebras depend only on the bijective coarse-equivalence class,
with all four identifications implemented by one spatial, isometric complex star-isomorphism. -/
theorem AreBijectivelyCoarselyEquivalent.dynamical_algebras {X Y : Type*}
    {C : CoarseStructure X} {D : CoarseStructure Y}
    (h : AreBijectivelyCoarselyEquivalent C D) :
    ∃ Φ : Operator X ≃⋆ₐ[ℂ] Operator Y, Isometry Φ ∧
      Φ '' stripAnalyticPoints C = stripAnalyticPoints D ∧
      Φ '' entireAnalyticPoints C = entireAnalyticPoints D ∧
      Φ '' exponentialAnalyticPoints C = exponentialAnalyticPoints D ∧
      Φ '' coarseContinuityPoints C = coarseContinuityPoints D := by
  obtain ⟨e, he, hei⟩ := h.exists_equiv
  exact ⟨operatorRelabel e, (operatorRelabelIsometry e).isometry,
    operatorRelabel_dynamical_algebras e he hei⟩

/-- The graph-union consequence following Theorem E: exponential quasi-locality,
after norm closure, is a bijective coarse invariant within this class. -/
theorem AreBijectivelyCoarselyEquivalent.graph_exponential_algebras {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] (hX : UniformlyLocallyFinite X)
    (hY : UniformlyLocallyFinite Y) (GX : CoarseGraphUnion X) (GY : CoarseGraphUnion Y)
    (h : AreBijectivelyCoarselyEquivalent (CoarseStructure.ofPseudoMetric X)
      (CoarseStructure.ofPseudoMetric Y)) :
    ∃ Φ : Operator X ≃⋆ₐ[ℂ] Operator Y, Isometry Φ ∧
      Φ '' exponentialQuasiLocal = exponentialQuasiLocal := by
  obtain ⟨Φ, hΦ, hstrip, _⟩ := h.dynamical_algebras
  exact ⟨Φ, hΦ, by simpa only [(theoremE hX).2 ⟨GX⟩,
    (theoremE hY).2 ⟨GY⟩] using hstrip⟩

end DynamicalCStarAlgebras
