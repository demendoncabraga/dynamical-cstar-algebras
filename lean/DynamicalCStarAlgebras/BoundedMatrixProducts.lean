import DynamicalCStarAlgebras.ExponentialProjectionBlocks
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.lpSpace
import Mathlib.Analysis.Normed.Lp.LpEquiv

noncomputable section

open scoped ENNReal

namespace DynamicalCStarAlgebras

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma isometry_adjoint_apply_self (e : H →ₗᵢ[ℂ] K) (x : H) :
    e.toContinuousLinearMap.adjoint (e x) = x := by
  simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self,
    LinearIsometry.coe_toContinuousLinearMap] using
    congrArg (fun f : H →L[ℂ] H => f x) e.adjoint_comp_self

/-- Extension by zero from a closed Hilbert subspace as a nonunital star algebra map. -/
def isometryCornerHom (e : H →ₗᵢ[ℂ] K) :
    (H →L[ℂ] H) →⋆ₙₐ[ℂ] (K →L[ℂ] K) where
  toFun a := e.toContinuousLinearMap.comp (a.comp e.toContinuousLinearMap.adjoint)
  map_zero' := by simp
  map_add' a b := by simp [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  map_mul' a b := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, mul_apply_eq_comp,
      LinearIsometry.coe_toContinuousLinearMap, isometry_adjoint_apply_self]
  map_smul' c a := by simp [ContinuousLinearMap.smul_comp]
  map_star' a := by
    change e.toContinuousLinearMap.comp (a.adjoint.comp e.toContinuousLinearMap.adjoint) =
      (e.toContinuousLinearMap.comp (a.comp e.toContinuousLinearMap.adjoint)).adjoint
    simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.comp_assoc]

theorem isometryCornerHom_injective (e : H →ₗᵢ[ℂ] K) :
    Function.Injective (isometryCornerHom e) := by
  intro a b h
  ext x
  apply e.injective
  have he := congrArg (fun f : K →L[ℂ] K => f (e x)) h
  simpa only [isometryCornerHom, NonUnitalStarAlgHom.coe_mk, NonUnitalAlgHom.coe_mk,
    ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    isometry_adjoint_apply_self] using he

/-- Pointwise corner maps act on the bounded C*-product, rather than the
unrestricted algebraic product. -/
def boundedProductHom {I J : Type*} {A : J → Type*} {B : I → Type*}
    [∀ j, NonUnitalCStarAlgebra (A j)] [∀ i, NonUnitalCStarAlgebra (B i)]
    (f : I → J) (φ : ∀ i, A (f i) →⋆ₙₐ[ℂ] B i)
    (hφ : ∀ i, Function.Injective (φ i)) :
    lp A ∞ →⋆ₙₐ[ℂ] lp B ∞ where
  toFun a := ⟨fun i => φ i (a (f i)), memℓp_infty ⟨‖a‖, by
    rintro _ ⟨i, rfl⟩
    exact (NonUnitalStarAlgHom.norm_map (φ i) (hφ i) (a (f i))).trans_le
      (lp.norm_apply_le_norm ENNReal.top_ne_zero a (f i))⟩⟩
  map_zero' := by ext i; exact map_zero (φ i)
  map_add' a b := by ext i; exact map_add (φ i) _ _
  map_mul' a b := by ext i; exact map_mul (φ i) _ _
  map_smul' c a := by ext i; exact map_smul (φ i) c _
  map_star' a := by ext i; exact map_star (φ i) _

theorem boundedProductHom_injective {I J : Type*} {A : J → Type*} {B : I → Type*}
    [∀ j, NonUnitalCStarAlgebra (A j)] [∀ i, NonUnitalCStarAlgebra (B i)]
    (f : I → J) (hf : Function.Surjective f) (φ : ∀ i, A (f i) →⋆ₙₐ[ℂ] B i)
    (hφ : ∀ i, Function.Injective (φ i)) :
    Function.Injective (boundedProductHom f φ hφ) := by
  intro a b h
  apply lp.ext
  funext j
  obtain ⟨i, rfl⟩ := hf j
  exact hφ i (congrArg (fun c : lp B ∞ => c i) h)

/-- An unbounded dimension sequence contains every matrix size, with unused
components assigned the zero-dimensional algebra. -/
lemma exists_surjective_rank_selector {d : ℕ → ℕ}
    (hd : Filter.Tendsto d Filter.atTop Filter.atTop) :
    ∃ f : ℕ → ℕ, Function.Surjective f ∧ ∀ i, f i ≤ d i := by
  classical
  obtain ⟨s, hs, hdim⟩ := Filter.extraction_forall_of_eventually
    (fun n => hd.eventually (Filter.eventually_ge_atTop n))
  let f (i : ℕ) : ℕ := if h : ∃ n, s n = i then h.choose else 0
  have hfs (n : ℕ) : f (s n) = n := by
    dsimp [f]
    split_ifs with h
    · exact hs.injective h.choose_spec
    · exact (h ⟨n, rfl⟩).elim
  refine ⟨f, fun n => ⟨s n, hfs n⟩, fun i => ?_⟩
  by_cases hi : ∃ n, s n = i
  · obtain ⟨n, rfl⟩ := hi
    rw [hfs]
    exact hdim n
  · simp only [f, dif_neg hi]
    exact Nat.zero_le _

/-- A finite-dimensional complex Hilbert space contains each smaller standard
Hilbert space isometrically. -/
def finHilbertIsometry (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (n : ℕ) (hn : n ≤ Module.finrank ℂ H) :
    HilbertSpace (Fin n) →ₗᵢ[ℂ] H :=
  (stdOrthonormalBasis ℂ H).repr.symm.toLinearIsometry.comp
    ((lpPiLpₗᵢ (fun _ : Fin (Module.finrank ℂ H) => ℂ) ℂ).toLinearIsometry.comp
      (coordinateEmbedding (Fin.castLE hn) (Fin.castLE_injective hn)))

/-- The bounded product of complex matrix algebras, realized with their usual
operator norms on the standard finite-dimensional Hilbert spaces. The index
zero contributes a trivial factor. -/
abbrev BoundedMatrixProduct := lp (fun n : ℕ => Operator (Fin n)) ∞

/-- The matrix-product step in Theorem Thm.Exp.decay.Still.Contains: Hilbert
spaces whose dimensions tend to infinity contain every finite matrix size
along a subsequence, giving an isometric embedding of the bounded products. -/
theorem exists_boundedMatrixProduct_embedding (W : ℕ → Type*)
    [∀ n, NormedAddCommGroup (W n)] [∀ n, InnerProductSpace ℂ (W n)]
    [∀ n, FiniteDimensional ℂ (W n)]
    (hdim : Filter.Tendsto (fun n => Module.finrank ℂ (W n)) Filter.atTop Filter.atTop) :
    ∃ Φ : BoundedMatrixProduct →⋆ₙₐ[ℂ] lp (fun n => W n →L[ℂ] W n) ∞,
      Function.Injective Φ ∧ Isometry Φ := by
  obtain ⟨f, hf, hbound⟩ := exists_surjective_rank_selector hdim
  let φ (i : ℕ) : Operator (Fin (f i)) →⋆ₙₐ[ℂ] (W i →L[ℂ] W i) :=
    isometryCornerHom (finHilbertIsometry (W i) (f i) (hbound i))
  have hφ (i : ℕ) : Function.Injective (φ i) :=
    isometryCornerHom_injective _
  let Φ := boundedProductHom (A := fun n => Operator (Fin n)) f φ hφ
  have hΦ : Function.Injective Φ :=
    boundedProductHom_injective (A := fun n => Operator (Fin n)) f hf φ hφ
  exact ⟨Φ, hΦ, NonUnitalStarAlgHom.isometry Φ hΦ⟩

end DynamicalCStarAlgebras
