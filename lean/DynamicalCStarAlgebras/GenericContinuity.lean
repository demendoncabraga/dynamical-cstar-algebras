import DynamicalCStarAlgebras.ContinuityPoints
import Mathlib.Analysis.CStarAlgebra.Hom

namespace DynamicalCStarAlgebras

/-- Continuity points for any family of complex C*-automorphisms, including
pre-flows on nonunital C*-algebras. -/
def continuousOrbitSubalgebra {A : Type*} [NonUnitalCStarAlgebra A]
    (σ : ℝ → A ≃⋆ₐ[ℂ] A) : NonUnitalStarSubalgebra ℂ A where
  carrier := {a | Continuous (fun t => σ t a)}
  zero_mem' := by simpa only [Set.mem_ofPred_eq, map_zero] using
    (continuous_const : Continuous (fun _ : ℝ => (0 : A)))
  add_mem' ha hb := by simpa only [Set.mem_ofPred_eq, map_add, Pi.add_def] using ha.add hb
  mul_mem' ha hb := by simpa only [Set.mem_ofPred_eq, map_mul, Pi.mul_def] using ha.mul hb
  star_mem' ha := by simpa only [Set.mem_ofPred_eq, map_star] using ha.star
  smul_mem' c a ha := by
    simpa only [Set.mem_ofPred_eq, map_smul, Pi.smul_def] using ha.const_smul c

/-- The continuity points of an arbitrary C*-pre-flow form a closed complex
star-subalgebra. No norm continuity of the pre-flow is assumed. -/
theorem continuousOrbitSubalgebra_isClosed {A : Type*} [NonUnitalCStarAlgebra A]
    (σ : ℝ → A ≃⋆ₐ[ℂ] A) : IsClosed (continuousOrbitSubalgebra σ : Set A) := by
  apply isClosed_continuousOrbitSet
  intro t a b
  exact (NonUnitalStarAlgHom.isometry (σ t) (σ t).injective).dist_eq a b |>.le

end DynamicalCStarAlgebras
