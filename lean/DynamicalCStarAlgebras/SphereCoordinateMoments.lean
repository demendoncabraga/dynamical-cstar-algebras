import DynamicalCStarAlgebras.HalfSphereNets

/-! Finite complex coordinate restrictions used in the checked Gaussian
concentration and frame-subspace construction. -/

noncomputable section
namespace DynamicalCStarAlgebras

/-- Coordinate restriction from a finite complex Euclidean space. -/
def euclideanCoordinateRestriction {ι : Type*} [Fintype ι] (A : Finset ι)
    (z : EuclideanSpace ℂ ι) : EuclideanSpace ℂ A :=
  WithLp.toLp 2 (fun i : A => z i)

lemma norm_sq_euclideanCoordinateRestriction {ι : Type*} [Fintype ι] (A : Finset ι)
    (z : EuclideanSpace ℂ ι) :
    ‖euclideanCoordinateRestriction A z‖ ^ 2 = ∑ i ∈ A, ‖z i‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  exact Finset.sum_coe_sort A (fun i => ‖z i‖ ^ 2)

end DynamicalCStarAlgebras
