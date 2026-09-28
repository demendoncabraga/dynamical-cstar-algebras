import DynamicalCStarAlgebras.SphereCoordinateMoments
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-! Haar probability on the finite-dimensional complex unitary group and
its orbit laws, used by the Gaussian concentration proof of the cited
Li--Zhang--Zhu frame-subspace theorem. -/

noncomputable section
open Classical MeasureTheory Set
namespace DynamicalCStarAlgebras

/-- The unitary group of a finite complex Euclidean space. -/
abbrev EuclideanUnitary (ι : Type*) [Fintype ι] :=
  unitary (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)

local instance euclideanOperator_continuousStar {ι : Type*} [Fintype ι] :
    ContinuousStar (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
  ⟨ContinuousLinearMap.adjoint.continuous⟩

instance euclideanUnitary_compactSpace {ι : Type*} [Fintype ι] :
    CompactSpace (EuclideanUnitary ι) := by
  apply isCompact_iff_compactSpace.mp
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨isClosed_unitary, ?_⟩
  rw [Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)]
  refine ⟨1, ?_⟩
  intro T hT
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact T.opNorm_le_bound zero_le_one (fun z => by
    simpa only [one_mul] using (Unitary.norm_map ⟨T, hT⟩ z).le)

/-- Haar probability, normalized on the entire compact unitary group. -/
def euclideanUnitaryHaar {ι : Type*} [Fintype ι] : Measure (EuclideanUnitary ι) :=
  Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

instance euclideanUnitaryHaar_probability {ι : Type*} [Fintype ι] :
    IsProbabilityMeasure (euclideanUnitaryHaar (ι := ι)) := by
  constructor
  exact Measure.haarMeasure_self

instance euclideanUnitaryHaar_leftInvariant {ι : Type*} [Fintype ι] :
    (euclideanUnitaryHaar (ι := ι)).IsMulLeftInvariant :=
  inferInstanceAs (Measure.haarMeasure _).IsMulLeftInvariant

lemma measurable_unitary_apply {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    Measurable (fun U : EuclideanUnitary ι => (U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) v) :=
  (continuous_subtype_val.clm_apply continuous_const).measurable

/-- The law of a Haar-random unitary applied to a fixed vector. -/
def unitaryOrbitLaw {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    Measure (EuclideanSpace ℂ ι) :=
  Measure.map (fun U : EuclideanUnitary ι => (U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) v)
    euclideanUnitaryHaar

instance unitaryOrbitLaw_probability {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    IsProbabilityMeasure (unitaryOrbitLaw v) :=
  Measure.isProbabilityMeasure_map (measurable_unitary_apply v).aemeasurable

end DynamicalCStarAlgebras
