import AllCharacteristics.GradedOverlapLifting
import AllCharacteristics.ProjectiveChartOverlap

/-!
# Ring-valued points on projective coefficient overlaps

A homomorphism from a coordinate-chart ring extends to the actual overlap
ring whenever its second distinguished coordinate is invertible.
-/

namespace AllCharacteristics
namespace HomogeneousProjective
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))

/-- Extend a chart point to the actual overlap by inverting the second coordinate ratio. -/
theorem exists_chartOverlap_hom (i j : σ) (φ : ChartRing I i →+* A)
    (hu : IsUnit (φ (chartCoordinate I i j))) :
    ∃ ψ : ChartOverlapRing I i j →+* A, ψ.comp (chartOverlapLeftMap I i j) = φ :=
  GradedChart.exists_overlap_hom (grading I) (coordinate_mem I i) (coordinate_mem I j) φ hu

end HomogeneousProjective
end AllCharacteristics
