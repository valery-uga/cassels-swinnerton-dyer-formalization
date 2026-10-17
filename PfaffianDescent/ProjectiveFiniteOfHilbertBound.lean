import PfaffianDescent.HomogeneousChartFinite
import PfaffianDescent.HomogeneousProjection
import AllCharacteristics.CoordinateCharts
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K : Type u} [Field K] {σ : Type} [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma polynomialQuotientGrade_finite
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) (n : ℕ) :
    Module.Finite K (grading I n) := by
  apply Module.Finite.iff_fg.mpr
  exact (MvPolynomial.homogeneousSubmodule_fg σ K n).map
    (Ideal.Quotient.mkₐ K I.toIdeal).toLinearMap

/-- An eventual finite bound on the actual homogeneous quotient components
makes the associated projective scheme finite over the coefficient field. -/
theorem projective_finite_of_hilbert_bound
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) (N D : ℕ)
    (hD : ∀ n, N ≤ n → finrank K (grading I n) ≤ D) : IsFinite (toBase I) := by
  letI : ∀ n, Module.Finite K (grading I n) := polynomialQuotientGrade_finite I
  have hcharts (j : σ) : (chartBaseMap I j).Finite := by
    exact (homogeneousChart_finite_of_bounded (grading I) (coordinate I j)
      (coordinate_mem I j) N D hD).1
  have : IsZariskiLocalAtSource (@LocallyQuasiFinite.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.QuasiFinite)
  have hqf : LocallyQuasiFinite (toBase I) := by
    apply (IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyQuasiFinite.{u})
      (coordinateOpenCover I).openCover).mpr
    intro j
    change σ at j
    change LocallyQuasiFinite (chartι I j ≫ toBase I)
    rw [chartι_toBase]
    haveI : IsFinite (Spec.map (CommRingCat.ofHom (chartBaseMap I j))) :=
      (IsFinite.SpecMap_iff _).mpr (hcharts j)
    infer_instance
  letI := hqf
  exact IsFinite.of_isProper_of_locallyQuasiFinite (toBase I)

end
end PfaffianDescent
