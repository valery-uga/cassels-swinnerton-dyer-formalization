import PfaffianDescent.ProjectiveFiniteOfHilbertBound
import AllCharacteristics.AffineChartPresentation
import Mathlib.AlgebraicGeometry.Artinian

/-!
# Artinian affine charts of a finite projective polynomial quotient

A projective homogeneous quotient finite over its coefficient field has
Artinian standard affine charts.  This is the affine form of the finite
base-locus hypothesis used in the net-of-quadrics argument.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective

universe u

section

variable {K : Type u} [Field K] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every standard affine chart of a finite projective polynomial quotient is
Artinian. -/
theorem projective_chart_isArtinian_of_finite
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    [IsFinite (toBase I)] (j : σ) :
    IsArtinianRing (Away (grading I) (coordinate I j)) := by
  letI : IsLocallyArtinian (Proj (grading I)) := by
    change IsLocallyArtinian (scheme I)
    exact IsLocallyArtinian.of_locallyQuasiFinite (toBase I)
  letI : IsLocallyArtinian
      (Spec (.of (Away (grading I) (coordinate I j)))) :=
    IsLocallyArtinian.of_isImmersion
      (Proj.awayι (grading I) (coordinate I j) (coordinate_mem I j) (by decide : 0 < 1))
  change IsArtinianRing (Away (grading I) (coordinate I j))
  exact (Scheme.isLocallyArtinianScheme_Spec
    (R := CommRingCat.of (Away (grading I) (coordinate I j)))).mp inferInstance

/-- In the explicit coordinate presentation, a finite projective quotient has
an Artinian chart quotient.  Thus the relations obtained by setting one
homogeneous coordinate to one cut out a zero-dimensional affine scheme. -/
theorem chartPresentation_isArtinian_of_finite
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    [IsFinite (toBase I)] (j : σ) :
    IsArtinianRing (MvPolynomial σ K ⧸ chartPresentationIdeal I j) := by
  letI : IsArtinianRing (Away (grading I) (coordinate I j)) :=
    projective_chart_isArtinian_of_finite I j
  exact (chartPresentationEquiv I j).symm.isArtinianRing

/-- Every prime ideal of a coordinate presentation of a finite projective
quotient is maximal. -/
theorem chartPresentation_isMaximal_of_finite
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    [IsFinite (toBase I)] (j : σ)
    (P : Ideal (MvPolynomial σ K ⧸ chartPresentationIdeal I j)) [P.IsPrime] :
    P.IsMaximal := by
  letI : IsArtinianRing (MvPolynomial σ K ⧸ chartPresentationIdeal I j) :=
    chartPresentation_isArtinian_of_finite I j
  exact IsArtinianRing.isMaximal_of_isPrime P

/-- Finiteness of the projective quotient rules out nontrivial
specializations between its relevant homogeneous prime ideals. -/
theorem projective_spectrum_eq_of_finite
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    [IsFinite (toBase I)]
    (x y : ProjectiveSpectrum (grading I)) (hxy : x ≤ y) : x = y := by
  letI : IsLocallyArtinian (Proj (grading I)) := by
    change IsLocallyArtinian (scheme I)
    exact IsLocallyArtinian.of_locallyQuasiFinite (toBase I)
  letI : DiscreteTopology (ProjectiveSpectrum (grading I)) := by
    change DiscreteTopology (Proj (grading I))
    infer_instance
  have hmem : y ∈ closure ({x} : Set (ProjectiveSpectrum (grading I))) :=
    (ProjectiveSpectrum.le_iff_mem_closure (grading I) x y).mp hxy
  rw [closure_eq_iff_isClosed.mpr (isClosed_discrete _)] at hmem
  simpa using hmem.symm

end

end PfaffianDescent
