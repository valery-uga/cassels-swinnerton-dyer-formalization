import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveTwistGerm

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The actual cubic chart-basis morphism is an isomorphism on the
common linear chart, with invertibility proved at every native stalk. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom_isIso
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1) :
    IsIso ((Scheme.Modules.restrictFunctor
      (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι).map
      (cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom I ell)) := by
  let U := Proj.basicOpen (grading I) (ell : CoordinateRing I)
  let F := Scheme.Modules.restrictFunctor U.ι
  have hspan : (HomogeneousIdeal.irrelevant (grading I)).toIdeal ≤
      Ideal.span (Set.range (fun f : grading I 1 => (f : CoordinateRing I))) :=
    gradedSurjective_irrelevant_le_span_degreeOne
      (homogeneousSubmodule (Fin 4) K) (grading I)
      (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
      mvPolynomial_irrelevant_le_span_degreeOne_small
  have hmul : IsIso (F.map
      (positiveMulHomogeneous (grading I) (degreeOnePower (grading I) ell 3) 0)) := by
    apply restrict_map_isIso_of_stalk U
    intro x
    letI : (positivePointIdeal (grading I) (U.ι x)).IsPrime :=
      ProjectiveSpectrum.isPrime (U.ι x)
    have hxell : (ell : CoordinateRing I) ∈
        (positivePointIdeal (grading I) (U.ι x)).primeCompl := by
      rw [Ideal.mem_primeCompl_iff]
      exact (ProjectiveSpectrum.mem_basicOpen (grading I)
        (ell : CoordinateRing I) (U.ι x)).mp x.2
    have hs : ((degreeOnePower (grading I) ell 3 : grading I 3) : CoordinateRing I) ∈
        (positivePointIdeal (grading I) (U.ι x)).primeCompl := by
      exact Submonoid.pow_mem _ hxell 3
    change IsIso ((TopCat.Presheaf.stalkFunctor _ (U.ι x)).map
      (positiveMulHomogeneousPresheaf (grading I) (degreeOnePower (grading I) ell 3) 0))
    exact positiveMulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
      (grading I) (degreeOnePower (grading I) ell 3) 0 (U.ι x) hs hspan
  letI : IsIso (F.map (unitToZeroTwist (grading I))) := by
    change IsIso (F.map (unitIsoZeroTwist (grading I)).hom)
    infer_instance
  letI : IsIso (F.map (zeroTwistToPositiveZero (grading I))) := by
    change IsIso (F.map (positiveZeroTwistIso (grading I)).inv)
    infer_instance
  letI := hmul
  change IsIso (F.map (cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom I ell))
  unfold cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

/-- The actual positive-three twist is the unit sheaf on the SAME common
linear chart used by the square-zero jet construction. -/
def cubicClosedPointSerreSurfaceJetCotangent_positiveThreeUnitIso
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1) :
    (Scheme.Modules.restrictFunctor
      (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι).obj
      (positiveSheafOfModules (grading I) 3) ≅
    SheafOfModules.unit
      ((Proj.basicOpen (grading I) (ell : CoordinateRing I) : Scheme).ringCatSheaf) := by
  letI := cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom_isIso I ell
  exact (asIso ((Scheme.Modules.restrictFunctor
      (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι).map
      (cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom I ell))).symm ≪≫
    Scheme.Modules.restrictUnitIso
      (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι

end PfaffianDescent
