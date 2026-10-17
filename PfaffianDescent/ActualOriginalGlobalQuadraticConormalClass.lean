import PfaffianDescent.ActualOriginalQuadraticConormalPointChartIso
import PfaffianDescent.ActualOriginalNativeQuadraticConormalClass

/- SOURCE ONLY / UNVERIFIED. Genuine ORIGINAL globally pulled-back cubic
ideal/O2 section, after the derived SAME chart Iso and genuine I/I² comparison,
is its SAME actual native conormal class. Domain remains genuine AMBIENT H0. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist IdealSheafDataModule
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

lemma actualOriginalGlobalQuadraticConormalClass_eq_native
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := closedImmersionIdealTwist q (positiveSheafOfModules (grading I) 2)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R ((hypersurface p hp).residueField P.1) := C.residue.toAlgebra
    surjectiveResidueTensorConormalEquiv C.residue C.residue_surjective
      (actualAffineConormalTensorEquiv C.residue C.residue_surjective
        ((moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))).map
          (actualOriginalQuadraticConormalPointChartIso p hp P hP).hom
          (actualModulePointSectionClass q M
            (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)))) =
    actualOriginalIdealQuadraticConormalClass p hp P hP s := by
  dsimp only
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let R := ChartRing I C.index
  letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
  letI : Algebra R ((hypersurface p hp).residueField P.1) := C.residue.toAlgebra
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom C.residue)) :=
    IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  rw [actualOriginalQuadraticConormalPointChartIso_section,
    actualAffineConormalClass_nativeSection,
    actualOriginalIdealQuadraticConormalClass_apply]

end PfaffianDescent
