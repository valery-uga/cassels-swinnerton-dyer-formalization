import PfaffianDescent.ActualOriginalNativeQuadraticIdealSection
import PfaffianDescent.ActualAffineConormalNativeSectionClass
import PfaffianDescent.ActualOriginalIdealQuadraticConormalClass

/- SOURCE ONLY / UNVERIFIED. SAME original genuine ambient H0 section,
actual cubic ideal/nativeO2 restriction, actual source-preserving chart ideal
section, actual residue point pullback, and genuine affine I/I² class agree. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist IdealSheafDataModule
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

lemma actualOriginalNativeQuadraticIdealSection_conormalClass
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R ((hypersurface p hp).residueField P.1) := C.residue.toAlgebra
    surjectiveResidueTensorConormalEquiv C.residue C.residue_surjective
      (actualAffineConormalTensorEquiv C.residue C.residue_surjective
        (actualModulePointSectionClass (Spec.map (CommRingCat.ofHom C.residue))
          (closedImmersionModule (Spec.map (CommRingCat.ofHom C.residue)))
          (actualOriginalNativeQuadraticIdealChartSection p hp P hP s))) =
      actualOriginalIdealQuadraticConormalClass p hp P hP s := by
  dsimp only
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let R := ChartRing I C.index
  letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
  letI : Algebra R ((hypersurface p hp).residueField P.1) := C.residue.toAlgebra
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom C.residue)) :=
    IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  rw [actualOriginalNativeQuadraticIdealChartSection_eq_native,
    actualAffineConormalClass_nativeSection,
    actualOriginalIdealQuadraticConormalClass_apply]

end PfaffianDescent
