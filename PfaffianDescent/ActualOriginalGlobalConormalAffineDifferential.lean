import PfaffianDescent.ActualOriginalGlobalQuadraticConormalClass
import PfaffianDescent.ActualAffineConormalDifferentialFiber

/-! SOURCE ONLY / UNVERIFIED. The SAME original globally pulled-back
ideal/native-O2 quadratic section, after the derived original chart source
comparison, maps to its actual affine genuinely sheafified differential class.
This is the affine comparison, not yet a global conormal sheaf map. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist IdealSheafDataModule
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

lemma actualOriginalGlobalQuadraticConormalClass_affineDifferential
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let M := closedImmersionIdealTwist q (positiveSheafOfModules (grading I) 2)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R ((hypersurface p hp).residueField P.1) := C.residue.toAlgebra
    actualAffineConormalDifferentialFiberMap (k := K) C.residue C.residue_surjective
      ((moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))).map
        (actualOriginalQuadraticConormalPointChartIso p hp P hP).hom
        (actualModulePointSectionClass q M
          (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s))) =
    actualAffineDifferentialPointClass (k := K) C.residue
      (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s) := by
  dsimp only
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let R := ChartRing I C.index
  letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
  letI : Algebra R ((hypersurface p hp).residueField P.1) := C.residue.toAlgebra
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom C.residue)) :=
    IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  rw [actualOriginalQuadraticConormalPointChartIso_section,
    actualAffineConormalDifferentialFiberMap_nativeSection]

lemma actualOriginalGlobalQuadraticConormalClass_affineUniversalSection
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let M := closedImmersionIdealTwist q (positiveSheafOfModules (grading I) 2)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R ((hypersurface p hp).residueField P.1) := C.residue.toAlgebra
    actualAffineConormalDifferentialFiberMap (k := K) C.residue C.residue_surjective
      ((moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))).map
        (actualOriginalQuadraticConormalPointChartIso p hp P hP).hom
        (actualModulePointSectionClass q M
          (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s))) =
    actualAffineSheafPointClass (CommRingCat.ofHom C.residue)
      (schemeRelativeDifferentials (Spec.map (CommRingCat.ofHom (algebraMap K R))))
      (actualRelativeDifferentialSection
        (Spec.map (CommRingCat.ofHom (algebraMap K R))) ⊤
        (algebraMap R Γ(Spec (.of R), ⊤)
          (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s))) := by
  dsimp only
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let R := ChartRing I C.index
  letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
  letI : Algebra R ((hypersurface p hp).residueField P.1) := C.residue.toAlgebra
  exact (actualOriginalGlobalQuadraticConormalClass_affineDifferential p hp P hP s).trans
    (actualAffineDifferentialPointClass_eq_actualPullbackD (k := K) C.residue
      (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s))

end PfaffianDescent
