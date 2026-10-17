import PfaffianDescent.ActualModulePointSectionGroundLinear
import PfaffianDescent.ActualOriginalGlobalCanonicalQuadraticPhi
import AllCharacteristics.ClosedPointAlgebra

/- SOURCE ONLY / UNVERIFIED. The genuine globally natural original Phi
is K-LINEAR, using ONLY the actual original point/base scalar square.
No chart, perfectness, degree, dimension or Phi comparison certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

def actualOriginalGlobalCanonicalQuadraticPhiLinearMap
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp)) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let E2 := (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (hypersurfaceToBase p hp))
          (positiveSheafOfModules (grading (equationIdeal p hp)) 2)))
    letI : Module K E2 := Module.compHom E2 (algebraMap K L)
    ActualOriginalPointIdealQuadraticSections p hp P →ₗ[K] E2 := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let I := equationIdeal p hp
  let L := (hypersurface p hp).residueField P.1
  let q := (hypersurface p hp).fromSpecResidueField P.1
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let g := hypersurfaceToBase p hp
  let M := closedImmersionIdealTwist q (positiveSheafOfModules (grading I) 2)
  let O2 := schemeModuleTensor (schemeRelativeDifferentials g)
    (positiveSheafOfModules (grading I) 2)
  let E1 := (moduleSpecΓFunctor (R := .of L)).obj ((Scheme.Modules.pullback q).obj M)
  let E2 := (moduleSpecΓFunctor (R := .of L)).obj ((Scheme.Modules.pullback q).obj O2)
  letI : Module K E1 := Module.compHom E1 (algebraMap K L)
  letI : Module K E2 := Module.compHom E2 (algebraMap K L)
  letI : IsScalarTower K L E1 := IsScalarTower.of_compHom K L E1
  letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
  have hb : q ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K L)) :=
    (AllCharacteristics.pointAlgebra_spec g P.1).symm
  let point : SchemeModuleGlobalSectionsOver g M →ₗ[K] E1 :=
    actualModulePointSectionClassGroundLinearMap g q (algebraMap K L) hb M
  let d : E1 ⟶ E2 := (moduleSpecΓFunctor (R := .of L)).map
    (actualGlobalPositiveTwistConormalDifferentialMap I q 2)
  exact (d.hom.restrictScalars K).comp
    (point.comp (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P))

@[simp] lemma actualOriginalGlobalCanonicalQuadraticPhiLinearMap_apply
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let E2 := (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (hypersurfaceToBase p hp))
          (positiveSheafOfModules (grading (equationIdeal p hp)) 2)))
    letI : Module K E2 := Module.compHom E2 (algebraMap K L)
    actualOriginalGlobalCanonicalQuadraticPhiLinearMap p hp P s =
      actualOriginalGlobalCanonicalQuadraticPhi p hp P s := rfl

end PfaffianDescent
