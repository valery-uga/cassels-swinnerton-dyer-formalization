import PfaffianDescent.ActualOriginalAmbientIdealQuadraticCubicRestriction
import PfaffianDescent.ActualAmbientPositiveTwistQuotientIso
import PfaffianDescent.ActualModulePointSectionClass

/- SOURCE ONLY / UNVERIFIED. Genuine AMBIENT H0 FIRST restricts into
I_(P,S) tensor i^*O_P3(2), then the DERIVED actual graded twist Iso
identifies the twist with original native O_S(2). Only then pull to P.
No silent ambient/cubic ideal or twist substitution. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def actualOriginalAmbientIdealQuadraticNativeTwistRestriction
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp)) :
    ActualOriginalPointIdealQuadraticSections p hp P →ₗ[K]
      SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
        (schemeModuleTensor
          (IdealSheafDataModule.closedImmersionModule
            ((hypersurface p hp).fromSpecResidueField P.1))
          (positiveSheafOfModules (grading (equationIdeal p hp)) 2)) :=
  (schemeModuleGlobalSectionsMap (hypersurfaceToBase p hp)
    (schemeModuleTensorMap
      (𝟙 (IdealSheafDataModule.closedImmersionModule
        ((hypersurface p hp).fromSpecResidueField P.1)))
      (actualAmbientPositiveTwistQuotientIso (equationIdeal p hp) 2).hom)).comp
        (actualOriginalAmbientIdealQuadraticCubicRestriction p hp P)

def actualOriginalAmbientIdealQuadraticNativePointConormalRestriction
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    (moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor
          (IdealSheafDataModule.closedImmersionModule
            ((hypersurface p hp).fromSpecResidueField P.1))
          (positiveSheafOfModules (grading (equationIdeal p hp)) 2))) :=
  actualModulePointSectionClass ((hypersurface p hp).fromSpecResidueField P.1) _
    (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)

end PfaffianDescent
