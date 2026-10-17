import PfaffianDescent.ActualClosedImmersionFactorIdealTwistGlobalSections
import PfaffianDescent.SchemeModuleGlobalSectionsBaseEq
import PfaffianDescent.ActualOriginalIdealQuadraticNativeRestriction

/- SOURCE ONLY / UNVERIFIED. Start with actual AMBIENT H0(P3,I_P(2)),
restrict to the SAME original cubic ideal, and retain the actual pullback
of ambient O(2). No ambient/cubic ideal replacement or comparison premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

def actualOriginalAmbientIdealQuadraticCubicRestriction
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp)) :
    ActualOriginalPointIdealQuadraticSections p hp P →ₗ[K]
      SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
        (schemeModuleTensor
          (IdealSheafDataModule.closedImmersionModule
            ((hypersurface p hp).fromSpecResidueField P.1))
          ((Scheme.Modules.pullback (quotientProjMap (equationIdeal p hp))).obj
            (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2))) := by
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let i := quotientProjMap (equationIdeal p hp)
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion (q ≫ i) := inferInstance
  let F := actualClosedImmersionFactorIdealTwistGlobalSectionsRestriction
    (ambientToBase (R := K) (σ := Fin 4)) i q
    (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)
  let M := schemeModuleTensor
    (IdealSheafDataModule.closedImmersionModule q)
    ((Scheme.Modules.pullback i).obj
      (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2))
  exact (schemeModuleGlobalSectionsBaseEqLinearEquiv
    (i ≫ ambientToBase (R := K) (σ := Fin 4))
    (hypersurfaceToBase p hp)
    (quotientProjMap_toBase (equationIdeal p hp)) M).toLinearMap.comp F

end PfaffianDescent
