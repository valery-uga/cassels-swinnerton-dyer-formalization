import PfaffianDescent.SerreActualCubicGroundFamilyMarkedGeometryCore
import PfaffianDescent.SerreActualCubicGroundFamilyOldSelectedNativeGoodMembership
import PfaffianDescent.SerreActualChosenMarkedResidualGeometry
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGroundSelectedCanonicalMarked
import PfaffianDescent.SerreActualGroundFamilyLiteralMarkedSurfaceOriginal
import PfaffianDescent.CubicConfigurationOrderedFieldCoefficientMarkedIdentification
import PfaffianDescent.SerreActualChosenMarkedParameterAssociationPointSurface
import PfaffianDescent.SerreActualCubicGroundFamilyLiteralTransportedMarkedStalk
import PfaffianDescent.SerreActualCubicGroundFamilyOldGoodSeedNewMarkedGoodOpen
import PfaffianDescent.SerreActualCubicGroundFamilyOldSeedNewMarkedSupportAvoidance
import PfaffianDescent.CubicConfigurationGenericMarkedOutsideSupport

/-! Actual old selected incidence data give residual eight at the same native
G/H/qF. All new marked field/support/finite-good data are constructed internally. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 250000 in
@[irreducible]
def serreActualCubicGroundFamily_oldSelectedSeed_nativeMarkedResidualGeometry
    {K L : Type u} [fieldK : Field K] [charZeroK : CharZero K] [fieldL : Field L] [algebraKL : Algebra K L]
    [finiteKL : FiniteDimensional K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [smoothP : Smooth (hypersurfaceToBase p hp)]
    [configNonempty : Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
    [configIntegral : IsIntegral (cubicConfigurationBase p hp 3)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 3).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫ cubicConfigurationToBase p hp 3)
    (ι : Spec (.of L) ⟶ hypersurface p hp) [closedIota : IsClosedImmersion ι]
    (hι : ι ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hL : finrank K L = 11)
    (e : SerreExtensionData (hypersurface p hp)
      (closedImmersionIdealTwist ι (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [finiteSections : FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    {Rk : Scheme.{u}} [rankIntegral : IsIntegral Rk]
    (aRank : Rk ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    [rankOpen : IsOpenImmersion aRank] :=
  let F := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  let A := serreIncidenceRankTwoAffineCover e C
  let e' := cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalSerre a.hom p hp ι e C
  let C' := cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalCover a.hom p hp ι e C
  let B := serreIncidenceRankTwoAffineCover e' C'
  letI : HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules := schemeModules_hasExt _
  let havoid := cubicConfigurationGenericMarkedOutsideSupport_rank_fieldpoint
    K p hp hp0 ι hι hL aRank (0 : Fin 3)
  serreActualCubicGroundFamily_selectedSeed_markedGeometryCore
    p hp hp0 a ha ι e C h9 A B aRank havoid

end PfaffianDescent
