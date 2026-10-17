import PfaffianDescent.SerreActualCubicGroundFamilyOldSelectedNativeMarkedInputsType
import PfaffianDescent.SerreActualCubicGroundFamilyNativeMarkedInputsOriginalSelectedSectionDataProvider

/-! Same explicit original Inputs contract; canonical
A/B remain internally constructed let-values. The staged full DATA producer
discharges finite/geometry/avoidance internally. No added public premise. -/
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
def serreActualCubicGroundFamily_oldSelectedSeed_nativeMarkedResidualInputs
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
    [rankOpen : IsOpenImmersion aRank] :
    serreActualCubicGroundFamily_oldSelectedSeed_nativeMarkedResidualInputsType p hp hp0 a ha ι hι hL e C h9 aRank := by
  unfold serreActualCubicGroundFamily_oldSelectedSeed_nativeMarkedResidualInputsType
  intro F E cA c cfg marked hm A e' C' B x M pp zero D₃ j₃
    β hβ G H hHG qF hqF r bE s hsp hcfg hgood hmarked
  exact serreActualCubicGroundFamily_nativeMarkedInputsOriginalSelectedSectionDataProvider
    p hp hp0 a ha ι hι hL e C h9 A B aRank β hβ G H hHG qF hqF
    s hsp hcfg hgood hmarked

end PfaffianDescent
