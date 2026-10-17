import PfaffianDescent.SerreActualCubicGroundFamilyNativeMarkedInputsCanonicalAPartialProvider

/- Fix the canonical coefficient cover B after A has been
fixed separately. The actual rank chart and all selected seed data remain
function inputs. No geometry/finite/support certificate is added. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[irreducible]
def serreActualCubicGroundFamily_nativeMarkedInputsCanonicalABPartialProvider
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
    [IsIntegral (cubicConfigurationBase p hp 3)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 3).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫ cubicConfigurationToBase p hp 3)
    (ι : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion ι]
    (hι : ι ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hL : finrank K L = 11)
    (e : SerreExtensionData (hypersurface p hp)
      (closedImmersionIdealTwist ι (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    {Rk : Scheme.{u}} [IsIntegral Rk]
    (aRank : Rk ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    [IsOpenImmersion aRank] :=
  letI : Algebra K (cubicConfigurationBase p hp 3).functionField := a.hom.toAlgebra
  serreActualCubicGroundFamily_nativeMarkedInputsCanonicalAPartialProvider
    (IB := ULift.{u} (Fin 2)) p hp hp0 a ha ι hι hL e C h9
    (serreIncidenceRankTwoAffineCover
      (cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalSerre a.hom p hp ι e C)
      (cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalCover a.hom p hp ι e C))
    aRank

end PfaffianDescent
