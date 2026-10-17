import PfaffianDescent.SerreActualCubicGroundFamilyNativeGeometryParameters
import PfaffianDescent.CubicConfigurationRankChosenEvidenceGeometry

/-! Partial native module/zero geometry adapter.
The actual native coefficient cubic, pulled module, parameter map and B-zero
are fixed. E/cA remain abstract declaration inputs. The selected point/map,
Evidence and avoidance remain subsequent function inputs as in the generic
adapter. This conditional adapter is not a public Evidence producer; final
assembly must supply the accepted native selected-section DATA factory.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Exact native pp/qp/zero specialization; q/hq/v/hv/n/Evidence/avoidance are
left abstract. Actual zero closedness is derived internally. Result inferred. -/
@[irreducible]
def serreActualCubicGroundFamily_nativeGeometryModuleZeroPartialProvider
    {K E : Type u} [Field K] [CharZero K] [Field E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
    [IsIntegral (cubicConfigurationBase p hp 3)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 3).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫ cubicConfigurationToBase p hp 3)
    {D : Scheme.{u}} [IsAffine D]
    (ι : D ⟶ hypersurface p hp) [IsClosedImmersion ι]
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    {IB : Type u} [Fintype IB] [DecidableEq IB]
    (B : letI : Algebra K (cubicConfigurationBase p hp 3).functionField := a.hom.toAlgebra
      SchemeModuleFiniteFreeAffineCover
        ((Scheme.Modules.pullback
          (cubicPointTraceFieldBaseChangeCubicCoefficientMap
            (algebraMap K (cubicConfigurationBase p hp 3).functionField) p hp)).obj e.E) IB)
    {Rk : Scheme.{u}} [IsIntegral Rk]
    (cA : Spec (.of E) ⟶ Rk)
    (aRank : Rk ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    [IsOpenImmersion aRank]
    (β : (cubicConfigurationBase p hp 3).functionField →+* E)
    (hβ : Spec.map (CommRingCat.ofHom β) ≫
      (cubicConfigurationBase p hp 3).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 3)) =
      (cA ≫ aRank) ≫ configurationQuotientMap (equationIdeal p hp) 3) :=
  letI : Algebra K (cubicConfigurationBase p hp 3).functionField := a.hom.toAlgebra
  letI : Algebra (cubicConfigurationBase p hp 3).functionField E := β.toAlgebra
  letI := serreActualNativeGeometryPulledModule_finiteDimensional
    (F := (cubicConfigurationBase p hp 3).functionField) p hp e C
  letI := serreActualNativeGeometryZeroToAmbient_isClosedImmersion
    (F := (cubicConfigurationBase p hp 3).functionField) p hp e C B
  cubicConfigurationRankChosenEvidence_geometry
    p hp hp0 cA aRank β hβ a ha ι
    (serreActualNativeGeometryParametersToBase
      (F := (cubicConfigurationBase p hp 3).functionField) p hp e C)
    (toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 3) (cubicConfigurationBase p hp 3).functionField)))
    (serreActualNativeGeometryZeroToAmbient
      (F := (cubicConfigurationBase p hp 3).functionField) p hp e C B)

end PfaffianDescent
