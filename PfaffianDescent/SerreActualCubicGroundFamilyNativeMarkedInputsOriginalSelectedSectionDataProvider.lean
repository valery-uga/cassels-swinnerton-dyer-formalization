import PfaffianDescent.SerreActualCubicGroundFamilyNativeMarkedInputsKernelParameterPartialProvider
import PfaffianDescent.SerreActualCubicGroundFamilyNativeMarkedInputsFiniteChosenProvider
import PfaffianDescent.CubicConfigurationGenericMarkedOutsideSupport

/-! Actual selected native marked Inputs DATA. The primitive original point,
Serre extension, rank chart, matrices, qF and old seed are unchanged. Finite
chosen fibre is derived from hgood; WHOLE geometry is constructed by the
accepted full native DATA producer. No geometry/Evidence/finite/support
certificate is supplied as an input. A/B are the same covers already used
by the original Core; the original wrapper instantiates their canonical
Serre covers internally, rather than adding covers to its public contract. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[irreducible]
def serreActualCubicGroundFamily_nativeMarkedInputsOriginalSelectedSectionDataProvider
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
    {IA IB : Type u} [Fintype IA] [DecidableEq IA] [Fintype IB] [DecidableEq IB]
    (A : SchemeModuleFiniteFreeAffineCover e.E IA)
    (B : letI : Algebra K (cubicConfigurationBase p hp 3).functionField := a.hom.toAlgebra
      SchemeModuleFiniteFreeAffineCover
        ((Scheme.Modules.pullback
          (cubicPointTraceFieldBaseChangeCubicCoefficientMap
            (algebraMap K (cubicConfigurationBase p hp 3).functionField) p hp)).obj e.E) IB)
    {Rk : Scheme.{u}} [IsIntegral Rk]
    (aRank : Rk ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    [IsOpenImmersion aRank]
    (β : (cubicConfigurationBase p hp 3).functionField →+*
      Rk.residueField (genericPoint Rk))
    (hβ : Spec.map (CommRingCat.ofHom β) ≫
      (cubicConfigurationBase p hp 3).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 3)) =
      (serreActualNativeOriginalResidueConfigurationPoint Rk ≫ aRank) ≫
        configurationQuotientMap (equationIdeal p hp) 3)
    (G : Matrix (Fin 9) (Fin 3) (cubicConfigurationBase p hp 3).functionField)
    (H : Matrix (Fin 3) (Fin 9) (cubicConfigurationBase p hp 3).functionField)
    (hHG : H * G = 1)
    (qF : Spec (.of (cubicConfigurationBase p hp 3).functionField) ⟶
      scheme (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 3) (cubicConfigurationBase p hp 3).functionField)))
    (hqF : qF ≫ toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 3) (cubicConfigurationBase p hp 3).functionField)) = 𝟙 _)
    (s : Spec (.of (Rk.residueField (genericPoint Rk))) ⟶
      serreActualNativeOriginalSectionIncidence p hp e A aRank)
    (hsp : letI : Algebra K (cubicConfigurationBase p hp 3).functionField := a.hom.toAlgebra
      s ≫ serreActualNativeOriginalSectionIncidenceToParameters p hp e A aRank =
        serreActualNativeSelectedResidueParameter β qF ≫
          serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG)
    (hcfg : s ≫ serreActualNativeOriginalSectionIncidenceToConfiguration p hp e A aRank =
      serreActualNativeOriginalResidueConfigurationPoint Rk)
    (hgood : s (IsLocalRing.closedPoint (Rk.residueField (genericPoint Rk))) ∈
      serreActualNativeMarkedInputsOriginalSectionIncidenceGoodOpen p hp e A aRank)
    (hmarked : s (IsLocalRing.closedPoint (Rk.residueField (genericPoint Rk))) ∈
      serreActualNativeOriginalSectionIncidenceMarkedOpen p hp e A aRank) :=
  letI : Algebra K (cubicConfigurationBase p hp 3).functionField := a.hom.toAlgebra
  letI : HasExt.{u} (hypersurface p hp).Modules := schemeModules_hasExt _
  letI : HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules := schemeModules_hasExt _
  letI : Finite ↥(pullback
      (serreActualNativeGeometryZeroToAmbient
        (F := (cubicConfigurationBase p hp 3).functionField) p hp e C B ≫
        pullback.snd
          (serreActualNativeGeometryCubicToBase
            (F := (cubicConfigurationBase p hp 3).functionField) p hp)
          (serreActualNativeGeometryParametersToBase
            (F := (cubicConfigurationBase p hp 3).functionField) p hp e C))
      (serreActualNativeSelectedResidueParameter β qF ≫
        serreActualCubicGroundKernelParameters p hp e C h9 G H hHG)) :=
    serreActualCubicGroundFamily_nativeMarkedInputsFiniteChosenProvider
    p hp a e C h9 A B aRank β G H hHG qF s hsp hgood
  serreActualCubicGroundFamily_nativeMarkedInputsKernelParameterPartialProvider
    p hp hp0 a ha ι e C h9 B β G H hHG qF
    (serreActualCubicGroundFamily_nativeOriginalSelectedSectionGeometryDataProvider
      p hp hp0 a ha ι e C h9 A B aRank β hβ G H hHG qF hqF
      s hsp hmarked hcfg (0 : Fin 3)
      (cubicConfigurationGenericMarkedOutsideSupport_rank_fieldpoint
        K p hp hp0 ι hι hL aRank (0 : Fin 3)))

end PfaffianDescent
