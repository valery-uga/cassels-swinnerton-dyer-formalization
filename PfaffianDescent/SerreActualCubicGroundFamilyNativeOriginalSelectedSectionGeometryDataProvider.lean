import PfaffianDescent.SerreActualCubicGroundFamilyNativeGeometryKernelParameterPartialProvider

/-! Literal selected-section geometry DATA from the checked native partial stages.
The actual section Evidence is constructed from the original incidence data;
no Evidence or geometry certificate is supplied as an assumption. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/- Actual native residual geometry from primitive incidence/parameter data.
The output, including exact original support and D3/j3, is inferred from the
checked generic geometry application, which constructs those data internally. -/
set_option profiler true in
set_option profiler.threshold 1000 in
set_option maxHeartbeats 250000 in
@[irreducible]
def serreActualCubicGroundFamily_nativeOriginalSelectedSectionGeometryDataProvider
    {K : Type u} [Field K] [CharZero K]
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
    (hmarked : s (IsLocalRing.closedPoint (Rk.residueField (genericPoint Rk))) ∈
      serreActualNativeOriginalSectionIncidenceMarkedOpen p hp e A aRank)
    (hcfg : s ≫ serreActualNativeOriginalSectionIncidenceToConfiguration p hp e A aRank =
      serreActualNativeOriginalResidueConfigurationPoint Rk)
    (n : Fin 3)
    (havoid : (serreActualNativeOriginalResidueConfigurationPoint Rk ≫ aRank ≫
      (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).left ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 n).left)
        (IsLocalRing.closedPoint (Rk.residueField (genericPoint Rk))) ∉ Set.range ι) :=
  serreActualCubicGroundFamily_nativeGeometryKernelParameterPartialProvider
    p hp hp0 a ha ι e C h9 B aRank β hβ G H hHG qF hqF
    n
    (serreActualCubicGroundFamily_nativeOriginalSelectedSectionEvidenceProvider
      p hp hp0 a ha ι e C h9 A B aRank β G H hHG qF s hsp hmarked hcfg n)
    havoid

end PfaffianDescent
