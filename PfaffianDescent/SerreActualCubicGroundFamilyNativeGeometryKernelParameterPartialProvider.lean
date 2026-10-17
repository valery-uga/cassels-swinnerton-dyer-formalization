import PfaffianDescent.SerreActualCubicGroundFamilyNativeGeometryActualResiduePartialProvider
import PfaffianDescent.SerreActualCubicGroundFamilyNativeOriginalSelectedSectionEvidenceProvider

/-! Partial native geometry stage at the actual selected kernel parameter map.
Fixes the actual selected qF and actual SAME-G ground kernel parameter map,
deriving its structural compatibility from the checked toBase theorem.
The marked index, Evidence and avoidance remain subsequent function inputs.
This conditional adapter is not a public Evidence producer.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Literal native selected-point/kernel-map partial geometry specialization.
No map compatibility or Evidence construction certificate is supplied. -/
@[irreducible]
def serreActualCubicGroundFamily_nativeGeometryKernelParameterPartialProvider
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
    {IB : Type u} [Fintype IB] [DecidableEq IB]
    (B : letI : Algebra K (cubicConfigurationBase p hp 3).functionField := a.hom.toAlgebra
      SchemeModuleFiniteFreeAffineCover
        ((Scheme.Modules.pullback
          (cubicPointTraceFieldBaseChangeCubicCoefficientMap
            (algebraMap K (cubicConfigurationBase p hp 3).functionField) p hp)).obj e.E) IB)
    {Rk : Scheme.{u}} [IsIntegral Rk]
    (aRank : Rk ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    [IsOpenImmersion aRank]
    (β : (cubicConfigurationBase p hp 3).functionField →+* Rk.residueField (genericPoint Rk))
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
      (homogeneousSubmodule (Fin 3) (cubicConfigurationBase p hp 3).functionField)) = 𝟙 _) :=
  letI : Algebra K (cubicConfigurationBase p hp 3).functionField := a.hom.toAlgebra
  serreActualCubicGroundFamily_nativeGeometryActualResiduePartialProvider
    p hp hp0 a ha ι e C B aRank β hβ
    qF hqF (serreActualCubicGroundKernelParameters p hp e C h9 G H hHG)
    (serreActualCubicGroundKernelParameters_toBase p hp e C h9 G H hHG)

end PfaffianDescent
