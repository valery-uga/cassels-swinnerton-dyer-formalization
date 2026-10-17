import PfaffianDescent.SerreActualCubicGroundFamilyNativeGeometryModuleZeroPartialProvider
import PfaffianDescent.SerreActualCubicGroundFamilyNativeOriginalSelectedSectionEvidenceProvider

/-! Partial native geometry application at the actual original residue-field point.
Fixes only the literal rank-chart generic residue field and actual original
fromSpecResidueField point. q/hq/v/hv/n/Evidence/avoidance stay unapplied.
No field/configuration lets, outer lambda, duplicated output contract or
Evidence/geometry certificates occur. 
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Exact actual E/cA specialization of the partial native module/zero
geometry adapter. Remaining selected-point/kernel/Evidence inputs unchanged. -/
@[irreducible]
def serreActualCubicGroundFamily_nativeGeometryActualResiduePartialProvider
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
      (serreActualNativeOriginalResidueConfigurationPoint Rk ≫ aRank) ≫ configurationQuotientMap (equationIdeal p hp) 3) :=
  serreActualCubicGroundFamily_nativeGeometryModuleZeroPartialProvider
    p hp hp0 a ha ι e C B
    (E := Rk.residueField (genericPoint Rk))
    (serreActualNativeOriginalResidueConfigurationPoint Rk) aRank β hβ

end PfaffianDescent
