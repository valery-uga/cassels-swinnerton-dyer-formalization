import PfaffianDescent.SerreActualCubicGroundFamilyNativeMarkedInputsModuleZeroPartialProvider
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGroundSelectedCanonicalMarked
import PfaffianDescent.SerreActualCubicGroundFamilyNativeOriginalSelectedSectionEvidenceProvider

/-! Fix the actual native F/E, original coefficient
point and SAME canonical D3 Spec map. Selected tE, Finite and whole d remain
unapplied. No selected-support geometry or finiteness is assumed by this
partial stage beyond the still-abstract generic bridge arguments. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[irreducible]
def serreActualCubicGroundFamily_nativeMarkedInputsActualResidueOriginalPointsPartialProvider
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
        (serreActualNativeGeometryPulledModule
          (F := (cubicConfigurationBase p hp 3).functionField) p hp e) IB)
    {Rk : Scheme.{u}} [IsIntegral Rk]
    (β : (cubicConfigurationBase p hp 3).functionField →+*
      Rk.residueField (genericPoint Rk)) :=
  letI : Algebra K (cubicConfigurationBase p hp 3).functionField := a.hom.toAlgebra
  letI : Algebra (cubicConfigurationBase p hp 3).functionField
    (Rk.residueField (genericPoint Rk)) := β.toAlgebra
  letI : HasExt.{u} (hypersurface p hp).Modules := schemeModules_hasExt _
  letI : HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules := schemeModules_hasExt _
  letI : IsFinite ((cubicConfigurationGenericFiniteSubscheme p hp 3 a ha).val.subschemeι ≫
      serreActualNativeGeometryCubicToBase
        (F := (cubicConfigurationBase p hp 3).functionField) p hp) :=
    (cubicConfigurationGenericFiniteSubscheme p hp 3 a ha).property.1
  letI : Field Γ((cubicConfigurationGenericFiniteSubscheme p hp 3 a ha).val.subscheme, ⊤) :=
    cubicClosedPointSerreFiniteZeroResidual_groundSelectedIsFieldField
      (cubicClosedPointSerreFiniteZeroResidual_groundSelectedMarked_isField p hp hp0 a ha)
  serreActualCubicGroundFamily_nativeMarkedInputsModuleZeroPartialProvider
    (F := (cubicConfigurationBase p hp 3).functionField)
    (E := Rk.residueField (genericPoint Rk))
    (L3 := Γ((cubicConfigurationGenericFiniteSubscheme p hp 3 a ha).val.subscheme, ⊤))
    p hp e C B
    (cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalPoint a.hom p hp ι)
    (finiteSubschemeDatumSpecMap
      (serreActualNativeGeometryCubicToBase
        (F := (cubicConfigurationBase p hp 3).functionField) p hp)
      (cubicConfigurationGenericFiniteSubscheme p hp 3 a ha))

end PfaffianDescent
