import PfaffianDescent.SerreActualCubicGroundFamilyNativeMarkedInputsActualResidueOriginalPointsPartialProvider

/-! Fix SAME native selected β/qF/G parameter;
chosen-fibre Finite and WHOLE geometry remain abstract FUNCTION inputs.
Raw @ application prevents eager synthesis of the remaining Finite argument. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[irreducible]
def serreActualCubicGroundFamily_nativeMarkedInputsKernelParameterPartialProvider
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
        (serreActualNativeGeometryPulledModule
          (F := (cubicConfigurationBase p hp 3).functionField) p hp e) IB)
    {Rk : Scheme.{u}} [IsIntegral Rk]
    (β : (cubicConfigurationBase p hp 3).functionField →+*
      Rk.residueField (genericPoint Rk))
    (G : Matrix (Fin 9) (Fin 3) (cubicConfigurationBase p hp 3).functionField)
    (H : Matrix (Fin 3) (Fin 9) (cubicConfigurationBase p hp 3).functionField)
    (hHG : H * G = 1)
    (qF : Spec (.of (cubicConfigurationBase p hp 3).functionField) ⟶
      scheme (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 3) (cubicConfigurationBase p hp 3).functionField))) :=
  letI : Algebra K (cubicConfigurationBase p hp 3).functionField := a.hom.toAlgebra
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional
    (F := (cubicConfigurationBase p hp 3).functionField) p hp e C
  @serreActualCubicGroundFamily_nativeMarkedInputsActualResidueOriginalPointsPartialProvider
    K _ _ p hp hp0 _ _ _ a ha D _ ι _ N e C _ IB _ _ B Rk _ β
    (serreActualNativeSelectedResidueParameter β qF ≫
      serreActualCubicGroundKernelParameters p hp e C h9 G H hHG)

end PfaffianDescent
