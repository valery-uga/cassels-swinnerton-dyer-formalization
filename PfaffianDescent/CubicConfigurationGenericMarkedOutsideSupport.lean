import PfaffianDescent.CubicConfigurationGenericMarkedOutsideSupportClosed
import PfaffianDescent.CubicConfigurationGenericMarkedOutsideSupportCoordinates
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicConfigurationGenericMarkedOutsideSupport_rank_generic
    (F : Type u) [Field F] [CharZero F]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (hP0 : P ≠ 0)
    [Smooth (hypersurfaceToBase P hP)]
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) F)).Modules]
    {L : Type u} [Field L] [Algebra F L]
    (i : Spec (.of L) ⟶ hypersurface P hP) [IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase P hP = Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (hL : Module.finrank F L = 11)
    {A : Scheme.{u}} [IsIntegral A]
    (a : A ⟶ (AllCharacteristics.orderedFamilyConfigurationOver (hypersurfaceToBase P hP) 3).left)
    [IsOpenImmersion a] (j : Fin 3) :
    (a ≫ (AllCharacteristics.orderedFamilyConfigurationι (hypersurfaceToBase P hP) 3).left ≫
      (AllCharacteristics.orderedFamilyCoordinate (hypersurfaceToBase P hP) 3 j).left)
        (genericPoint A) ∉ Set.range i := by
  let base := hypersurfaceToBase P hP
  letI : IsIntegral (hypersurface P hP) :=
    isIntegral_hypersurface_of_smooth_of_nonzero_of_infinite P hP hP0
  rw [cubicConfigurationGenericMarkedOutsideSupport_rank_coordinate_generic base a j]
  exact cubicConfigurationGenericMarkedOutsideSupport_generic_not_mem F P hP hP0 i hi hL

theorem cubicConfigurationGenericMarkedOutsideSupport_rank_fieldpoint
    (F : Type u) [Field F] [CharZero F]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (hP0 : P ≠ 0)
    [Smooth (hypersurfaceToBase P hP)]
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) F)).Modules]
    {L : Type u} [Field L] [Algebra F L]
    (i : Spec (.of L) ⟶ hypersurface P hP) [IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase P hP = Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (hL : Module.finrank F L = 11)
    {A : Scheme.{u}} [IsIntegral A]
    (a : A ⟶ (AllCharacteristics.orderedFamilyConfigurationOver (hypersurfaceToBase P hP) 3).left)
    [IsOpenImmersion a] (j : Fin 3) :
    (A.fromSpecResidueField (genericPoint A) ≫ a ≫
      (AllCharacteristics.orderedFamilyConfigurationι (hypersurfaceToBase P hP) 3).left ≫
      (AllCharacteristics.orderedFamilyCoordinate (hypersurfaceToBase P hP) 3 j).left)
        (IsLocalRing.closedPoint (A.residueField (genericPoint A))) ∉ Set.range i := by
  simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using
    cubicConfigurationGenericMarkedOutsideSupport_rank_generic F P hP hP0 i hi hL a j
end PfaffianDescent.ProjectiveNegativeTwist
