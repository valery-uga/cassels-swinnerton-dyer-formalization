import PfaffianDescent.BundleSectionZeroLocus
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Actual section vanishing and affine zero-scheme factorization

The vanishing hypothesis is the zero map obtained by the actual scheme-module
pullback functor.  Scalar coordinates, their annihilation, and the closed
immersion factorization are derived from that map.+-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_coordinate_annihilated
    {X Z : Scheme.{u}} (j : Z ⟶ X) {E : X.Modules} (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (s : E.sections)
    (hs : (Scheme.Modules.pullback j).map (E.unitHomEquiv.symm s) = 0)
    (a : I) : j.appTop (sectionCoordinateOfFreeIso I t s a) = 0 := by
  let F := Scheme.Modules.pullback j
  let A := Scheme.Modules.pullbackPushforwardAdjunction j
  let c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf :=
    E.unitHomEquiv.symm s ≫ t.inv ≫ freeCoordinateMap I a
  have hc : F.map c = 0 := by
    dsimp only [c, F]
    simp only [Functor.map_comp, hs, zero_comp]
  have hp : A.homEquiv _ _ (pullbackUnitComparison j) =
      SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom := by
    letI : (SheafOfModules.pushforward j.toRingCatSheafHom).IsRightAdjoint :=
      (Scheme.Modules.pullbackPushforwardAdjunction j).isRightAdjoint
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hz : c ≫ SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom = 0 := by
    rw [← hp, ← A.homEquiv_naturality_left c (pullbackUnitComparison j), hc]
    change A.unit.app _ ≫ (Scheme.Modules.pushforward j).map (0 ≫ _) = 0
    simp only [zero_comp, Functor.map_zero, comp_zero]
  have hval := congrArg (fun f => (f.val.app (Opposite.op ⊤)) (1 : Γ(X, ⊤))) hz
  change j.appTop (unitEndomorphismValue c) = 0 at hval
  convert hval using 1
  unfold sectionCoordinateOfFreeIso freeSectionCoordinate unitEndomorphismValue
  rw [← SheafOfModules.unitHomEquiv_symm_comp]
  rfl

theorem cubicClosedPointSerreFiniteZeroResidual_affine_zeroIdeal_le_kernel
    {X Z : Scheme.{u}} [IsAffine X] (j : Z ⟶ X) [QuasiCompact j]
    {E : X.Modules} (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (s : E.sections)
    (hs : (Scheme.Modules.pullback j).map (E.unitHomEquiv.symm s) = 0) :
    sectionZeroIdealOfFreeIso I t s ≤ j.ker := by
  apply Scheme.IdealSheafData.le_of_isAffine
  rw [sectionZeroIdealOfFreeIso, freeSectionZeroIdeal,
    Scheme.IdealSheafData.ofIdealTop_ideal, Scheme.Hom.ker_apply]
  simp only [homOfLE_refl, op_id]
  erw [X.presheaf.map_id]
  simp only [CommRingCat.hom_id, Ideal.map_id]
  apply Ideal.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact cubicClosedPointSerreFiniteZeroResidual_coordinate_annihilated j I t s hs a

def cubicClosedPointSerreFiniteZeroResidual_affine_zeroLift
    {X Z : Scheme.{u}} [IsAffine X] (j : Z ⟶ X) [QuasiCompact j]
    {E : X.Modules} (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (s : E.sections)
    (hs : (Scheme.Modules.pullback j).map (E.unitHomEquiv.symm s) = 0) :
    Z ⟶ sectionZeroSubschemeOfFreeIso I t s := by
  letI := isClosedImmersion_sectionZeroSubschemeOfFreeIsoι I t s
  apply IsClosedImmersion.lift (sectionZeroSubschemeOfFreeIsoι I t s) j
  simpa only [sectionZeroSubschemeOfFreeIsoι, Scheme.IdealSheafData.ker_subschemeι] using
    cubicClosedPointSerreFiniteZeroResidual_affine_zeroIdeal_le_kernel j I t s hs

@[reassoc]
theorem cubicClosedPointSerreFiniteZeroResidual_affine_zeroLift_comp
    {X Z : Scheme.{u}} [IsAffine X] (j : Z ⟶ X) [QuasiCompact j]
    {E : X.Modules} (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (s : E.sections)
    (hs : (Scheme.Modules.pullback j).map (E.unitHomEquiv.symm s) = 0) :
    cubicClosedPointSerreFiniteZeroResidual_affine_zeroLift j I t s hs ≫
      sectionZeroSubschemeOfFreeIsoι I t s = j := by
  letI := isClosedImmersion_sectionZeroSubschemeOfFreeIsoι I t s
  unfold cubicClosedPointSerreFiniteZeroResidual_affine_zeroLift
  exact IsClosedImmersion.lift_fac _ _ _

end PfaffianDescent
