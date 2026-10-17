import PfaffianDescent.CubicClosedPointSerreLocalKoszulRepresenter
import PfaffianDescent.CubicClosedPointSerreLocalKoszulKernel
import PfaffianDescent.FieldPointUnitQuotientMaximalIdeal
import PfaffianDescent.SheafModulePushforwardExact

/-! # The actual point restriction is the affine Koszul augmentation

The unit-twist point coordinate and the actual restriction of one identify
the augmented Koszul map with the original unit-to-point map. This supplies
the exact row ending at the actual ideal kernel.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

def cubicClosedPointSerreLocalKoszulUnitSequence
    {X : Scheme.{u}} {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ShortComplex X.Modules :=
  ShortComplex.mk (IdealSheafDataModule.closedImmersionModuleToUnit i)
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
      (closedImmersionIdealTwistSequenceUnitTargetIso i).inv) (by
    have hz := (IdealSheafDataModule.closedImmersionModulePushforwardSequence i).zero
    change IdealSheafDataModule.closedImmersionModuleToUnit i ≫
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i = 0 at hz
    rw [← Category.assoc, hz, zero_comp])

theorem cubicClosedPointSerreLocalKoszulUnitSequence_shortExact
    {X : Scheme.{u}} {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (cubicClosedPointSerreLocalKoszulUnitSequence i).ShortExact := by
  let b : IdealSheafDataModule.closedImmersionModulePushforwardSequence i ≅
      cubicClosedPointSerreLocalKoszulUnitSequence i :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (closedImmersionIdealTwistSequenceUnitTargetIso i).symm
      (by simp [cubicClosedPointSerreLocalKoszulUnitSequence,
        IdealSheafDataModule.closedImmersionModulePushforwardSequence])
      (by simp [cubicClosedPointSerreLocalKoszulUnitSequence,
        IdealSheafDataModule.closedImmersionModulePushforwardSequence])
  exact ShortComplex.shortExact_of_iso b
    (IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i)

theorem cubicClosedPointSerreLocalKoszulAugmentation_unit_comp
    {X : Scheme.{u}} (U : X.Opens) {M : X.Modules}
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    cubicClosedPointSerreLocalKoszulRepresenterUnitMap U ≫ a =
      sectionRepresenterAugmentation X.ringCatSheaf U M
        (a.val.app (op U) (1 : Γ(X, U))) := by
  apply (sectionRepresenterHomEquiv X.ringCatSheaf U M).injective
  rw [sectionRepresenterHomEquiv_postcomp,
    cubicClosedPointSerreLocalKoszulRepresenterUnitMap,
    sectionRepresenterHomEquiv_augmentation, sectionRepresenterHomEquiv_augmentation]

theorem cubicClosedPointSerreLocalKoszulAugmentation_eq
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    {J : Type u} (V : J → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (V j)).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (V j))))
    (U : X.Opens) (hx : i default ∈ U) (q f : Γ(X, U))
    (hmax : Ideal.span ({X.presheaf.germ U (i default) hx q,
      X.presheaf.germ U (i default) hx f} : Set _) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i default))) :
    letI := schemeModuleStalkModule (show X.Modules from
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
      (i default)
    let hk := (closedFieldPoint_pushforwardStalkFromRingLinearMap_ker_eq_maximalIdeal
      i default).trans hmax.symm
    let qM := closedImmersionUnitTwistStalkQuotientIso i (i default)
      (X.presheaf.germ U (i default) hx q) (X.presheaf.germ U (i default) hx f) hk
    cubicClosedPointSerreLocalKoszulRepresenterUnitMap U ≫
      (cubicClosedPointSerreLocalKoszulUnitSequence i).g =
      sectionRepresenterKoszulAugmentation X.ringCatSheaf U
        (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃
        (fieldPointSectionRepresenterKoszulSection i (SheafOfModules.unit X.ringCatSheaf)
          V hV eV U hx q f qM) := by
  dsimp only
  letI := schemeModuleStalkModule (show X.Modules from
    (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (i default)
  let hk := (closedFieldPoint_pushforwardStalkFromRingLinearMap_ker_eq_maximalIdeal
    i default).trans hmax.symm
  rw [cubicClosedPointSerreLocalKoszulAugmentation_unit_comp]
  change sectionRepresenterAugmentation X.ringCatSheaf U _
    (closedImmersionUnitTwistRestrictionSection i U 1) = _
  rw [closedFieldPointUnitTwistRestriction_one_eq_koszulSection i V hV eV U hx q f hk]
  rfl

end PfaffianDescent
