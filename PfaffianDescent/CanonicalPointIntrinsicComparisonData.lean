import PfaffianDescent.CanonicalPointIntrinsicPullback
import PfaffianDescent.PointSkyscraperSectionUniqueness
import PfaffianDescent.FieldPointKoszulCechPullback
import PfaffianDescent.SectionRepresenterCanonicalRestriction

/-!
# Canonical intrinsic point pullback with its actual comparison maps

The point Koszul class is pulled back along the actual restriction of one,
using the canonical quotient-stalk coordinate. Its representative on the
actual point-adapted cover is supplied by the checked chain comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped nonZeroDivisors

namespace PfaffianDescent

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

universe u

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
theorem exists_closedFieldPointCanonicalRestriction_intrinsic_comparison_data
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [hExt : HasExt.{u} X.Modules]
    {J : Type u} (V : J → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (V j)).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (V j))))
    (U : X.Opens) (hU : IsAffineOpen U) (hx : i default ∈ U) (q f : Γ(X, U))
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ i default →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤)
    (hqreg : X.presheaf.germ U (i default) hx q ∈ (X.presheaf.stalk (i default))⁰)
    (hfreg : Ideal.Quotient.mk (Ideal.span {X.presheaf.germ U (i default) hx q})
        (X.presheaf.germ U (i default) hx f) ∈
      ((X.presheaf.stalk (i default)) ⧸ Ideal.span {X.presheaf.germ U (i default) hx q})⁰)
    (Y : X.Modules) (y : Y.val.obj (op U)) :
    letI := schemeModuleStalkModule (show X.Modules from
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
      (i default)
    ∀ (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap
        i (i default)) = Ideal.span
          ({X.presheaf.germ U (i default) hx q, X.presheaf.germ U (i default) hx f} : Set _)),
    let qM := closedImmersionUnitTwistStalkQuotientIso i (i default)
      (X.presheaf.germ U (i default) hx q) (X.presheaf.germ U (i default) hx f) hkernel
    ∃ (a₁ : (sectionRepresenterCechChain X.ringCatSheaf
        (PointAdaptedAffineCover.opens U (i default))).X 1 ⟶
          ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U)
      (a₂ : (sectionRepresenterCechChain X.ringCatSheaf
        (PointAdaptedAffineCover.opens U (i default))).X 2 ⟶ sectionRepresenter X.ringCatSheaf U)
      (z : DegreeTwoCocycle ((sectionRepresenterCechChain X.ringCatSheaf
        (PointAdaptedAffineCover.opens U (i default))).d 3 2) (Y := Y)),
      a₁ ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f =
        (sectionRepresenterCechChain X.ringCatSheaf (PointAdaptedAffineCover.opens U (i default))).d 1 0 ≫
          PointAdaptedAffineCover.onC₀ U (i default) ∧
      a₂ ≫ sectionRepresenterKoszulFirst X.ringCatSheaf U q f =
        (sectionRepresenterCechChain X.ringCatSheaf (PointAdaptedAffineCover.opens U (i default))).d 2 1 ≫ a₁ ∧
      (sectionRepresenterCechChain X.ringCatSheaf (PointAdaptedAffineCover.opens U (i default))).d 3 2 ≫ a₂ = 0 ∧
      z.1 = a₂ ≫ sectionRepresenterAugmentation X.ringCatSheaf U Y y ∧
      (Ext.mk₀ (C := X.Modules)
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
          (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)).comp
        (fieldPointSectionRepresenterKoszulDegreeTwoClass i (SheafOfModules.unit X.ringCatSheaf)
          V hV eV U hx q f qM haway hqreg hfreg Y y) (zero_add 2) =
        schemeCoverDegreeTwoToCohomology (PointAdaptedAffineCover.opens U (i default))
          (PointAdaptedAffineCover.coversTop U (i default) hx (fieldPoint_image_isClosed i)) Y z := by
  dsimp only
  letI := schemeModuleStalkModule (show X.Modules from
    (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (i default)
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  intro hkernel
  let qM := closedImmersionUnitTwistStalkQuotientIso i (i default)
    (X.presheaf.germ U (i default) hx q) (X.presheaf.germ U (i default) hx f) hkernel
  obtain ⟨s, a₁, a₂, z, hs, h₁, h₂, h₃, hz, hext⟩ :=
    exists_fieldPointUnitKoszul_cech_pullback i V hV eV U hU hx q f qM
      haway hqreg hfreg Y y
  have hcanonical := (closedFieldPointUnitTwistRestriction_one_augmentation_square
    i V hV eV U hx q f hkernel).1
  have heq : s = closedImmersionUnitTwistRestrictionSection i ⊤ 1 := by
    apply schemeModule_restriction_from_top_injective_of_skyscraperIso (i default) _
      (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃
      (fieldPointPushforwardTwist_skyscraperIso_of_coversTop_iso_unit i
        (SheafOfModules.unit X.ringCatSheaf) V hV eV) U hx
    exact hs.trans hcanonical.symm
  rw [heq, sectionRepresenterAugmentation_top_canonicalRestriction] at hext
  let W := PointAdaptedAffineCover.opens U (i default)
  let e := schemeCoverCechTargetIsoUnit W
  have h := congrArg (fun t ↦ (Ext.mk₀ (C := X.Modules) e.inv).comp t (zero_add 2)) hext
  rw [Ext.mk₀_comp_mk₀_assoc] at h
  have hc : e.inv ≫
      ((sectionRepresenterCechTargetIsoTerminal X.ringCatSheaf W ⊤ isTerminalTop).hom ≫
        (sectionRepresenterTopIsoUnit X).hom ≫
          IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
            (closedImmersionIdealTwistSequenceUnitTargetIso i).inv) =
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
        (closedImmersionIdealTwistSequenceUnitTargetIso i).inv := by
    simp only [e, schemeCoverCechTargetIsoUnit, Iso.trans_inv, Category.assoc,
      Iso.inv_hom_id_assoc]
  rw [hc] at h
  exact ⟨a₁, a₂, z, h₁, h₂, h₃, hz, h⟩

end PfaffianDescent
