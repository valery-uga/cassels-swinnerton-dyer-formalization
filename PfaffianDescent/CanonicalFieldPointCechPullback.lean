import PfaffianDescent.CanonicalPointKoszulAugmentation
import PfaffianDescent.PointSkyscraperSectionUniqueness
import PfaffianDescent.FieldPointKoszulCechPullback
import PfaffianDescent.SectionRepresenterCanonicalRestriction

/-!
# Pullback of the point class along canonical restriction

The point Koszul class is pulled back along the actual restriction of one,
using the canonical quotient-stalk coordinate. Its representative on the
actual point-adapted cover is supplied by the checked chain comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped nonZeroDivisors

namespace PfaffianDescent

universe u

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
theorem exists_closedFieldPointCanonicalRestriction_cech_pullback
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
    ∃ z : DegreeTwoCocycle ((sectionRepresenterCechChain X.ringCatSheaf
        (PointAdaptedAffineCover.opens U (i default))).d 3 2) (Y := Y),
      (Ext.mk₀ (C := X.Modules)
        ((sectionRepresenterCechTargetIsoTerminal X.ringCatSheaf
          (PointAdaptedAffineCover.opens U (i default)) ⊤ isTerminalTop).hom ≫
            (sectionRepresenterTopIsoUnit X).hom ≫
              IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
                (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)).comp
        (fieldPointSectionRepresenterKoszulDegreeTwoClass i (SheafOfModules.unit X.ringCatSheaf)
          V hV eV U hx q f qM haway hqreg hfreg Y y) (zero_add 2) =
        PointAdaptedAffineCover.degreeTwoToExt U (i default) hx (fieldPoint_image_isClosed i) Y z := by
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
  exact ⟨z, hext⟩

end PfaffianDescent
