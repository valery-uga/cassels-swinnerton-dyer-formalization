import PfaffianDescent.CanonicalFieldPointCechPullback
import PfaffianDescent.SchemeCoverIntrinsicCohomology
import PfaffianDescent.PointAdaptedCechExt

/-!
# Canonical point pullback as an intrinsic cohomology class

The formal Cech augmentation source is removed using its actual canonical
isomorphism with the structure sheaf. The resulting equality is in the
intrinsic degree-two cohomology used by cubic-surface duality.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped nonZeroDivisors

namespace PfaffianDescent

universe u

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
theorem exists_closedFieldPointCanonicalRestriction_intrinsic_pullback
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
  obtain ⟨z, hz⟩ := exists_closedFieldPointCanonicalRestriction_cech_pullback
    i V hV eV U hU hx q f haway hqreg hfreg Y y hkernel
  let W := PointAdaptedAffineCover.opens U (i default)
  let e := schemeCoverCechTargetIsoUnit W
  have h := congrArg (fun t ↦ (Ext.mk₀ (C := X.Modules) e.inv).comp t (zero_add 2)) hz
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
  exact ⟨z, h⟩

end PfaffianDescent
