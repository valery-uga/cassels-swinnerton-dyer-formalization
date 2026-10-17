import PfaffianDescent.FieldPointSectionRepresenterKoszul
import PfaffianDescent.SectionRepresenterKoszulNaturality

/-! # Coefficient naturality of the actual point-supported Koszul class -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped nonZeroDivisors
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false in
/-- The actual point-class construction commutes with a coefficient
morphism; its exactness and epi inputs are proved inside the construction. -/
theorem fieldPointSectionRepresenterKoszulDegreeTwoClass_postcomp
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) {J : Type u} (V : J → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (V j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (V j))))
    (U : X.Opens) (hx : i default ∈ U) (q f : Γ(X, U))
    (qM : (schemeModuleStalkModuleFunctor X (i default)).obj
        (closedImmersionIdealTwistSequence i T).X₃ ≅
      ModuleCat.of (X.presheaf.stalk (i default))
        (sectionRepresenterPointKoszulQuotient
          X U (i default) hx q f))
    (hspan : ∀ (y : X) (hy : y ∈ U), y ≠ i default →
      Ideal.span
        ({X.presheaf.germ U y hy q, X.presheaf.germ U y hy f} :
          Set (X.presheaf.stalk y)) = ⊤)
    (hqreg : X.presheaf.germ U (i default) hx q ∈
      (X.presheaf.stalk (i default))⁰)
    (hfreg : Ideal.Quotient.mk
        (Ideal.span {X.presheaf.germ U (i default) hx q})
        (X.presheaf.germ U (i default) hx f) ∈
      ((X.presheaf.stalk (i default)) ⧸
        Ideal.span {X.presheaf.germ U (i default) hx q})⁰)
    [hExt : HasExt.{u} X.Modules] (Y Z : X.Modules)
    (y : Y.val.obj (op U)) (h : Y ⟶ Z) :
    (fieldPointSectionRepresenterKoszulDegreeTwoClass i T V hV eV U hx q f qM
      hspan hqreg hfreg Y y).comp (Ext.mk₀ h) (add_zero 2) =
    fieldPointSectionRepresenterKoszulDegreeTwoClass i T V hV eV U hx q f qM
      hspan hqreg hfreg Z (h.val.app (op U) y) := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  letI : Epi (sectionRepresenterKoszulAugmentation X.ringCatSheaf U
      (closedImmersionIdealTwistSequence i T).X₃
      (fieldPointSectionRepresenterKoszulSection i T V hV eV U hx q f qM)) :=
    fieldPointSectionRepresenterKoszul_augmentation_epi i T V hV eV U hx q f qM
  unfold fieldPointSectionRepresenterKoszulDegreeTwoClass
  apply @sectionRepresenterKoszulDegreeTwoClass_postcomp
    X.Opens _ _ X.ringCatSheaf _ _ hExt

end PfaffianDescent
