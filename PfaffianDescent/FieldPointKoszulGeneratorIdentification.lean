import PfaffianDescent.CanonicalPointRestriction

/-!
# Identifying the normalized point generator

The actual field-point target isomorphism is the adjoint map associated to
its quotient-stalk coordinate. Thus a section is the normalized Koszul
generator precisely when its germ has coordinate one.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace PfaffianDescent

universe u

section

variable {L : Type u} [Field L] {X : Scheme.{u}}
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
      (sectionRepresenterPointKoszulQuotient X U (i default) hx q f))

set_option backward.isDefEq.respectTransparency false in
/-- The actual point-target isomorphism has the canonical adjoint map as
its forward morphism. -/
theorem fieldPointSectionRepresenterKoszulTargetIso_hom_eq_toSkyscraper :
    (fieldPointSectionRepresenterKoszulTargetIso i T V hV eV U hx q f qM).hom =
      schemeModuleToSkyscraper (i default) qM.hom := by
  change schemeModuleToSkyscraper (i default) (𝟙 _) ≫
    schemeModuleSkyscraperMap (i default) qM.hom = _
  rw [← schemeModuleToSkyscraper_comp, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- A section with quotient-stalk coordinate one is the actual normalized
Koszul generator. No choice of extension of that generator is involved. -/
theorem fieldPointSectionRepresenterKoszulSection_eq_of_germ_coordinate_one
    (s : (closedImmersionIdealTwistSequence i T).X₃.val.obj (op U))
    (hs : qM.hom ((closedImmersionIdealTwistSequence i T).X₃.presheaf.germ
      U (i default) hx s) = 1) :
    s = fieldPointSectionRepresenterKoszulSection i T V hV eV U hx q f qM := by
  let e := fieldPointSectionRepresenterKoszulTargetIso i T V hV eV U hx q f qM
  have himage : e.hom.val.app (op U) s =
      sectionRepresenterPointKoszulSection X U (i default) hx q f := by
    apply (schemeModuleSkyscraperAbPresheafAddEquivOfMem (i default)
      (ModuleCat.of (X.presheaf.stalk (i default))
        (sectionRepresenterPointKoszulQuotient X U (i default) hx q f)) U hx).injective
    rw [sectionRepresenterPointKoszulSection, AddEquiv.apply_symm_apply]
    change schemeModuleSkyscraperAbPresheafAddEquivOfMem (i default) _ U hx
      (e.hom.val.app (op U) s) = 1
    dsimp only [e]
    rw [fieldPointSectionRepresenterKoszulTargetIso_hom_eq_toSkyscraper]
    exact (schemeModuleSkyscraperAbPresheafAddEquivOfMem_toSkyscraper_app
      (i default) qM.hom U hx s).trans hs
  have h := congrArg (fun t ↦ e.inv.val.app (op U) t) himage
  change (e.hom ≫ e.inv).val.app (op U) s = _ at h
  rw [e.hom_inv_id] at h
  exact h

end

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- With the canonical unit-twist coordinate, the actual restriction of one
is the normalized field-point Koszul generator. -/
theorem closedFieldPointUnitTwistRestriction_one_eq_koszulSection
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    {J : Type u} (V : J → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (V j)).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (V j))))
    (U : X.Opens) (hx : i default ∈ U) (q f : Γ(X, U)) :
    letI := schemeModuleStalkModule (show X.Modules from
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
      (i default)
    ∀ (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap
        i (i default)) = Ideal.span
          ({X.presheaf.germ U (i default) hx q, X.presheaf.germ U (i default) hx f} : Set _)),
      closedImmersionUnitTwistRestrictionSection i U 1 =
        fieldPointSectionRepresenterKoszulSection i (SheafOfModules.unit X.ringCatSheaf)
          V hV eV U hx q f (closedImmersionUnitTwistStalkQuotientIso i (i default)
            (X.presheaf.germ U (i default) hx q) (X.presheaf.germ U (i default) hx f)
            hkernel) := by
  dsimp only
  letI := schemeModuleStalkModule (show X.Modules from
    (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (i default)
  intro hkernel
  apply fieldPointSectionRepresenterKoszulSection_eq_of_germ_coordinate_one
    i (SheafOfModules.unit X.ringCatSheaf) V hV eV U hx q f
  simpa only [map_one] using closedImmersionUnitTwistStalkQuotientIso_restriction_germ
    i U (i default) hx (X.presheaf.germ U (i default) hx q)
      (X.presheaf.germ U (i default) hx f) hkernel 1

end PfaffianDescent
