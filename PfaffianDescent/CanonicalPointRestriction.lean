import PfaffianDescent.CanonicalQuotientStalkCoordinate
import PfaffianDescent.FieldPointSectionRepresenterKoszul

/-!
# The canonical restriction section in the point quotient

The unit-twisted quotient is canonically an ordinary direct image. Its
restriction section is defined by the actual unit-to-direct-image morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace PfaffianDescent

universe u

set_option backward.isDefEq.respectTransparency false in
/-- Stalk maps act on section germs by the original section map. -/
theorem schemeModuleStalkModuleFunctor_map_germ
    {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (U : X.Opens) (x : X) (hx : x ∈ U) (s : M.val.obj (op U)) :
    (schemeModuleStalkModuleFunctor X x).map φ (M.presheaf.germ U x hx s) =
      N.presheaf.germ U x hx (φ.val.app (op U) s) := by
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom s

/-- Restriction to the closed subscheme, expressed in the unit-twisted target. -/
noncomputable def closedImmersionUnitTwistRestrictionSection
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) (r : Γ(X, U)) :
    (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃.val.obj
      (op U) :=
  (closedImmersionIdealTwistSequenceUnitTargetIso i).inv.val.app (op U)
    ((IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i).val.app (op U) r)

set_option backward.isDefEq.respectTransparency false in
/-- The germ of the actual untwisted restriction is the image of the ring germ. -/
theorem closedImmersionPushforwardStalkFromRingLinearMap_germ
    {X Z : Scheme.{u}} (i : Z ⟶ X) (U : X.Opens) (x : X) (hx : x ∈ U)
    (r : Γ(X, U)) :
    closedImmersionPushforwardStalkFromRingLinearMap i x (X.presheaf.germ U x hx r) =
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)).presheaf.germ
        U x hx ((IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i).val.app
          (op U) r) := by
  change schemeModuleStalkLinearMap
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) x
    (presheafOfModules_unitStalkAddEquiv X.presheaf x (X.presheaf.germ U x hx r)) = _
  rw [presheafOfModules_unitStalkAddEquiv_germ]
  exact schemeModuleStalkModuleFunctor_map_germ
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) U x hx r

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical point coordinate of a restriction section is its residue
class. This uses the actual restriction morphism, not a chosen generator. -/
theorem closedImmersionUnitTwistStalkQuotientIso_restriction_germ
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    letI := schemeModuleStalkModule (show X.Modules from
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) x
    ∀ (f g : X.presheaf.stalk x)
      (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        Ideal.span ({f, g} : Set (X.presheaf.stalk x))) (r : Γ(X, U)),
      (closedImmersionUnitTwistStalkQuotientIso i x f g hkernel).hom
        ((closedImmersionIdealTwistSequence i
          (SheafOfModules.unit X.ringCatSheaf)).X₃.presheaf.germ U x hx
            (closedImmersionUnitTwistRestrictionSection i U r)) =
        Ideal.Quotient.mk (Ideal.span ({f, g} : Set _)) (X.presheaf.germ U x hx r) := by
  dsimp only
  let M : X.Modules := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit Z.ringCatSheaf)
  letI := schemeModuleStalkModule M x
  intro f g hkernel r
  let e := closedImmersionIdealTwistSequenceUnitTargetIso i
  have hcancel : e.hom.val.app (op U)
      (closedImmersionUnitTwistRestrictionSection i U r) =
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i).val.app (op U) r := by
    change (e.inv ≫ e.hom).val.app (op U) _ = _
    rw [e.inv_hom_id]
    rfl
  change (closedImmersionPushforwardStalkQuotientLinearEquivOfKernelEq
    i x f g hkernel).symm
      ((schemeModuleStalkModuleFunctor X x).map e.hom
        ((closedImmersionIdealTwistSequence i
          (SheafOfModules.unit X.ringCatSheaf)).X₃.presheaf.germ U x hx _)) = _
  rw [schemeModuleStalkModuleFunctor_map_germ, hcancel,
    ← closedImmersionPushforwardStalkFromRingLinearMap_germ]
  exact closedImmersionPushforwardStalkQuotientLinearEquivOfKernelEq_symm_apply
    i x f g hkernel _

end PfaffianDescent
