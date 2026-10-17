import PfaffianDescent.SchemeModuleLocalIsoGerm
import PfaffianDescent.FieldPointKoszulLocalization
import PfaffianDescent.FieldPointTwistQuotient

/-! # Actual field-point Ext coordinates with a locally trivial coefficient target -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open scoped nonZeroDivisors
namespace PfaffianDescent
universe u

set_option backward.isDefEq.respectTransparency false in
/-- Localization of the actual point Ext group is injective for any coefficient
module trivialized on the affine Koszul chart. -/
theorem fieldPointKoszul_stalkExtTwo_injective_of_localTargetTrivialization
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) {J : Type u} (V : J → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (V j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (V j))))
    (U : X.Opens) (hU : IsAffineOpen U)
    [IsNoetherianRing Γ((U : Scheme), ⊤)] (hx : i default ∈ U) (q f : Γ(X, U))
    (qM : (schemeModuleStalkModuleFunctor X (i default)).obj
        (closedImmersionIdealTwistSequence i T).X₃ ≅
      ModuleCat.of (X.presheaf.stalk (i default))
        (sectionRepresenterPointKoszulQuotient
          X U (i default) hx q f))
    (hspan : ∀ (z : X) (hz : z ∈ U), z ≠ i default →
      Ideal.span
        ({X.presheaf.germ U z hz q, X.presheaf.germ U z hz f} :
          Set (X.presheaf.stalk z)) = ⊤)
    (hqreg : X.presheaf.germ U (i default) hx q ∈
      (X.presheaf.stalk (i default))⁰)
    (hfreg : Ideal.Quotient.mk
        (Ideal.span {X.presheaf.germ U (i default) hx q})
        (X.presheaf.germ U (i default) hx f) ∈
      ((X.presheaf.stalk (i default)) ⧸
        Ideal.span {X.presheaf.germ U (i default) hx q})⁰)
    (Y : X.Modules)
    (eY : Y.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf)
    [hExt : HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i default)))] :
    Function.Injective (schemeModuleStalkModuleExtMap X (i default)
      (closedImmersionIdealTwistSequence i T).X₃
      Y 2) := by
  let x : U := ⟨i default, hx⟩
  let qY := schemeModuleLocalUnitStalkIso U x Y eY
  let coord := schemeModuleLocalUnitSectionAddEquiv U Y eY
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨y, rfl⟩ :=
    fieldPointSectionRepresenterKoszulDegreeTwoClass_surjective_of_affineOpen
      i T V hV eV U hU hx q f qM hspan hqreg hfreg Y eY z
  have hpoint :=
    fieldPointSectionRepresenterKoszulDegreeTwoClass_stalk_zero_coordinate_mem_span
      i T V hV eV U hx q f qM hspan hqreg hfreg Y y qY hz
  have hgerm : schemeModuleSectionStalkCoordinateAddHom U (i default) hx Y qY y =
      X.presheaf.germ U (i default) hx (coord y) :=
    schemeModuleLocalUnitStalkCoordinate_germ U x Y eY y
  rw [hgerm] at hpoint
  have hy : coord y ∈ Ideal.span ({q, f} : Set Γ(X, U)) := by
    apply hU.mem_ideal_iff.mpr
    intro w hw
    rw [Ideal.map_span, Set.image_pair]
    by_cases hwpoint : w = i default
    · subst w
      exact hpoint
    · rw [hspan w hw hwpoint]
      trivial
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hy
  apply (fieldPointSectionRepresenterKoszulDegreeTwoClass_eq_zero_iff_of_affineOpen
    i T V hV eV U hU hx q f qM hspan hqreg hfreg Y eY y).mpr
  refine ⟨coord.symm (-b), coord.symm a, ?_⟩
  apply coord.injective
  have hsmul (r : Γ(X, U)) (t : Γ(Y, U)) : coord (r • t) = r * coord t :=
    schemeModuleLocalUnitSectionAddEquiv_smul U Y eY r t
  rw [map_add, hsmul, hsmul,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  calc
    (-f) * (-b) + q * a = a * q + b * f := by ring
    _ = coord y := hab

end PfaffianDescent
