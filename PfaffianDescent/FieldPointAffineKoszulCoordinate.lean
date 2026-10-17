import PfaffianDescent.FieldPointSectionRepresenterKoszul
import PfaffianDescent.FieldPointKoszulLocalization
import PfaffianDescent.FieldPointTwistQuotient
import PfaffianDescent.FieldPointExtCoordinate

/-!
# Field-point Ext coordinates from the affine Koszul resolution

This combines the independently constructed global point class with the
local complete-intersection residue coordinate. The nonzero-class input to
the abstract coordinate constructor is proved here, rather than assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open scoped nonZeroDivisors

namespace PfaffianDescent

universe u

set_option backward.isDefEq.respectTransparency false in
/-- The actual affine point resolution supplies the nonzero class needed
for the local field-valued Ext coordinate. Localization injectivity is
proved from the affine resolution, and the twisted quotient stalk is
constructed from the local twist trivialization and parameter span. -/
noncomputable def fieldPointExtTwoCoordinateAddEquivOfAffineKoszulResolution
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) {J : Type u} (V : J → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (V j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (V j))))
    (U : X.Opens) (hU : IsAffineOpen U)
    [IsNoetherianRing Γ((U : Scheme), ⊤)] (hx : i default ∈ U) (q f : Γ(X, U))
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
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U)))
    [hExt : HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i default)))]
    (hmax : Ideal.span
        ({X.presheaf.germ U (i default) hx q,
          X.presheaf.germ U (i default) hx f} : Set _) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i default))) :
    Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2 ≃+ L := by
  let qM := fieldPointPushforwardTwistStalkQuotientIsoOfLocalTrivialization
    i default T U hx eT
    (X.presheaf.germ U (i default) hx q)
    (X.presheaf.germ U (i default) hx f) hmax
  have hqmax : X.presheaf.germ U (i default) hx q ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i default)) := by
    rw [← hmax]
    exact Ideal.subset_span (by simp)
  have hfmax : X.presheaf.germ U (i default) hx f ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i default)) := by
    rw [← hmax]
    exact Ideal.subset_span (by simp)
  let z := fieldPointSectionRepresenterKoszulDegreeTwoClass
    i T V hV eV U hx q f qM hspan hqreg hfreg
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) (1 : Γ(X, U))
  have hz : z ≠ 0 :=
    fieldPointSectionRepresenterKoszulUnitClass_ne_zero_of_affineOpen
      i T V hV eV U hU hx q f qM hspan hqreg hfreg hqmax hfmax
  let hstalk := fieldPointKoszulUnit_stalkExtTwo_injective
    i T V hV eV U hU hx q f qM hspan hqreg hfreg
  exact fieldPointExtTwoCoordinateAddEquivOfLocalTrivialization
    i default T U hx eT
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
    (X.presheaf.germ U (i default) hx q)
    (X.presheaf.germ U (i default) hx f) hqreg hfreg hqmax hfmax
    qM (schemeModuleUnitStalkIso X (i default)) hmax hstalk z hz

end PfaffianDescent
