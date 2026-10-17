import PfaffianDescent.FieldPointExtCoordinate
import PfaffianDescent.BundleSectionZeroLocus

/-! The internally derived213 frame unit gives an actual whole quotient
sheaf automorphism. Its native map is the SAME scalar action used there. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- Genuine residue-field multiplication, conjugated by the SAME original
whole global quotient Iso. Unit invertibility is derived natively. -/
def actualWholePointFrameUnitIso217
    {X : Scheme.{u}} {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ X) (Q : X.Modules)
    (E : Q ≅ (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (theta : L) (hTheta : IsUnit theta) : Q ≅ Q := by
  let c := schemeModuleConstantEndomorphism (𝟙 (Spec (.of L))) theta
  letI : IsIso c := by
    change IsIso (BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
      (affineFunctionHom (𝟙 (Spec (.of L))) theta))
    exact BundleSectionZeroLocus.isIso_unitEndomorphismOfRegularFunction_of_isUnit _
      (hTheta.map (affineFunctionHom (𝟙 (Spec (.of L)))))
  exact E ≪≫ (Scheme.Modules.pushforward i).mapIso (asIso c) ≪≫ E.symm

lemma actualWholePointFrameUnitIso_hom217
    {X : Scheme.{u}} {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ X) (Q : X.Modules)
    (E : Q ≅ (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (theta : L) (hTheta : IsUnit theta) :
    (actualWholePointFrameUnitIso217 i Q E theta hTheta).hom =
      E.hom ≫ fieldPointPushforwardScalarEndomorphismAddHom i theta ≫ E.inv := rfl

end PfaffianDescent
