import PfaffianDescent.FieldPointExtCoordinate
import PfaffianDescent.SchemeModuleSupportedFiberGroundDimension

/-! SOURCE ONLY203. True point-pushforward translations supply actual
whole-quotient sections and their literal Yoneda boundary identities. Original
base linearity is inherited from actual sheaf maps, not defined through an Iso. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual residue translates give honest sections of the WHOLE original Q.
The original field-point scalar endomorphism acts on the actual pushforward. -/
def actualPointWholeQuotientTranslatedSection203
    {X : Scheme.{u}} {L : Type u} [Field L] (i : Spec (.of L) ⟶ X)
    (Q : X.Modules)
    (E : Q ≅ (Scheme.Modules.pushforward i).obj
      (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (a : L) : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ Q :=
  closedImmersionUnitToPushforwardUnit i ≫
    fieldPointPushforwardScalarEndomorphismAddHom i a ≫ E.inv

/-- The actual section boundary is EXACTLY the original residue translate
of the actual supported class obtained from the WHOLE quotient identification.
This is map associativity, never a desired trace/nonzero comparison premise. -/
theorem actualPointWholeQuotientTranslatedSection_boundary203
    {X : Scheme.{u}} {L : Type u} [Field L] (i : Spec (.of L) ⟶ X)
    [HasExt.{u} X.Modules] (Q N : X.Modules) (n : ℕ)
    (E : Q ≅ (Scheme.Modules.pushforward i).obj
      (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (a : L) (z : Ext.{u} (C := X.Modules) Q N n) :
    (Ext.mk₀.{u} (C := X.Modules) (actualPointWholeQuotientTranslatedSection203 i Q E a)).comp z
      (zero_add n) =
      (Ext.mk₀.{u} (C := X.Modules) (closedImmersionUnitToPushforwardUnit i)).comp
        ((Ext.mk₀.{u} (C := X.Modules) (fieldPointPushforwardScalarEndomorphismAddHom i a)).comp
          ((Ext.mk₀.{u} (C := X.Modules) E.inv).comp z (zero_add n)) (zero_add n))
        (zero_add n) := by
  unfold actualPointWholeQuotientTranslatedSection203
  symm
  calc
    _ = (Ext.mk₀.{u} (C := X.Modules)
        (closedImmersionUnitToPushforwardUnit i ≫ fieldPointPushforwardScalarEndomorphismAddHom i a)).comp
          ((Ext.mk₀.{u} (C := X.Modules) E.inv).comp z (zero_add n)) (zero_add n) :=
      Ext.mk₀_comp_mk₀_assoc _ _ _
    _ = (Ext.mk₀.{u} (C := X.Modules)
        ((closedImmersionUnitToPushforwardUnit i ≫ fieldPointPushforwardScalarEndomorphismAddHom i a) ≫ E.inv)).comp
          z (zero_add n) := Ext.mk₀_comp_mk₀_assoc _ _ _
    _ = _ := by rw [Category.assoc]

/-- The WHOLE actual quotient's top sections are equivalent to the original
residue field, linearly for the independently original-pi/pointAlgebra actions.
The geometric factory above supplies E without a caller support certificate. -/
def actualClosedPointWholeQuotientTopGroundLinearEquiv203
    {K : Type u} [Field K] {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (.of K)) (P : closedPoints X) (Q : X.Modules)
    (E : Q ≅ (Scheme.Modules.pushforward (X.fromSpecResidueField P.1)).obj
      (show (Spec (X.residueField P.1)).Modules from
        SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf)) :
    letI := AllCharacteristics.pointAlgebra pi P.1
    SchemeModuleOpenSectionsOver pi Q ⊤ ≃ₗ[K] X.residueField P.1 := by
  letI := AllCharacteristics.pointAlgebra pi P.1
  let i := X.fromSpecResidueField P.1
  exact (Coray.schemeModuleOpenTopIsoLinearEquivOver pi E).trans
    ((Coray.schemeModulePushforward_topSectionsLinearEquiv pi i
      (SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf)).trans
      (Coray.schemeModuleFieldSpecUnitTopLinearEquiv (i ≫ pi)))

end PfaffianDescent
