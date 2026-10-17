import PfaffianDescent.SchemeModuleGlobalSections
import PfaffianDescent.AffineQuotientPushforwardTilde

/- SOURCE ONLY / UNVERIFIED. The coefficient is derived from the ACTUAL
unit automorphism, not supplied as a comparison certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory BundleSectionZeroLocus
universe u

def actualFieldUnitAutomorphismScalar
    {L : Type u} [Field L]
    (a : SheafOfModules.unit (Spec (.of L)).ringCatSheaf ⟶
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf) : L :=
  (Scheme.ΓSpecIso (.of L)).hom (unitEndomorphismValue a)

theorem actualFieldUnitAutomorphismScalar_ne_zero
    {L : Type u} [Field L]
    (a : SheafOfModules.unit (Spec (.of L)).ringCatSheaf ⟶
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf) [IsIso a] :
    actualFieldUnitAutomorphismScalar a ≠ 0 := by
  exact ((isUnit_unitEndomorphismValue_of_isIso a).map
    (Scheme.ΓSpecIso (.of L)).hom.hom).ne_zero

theorem actualFieldUnitAutomorphism_eq_constant
    {L : Type u} [Field L]
    (a : SheafOfModules.unit (Spec (.of L)).ringCatSheaf ⟶
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf) :
    a = schemeModuleConstantEndomorphism (𝟙 (Spec (.of L)))
      (actualFieldUnitAutomorphismScalar a) := by
  have h : affineFunctionHom (𝟙 (Spec (.of L)))
      (actualFieldUnitAutomorphismScalar a) = unitEndomorphismValue a := by
    simp only [affineFunctionHom, Scheme.Hom.id_appTop, Category.comp_id,
      actualFieldUnitAutomorphismScalar]
    exact Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of L)) _
  rw [schemeModuleConstantEndomorphism, h]
  exact (unitEndomorphismOfRegularFunction_value a).symm

end PfaffianDescent
