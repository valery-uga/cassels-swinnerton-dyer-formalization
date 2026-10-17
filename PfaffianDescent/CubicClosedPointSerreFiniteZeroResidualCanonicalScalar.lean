import PfaffianDescent.SerreExtensionFoundation
import PfaffianDescent.SchemeModuleGlobalSections

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_projection_zero_scalar_canonical
    {K : Type u} [Field K] {X : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of K)) (e : SerreExtensionData X N)
    (hconst : Function.Surjective (affineFunctionHom base))
    (s : SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))
    (hs : SheafOfModules.sectionsMap e.projection (e.E.unitHomEquiv s) =
      zeroSection N) :
    let z : SchemeModuleGlobalSectionsOver base (show X.Modules from e.E) := e.inclusion
    ∃ a : K, s = a • z := by
  dsimp only
  obtain ⟨u,hu,_⟩ := e.exists_unique_unit_section_of_projection_sections_eq_zero
    (e.E.unitHomEquiv s) hs
  let q := (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm u
  obtain ⟨a,ha⟩ := hconst (unitEndomorphismValue q)
  have hq : q = schemeModuleConstantEndomorphism base a := by
    rw [schemeModuleConstantEndomorphism, ha]
    exact (unitEndomorphismOfRegularFunction_value q).symm
  have hsu : q ≫ e.inclusion = s := by
    dsimp only [q]
    rw [(SheafOfModules.unit X.ringCatSheaf).unitHomEquiv_symm_comp,hu,Equiv.symm_apply_apply]
  exact ⟨a, by rw [← hsu,hq]; rfl⟩

end PfaffianDescent
