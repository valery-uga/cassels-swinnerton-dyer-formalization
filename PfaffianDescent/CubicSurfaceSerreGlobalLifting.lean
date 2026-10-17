import PfaffianDescent.VoisinCubicSurfaceSerre
import PfaffianDescent.SchemeModuleGlobalSections

/-! Native cubic-surface cohomology lifts every actual quotient section of
a Serre extension. No lifting or evaluation certificate is an input. -/

noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory
open CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicSurfaceSerre_projection_globalSections_surjective
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    [HasExt.{u} (hypersurface p hp).Modules]
    {Q : (hypersurface p hp).Modules}
    (e : SerreExtensionSequenceData (hypersurface p hp) Q) :
    Function.Surjective
      (schemeModuleGlobalSectionsMap (hypersurfaceToBase p hp) e.projection) := by
  letI : HasExt.{u} (SheafOfModules.{u} (hypersurface p hp).ringCatSheaf) :=
    ‹HasExt.{u} (hypersurface p hp).Modules›
  letI : Subsingleton (Ext.{u}
      (C := SheafOfModules.{u} (hypersurface p hp).ringCatSheaf)
      (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)
      (SheafOfModules.unit (hypersurface p hp).ringCatSheaf) 1) :=
    cubicSurface_structure_ext_one_subsingleton_of_smooth K p hp hp0
  intro t
  obtain ⟨s, hs⟩ := e.projection_sections_surjective_of_ext_one_subsingleton
    (Q.unitHomEquiv t)
  refine ⟨e.E.unitHomEquiv.symm s, ?_⟩
  apply Q.unitHomEquiv.injective
  change Q.unitHomEquiv (e.E.unitHomEquiv.symm s ≫ e.projection) = Q.unitHomEquiv t
  rw [e.E.unitHomEquiv_comp_apply, e.E.unitHomEquiv.apply_symm_apply]
  exact hs

end PfaffianDescent.ProjectiveNegativeTwist
