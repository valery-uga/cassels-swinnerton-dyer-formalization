import PfaffianDescent.SchemeAffineFunctions
import PfaffianDescent.CoordinateModuleSheafMaps
import Mathlib.AlgebraicGeometry.Restrict

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
section
variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]

/-- Affine coordinate functions of a morphism defined only on an open subscheme. -/
noncomputable def openAffineFunctionHom (U : X.Opens) (f : U.toScheme ⟶ Spec (.of R)) :
    R →+* Γ(X, U) := U.topIso.hom.hom.comp (affineFunctionHom f)

/-- Open-subscheme coordinates pull back by the ordinary map on sections. -/
lemma openAffineFunctionHom_resLE (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (g : U.toScheme ⟶ Spec (.of R)) :
    openAffineFunctionHom V (f.resLE U V e ≫ g) =
      (f.appLE U V e).hom.comp (openAffineFunctionHom U g) := by
  change (((Scheme.ΓSpecIso (.of R)).inv ≫ (f.resLE U V e ≫ g).appTop) ≫ V.topIso.hom).hom =
    ((((Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop) ≫ U.topIso.hom) ≫ f.appLE U V e).hom
  have hr : (f.resLE U V e).appTop = U.topIso.hom ≫ f.appLE U V e ≫ V.topIso.inv :=
    Scheme.Hom.resLE_app_top f e
  rw [Scheme.Hom.comp_appTop, hr]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma open_inclusion_appTop (U : X.Opens) :
    U.ι.appTop ≫ U.topIso.hom =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
  change X.presheaf.map (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op ≫
    X.presheaf.map (eqToHom U.ι_image_top.symm).op = _
  exact (X.presheaf.map_comp
    (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op
    (eqToHom U.ι_image_top.symm).op).symm

/-- Restricting a global affine morphism restricts its coordinate functions. -/
lemma openAffineFunctionHom_restrict (U : X.Opens) (f : X ⟶ Spec (.of R)) :
    openAffineFunctionHom U (U.ι ≫ f) = (regularFunctionRestrict X U).comp (affineFunctionHom f) := by
  change (((Scheme.ΓSpecIso (.of R)).inv ≫ (U.ι ≫ f).appTop) ≫ U.topIso.hom).hom =
    (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop) ≫
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom
  rw [Scheme.Hom.comp_appTop, Category.assoc, Category.assoc, open_inclusion_appTop]
  simp only [Category.assoc]

end
end PfaffianDescent
