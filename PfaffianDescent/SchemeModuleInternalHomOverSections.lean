import PfaffianDescent.SchemeModuleInternalHomSheaf

/-! Actual sections of the constructed internal Hom are ACTUAL module
sheaf morphisms on the corresponding over-site. Both directions enforce
the original local scalar laws. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} (M N : X.Modules)

/-- The ACTUAL additive presheaf underlying open-site restriction. Its
values and maps retain the original module restriction functions. -/
theorem over_presheaf (U : X.Opens) :
    (M.over U).val.presheaf = (Over.forget U).op ⋙ M.presheaf := rfl

/-- Actual internal Hom sections coincide with genuine O-linear module
sheaf maps over U. Linearity is proved in both directions, never supplied
as a section-comparison condition. -/
def sectionsEquivOver (U : X.Opens) :
    (sheaf M N).val.obj (op U) ≃ (M.over U ⟶ N.over U) where
  toFun a :=
    { val := PresheafOfModules.homMk
        (show (M.over U).val.presheaf ⟶ (N.over U).val.presheaf from a.1)
        (fun V r m => a.2 V.unop r m) }
  invFun f :=
    ⟨(PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map f.val,
      fun V r m => (f.val.app (op V)).hom.map_smul r m⟩
  left_inv a := by
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    ext m
    rfl
  right_inv f := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

/-- The comparison retains literal component values. -/
theorem sectionsEquivOver_apply (U : X.Opens)
    (a : (sheaf M N).val.obj (op U)) (V : Over U)
    (m : M.val.obj (op V.left)) :
    (sectionsEquivOver M N U a).val.app (op V) m = a.1.app (op V) m := rfl

end PfaffianDescent.SchemeModuleInternalHom
