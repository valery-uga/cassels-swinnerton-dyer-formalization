import PfaffianDescent.SchemeModuleFixedFrameStalkFunctionField

/-! Shrinking an actual fixed frame preserves the SAME original local
and stalk field maps. Every equality follows from coefficient naturality
and actual generic germs; no comparison premise. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem restrictedChart_app
    (M : X.Modules) {B C : X.Opens} (f : C ⟶ B)
    (e : M.over B ≅ (SheafOfModules.unit X.ringCatSheaf).over B)
    {W : X.Opens} (g : W ⟶ C) (a : M.val.obj (op W)) :
    ((SchemeModuleInternalHom.overUnitChartRestrict M f e).hom.val.app (op (Over.mk g)) a :
        Γ(X, W)) = e.hom.val.app (op (Over.mk (g ≫ f))) a := rfl

private theorem additiveRestriction_comp
    {C : Type*} [Category C] (F : C ⥤ AddCommGrpCat.{u})
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D)
    (he : f ≫ g = h) (s : F.obj A) :
    F.map g (F.map f s) = F.map h s :=
  (ConcreteCategory.congr_hom (F.map_comp f g) s).symm.trans
    (congrArg (fun k : A ⟶ D => F.map k s) he)

variable {K : Type u} [Field K] [IsIntegral X]

private theorem generic_mem (U : X.Opens) [Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
    (by simpa using (inferInstance : Nonempty U))

/-- Actual K-linear local maps are unchanged on shrinking the nonempty
fixed open and restricting the SAME original chart by the actual functor. -/
theorem schemeModuleFixedFrameOpenToFunctionFieldLinearMap_shrink
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (B C : X.Opens) [Nonempty B] [Nonempty C] (f : C ⟶ B)
    (e : M.over B ≅ (SheafOfModules.unit X.ringCatSheaf).over B)
    (U : X.Opens) [Nonempty U] :
    schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C
        (SchemeModuleInternalHom.overUnitChartRestrict M f e) U =
      schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M B e U := by
  apply LinearMap.ext
  intro a
  change M.val.obj (op U) at a
  let A : X.Opens := U ⊓ B
  let W : X.Opens := U ⊓ C
  letI : Nonempty A := ⟨⟨genericPoint X, generic_mem U, generic_mem B⟩⟩
  letI : Nonempty W := ⟨⟨genericPoint X, generic_mem U, generic_mem C⟩⟩
  let rA : A ⟶ U := homOfLE inf_le_left
  let rW : W ⟶ U := homOfLE inf_le_left
  let rC : W ⟶ C := homOfLE inf_le_right
  let fA : A ⟶ B := homOfLE inf_le_right
  let fW : W ⟶ B := rC ≫ f
  let g : W ⟶ A := homOfLE (le_inf inf_le_left (inf_le_right.trans f.le))
  have hs : M.val.map rW.op a = M.val.map g.op (M.val.map rA.op a) :=
    (additiveRestriction_comp M.val.presheaf rA.op g.op rW.op
      (Subsingleton.elim _ _) a).symm
  let k : Over.mk fW ⟶ Over.mk fA := Over.homMk g (Subsingleton.elim _ _)
  have hc : (e.hom.val.app (op (Over.mk fW)) (M.val.map g.op (M.val.map rA.op a)) :
      Γ(X, W)) = X.presheaf.map g.op (e.hom.val.app (op (Over.mk fA)) (M.val.map rA.op a)) :=
    PresheafOfModules.naturality_apply e.hom.val k.op (M.val.map rA.op a)
  exact (schemeModuleFixedFrameOpenToFunctionFieldLinearMap_apply pi M C
    (SchemeModuleInternalHom.overUnitChartRestrict M f e) U a).trans
      ((congrArg (X.germToFunctionField W)
        (restrictedChart_app M f e rC (M.val.map rW.op a))).trans
          ((congrArg (fun s => X.germToFunctionField W
            (e.hom.val.app (op (Over.mk fW)) s)) hs).trans
              ((congrArg (X.germToFunctionField W) hc).trans
                ((X.presheaf.germ_res_apply g (genericPoint X) (generic_mem W) _).trans
                  (schemeModuleFixedFrameOpenToFunctionFieldLinearMap_apply pi M B e U a).symm))))

/-- The literal native stalk-linear map is independent of shrinking the
actual fixed frame. Actual stalk representatives prove this, with the SAME
source and target scalar actions on both sides. -/
theorem schemeModuleFixedFrameStalkToFunctionFieldLinearMap_shrink
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (B C : X.Opens) [Nonempty B] [Nonempty C] (f : C ⟶ B)
    (e : M.over B ≅ (SheafOfModules.unit X.ringCatSheaf).over B) (x : X) :
    letI := schemeModuleStalkModule M x
    schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C
        (SchemeModuleInternalHom.overUnitChartRestrict M f e) x =
      schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M B e x := by
  letI := schemeModuleStalkModule M x
  apply LinearMap.ext
  intro a
  obtain ⟨U, hxU, m, rfl⟩ := M.presheaf.exists_germ_eq a
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  exact (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_germ pi M C
    (SchemeModuleInternalHom.overUnitChartRestrict M f e) x U hxU m).trans
      ((DFunLike.congr_fun (schemeModuleFixedFrameOpenToFunctionFieldLinearMap_shrink
        pi M B C f e U) m).trans
          (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_germ pi M B e x U hxU m).symm)

end PfaffianDescent
