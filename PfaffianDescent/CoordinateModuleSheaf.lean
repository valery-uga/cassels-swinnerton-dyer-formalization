import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
section
variable (X : Scheme.{u}) (ι : Type)

/-- The presheaf of coordinate tuples of regular functions, with its pointwise module structure. -/
noncomputable def coordinateModulePresheaf : X.PresheafOfModules where
  obj U := ModuleCat.of (X.ringCatSheaf.obj.obj U) (ι → X.ringCatSheaf.obj.obj U)
  map {U V} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).obj
      (ModuleCat.of (X.ringCatSheaf.obj.obj V) (ι → X.ringCatSheaf.obj.obj V)))
    { toFun c i := X.ringCatSheaf.obj.map f (c i)
      map_add' c d := by funext i; exact map_add (X.ringCatSheaf.obj.map f).hom _ _
      map_smul' r c := by
        funext i
        exact map_mul (X.ringCatSheaf.obj.map f).hom r (c i) }
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    change (fun i => X.ringCatSheaf.obj.map (𝟙 U) (c i)) = c
    funext i
    rw [X.ringCatSheaf.obj.map_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    change (fun i => X.ringCatSheaf.obj.map (f ≫ g) (c i)) =
      (fun i => X.ringCatSheaf.obj.map g (X.ringCatSheaf.obj.map f (c i)))
    funext i
    rw [X.ringCatSheaf.obj.map_comp]
    rfl

/-- Coordinate projection to the structure presheaf. -/
noncomputable def coordinateModulePresheafProjection (i : ι) :
    coordinateModulePresheaf X ι ⟶ PresheafOfModules.unit X.ringCatSheaf.obj where
  app U := ModuleCat.ofHom (LinearMap.proj i)
  naturality f := by ext c; rfl

noncomputable def coordinateModulePresheafFan :
    Fan (fun _ : ι => PresheafOfModules.unit X.ringCatSheaf.obj) :=
  Fan.mk (coordinateModulePresheaf X ι) (coordinateModulePresheafProjection X ι)

/-- Tuple-valued sections form the categorical product of copies of the structure presheaf. -/
noncomputable def coordinateModulePresheafFanIsLimit : IsLimit (coordinateModulePresheafFan X ι) := by
  refine Fan.IsLimit.mk _ (fun s => ?_) ?_ ?_
  · exact
      { app U := ModuleCat.ofHom (LinearMap.pi (fun i => ((s.proj i).app U).hom))
        naturality := fun {U V} f => by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro c
          change (fun i => (s.proj i).app V (s.pt.map f c)) =
            (fun i => X.ringCatSheaf.obj.map f ((s.proj i).app U c))
          funext i
          exact CategoryTheory.congr_fun ((s.proj i).naturality f) c }
  · intro s i
    ext U c
    rfl
  · intro s m hm
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    change (m.app U c) = (fun i => (s.proj i).app U c)
    funext i
    exact CategoryTheory.congr_fun (congrArg (fun f => f.app U) (hm i)) c

/-- The sheaf condition for coordinate tuples follows from the product limit. -/
lemma coordinateModulePresheaf_isSheaf :
    TopCat.Presheaf.IsSheaf (coordinateModulePresheaf X ι).presheaf :=
  PresheafOfModules.isSheaf_of_isLimit (coordinateModulePresheafFanIsLimit X ι)
    (fun _ => (SheafOfModules.unit X.ringCatSheaf).isSheaf)

/-- The actual sheaf of coordinate tuples of regular functions on a scheme. -/
noncomputable def coordinateModuleSheaf : X.Modules :=
  ⟨coordinateModulePresheaf X ι, coordinateModulePresheaf_isSheaf X ι⟩

lemma coordinateModuleSheaf_sections (U : X.Opens) :
    (Γ(coordinateModuleSheaf X ι, U) : Type u) = (ι → Γ(X, U)) := rfl

end
end PfaffianDescent
