import PfaffianDescent.CoordinateModuleSheafMaps
import PfaffianDescent.CoordinateModuleSheafFree

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
section
variable (X : Scheme.{u})

/-- Restriction of functions from one open subset to a smaller one. -/
noncomputable def regularFunctionRestrictFrom (U V : X.Opens) (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

lemma regularFunctionRestrictFrom_trans (U V W : X.Opens) (hV : V ≤ U) (hW : W ≤ V)
    (r : Γ(X, U)) :
    regularFunctionRestrictFrom X V W hW (regularFunctionRestrictFrom X U V hV r) =
      regularFunctionRestrictFrom X U W (hW.trans hV) r :=
  CategoryTheory.congr_fun (X.presheaf.map_comp (homOfLE hV).op (homOfLE hW).op).symm r

/-- The coordinate sheaf restricted to an open is the corresponding free sheaf on that open site. -/
noncomputable def coordinateModuleSheafOverFree (U : X.Opens) (ι : Type) [Finite ι] :
    (coordinateModuleSheaf X ι).over U ≅
      SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} ι) := by
  let F : SheafOfModules X.ringCatSheaf ⥤ SheafOfModules (X.ringCatSheaf.over U) :=
    SheafOfModules.pushforward (F := Over.forget U) (𝟙 (X.ringCatSheaf.over U))
  let η : SheafOfModules.unit (X.ringCatSheaf.over U) ≅ F.obj (SheafOfModules.unit X.ringCatSheaf) := Iso.refl _
  haveI : PreservesColimitsOfSize.{u, u} F := by dsimp [F]; infer_instance
  exact F.mapIso (coordinateModuleSheafFree X ι) ≪≫
    (SheafOfModules.mapFreeIso F (ULift.{u} ι) η).symm

variable (U : X.Opens) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A matrix regular on an open subset defines a morphism of coordinate sheaves over that open. -/
noncomputable def coordinateModuleSheafOverMatrix (P : Matrix κ ι Γ(X, U)) :
    (coordinateModuleSheaf X ι).over U ⟶ (coordinateModuleSheaf X κ).over U where
  val :=
    { app V := by
        change ModuleCat.of Γ(X, V.unop.left) (ι → Γ(X, V.unop.left)) ⟶
          ModuleCat.of Γ(X, V.unop.left) (κ → Γ(X, V.unop.left))
        exact ModuleCat.ofHom (Matrix.toLin' (P.map
          (regularFunctionRestrictFrom X U V.unop.left (leOfHom V.unop.hom))))
      naturality := fun {V W} h => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro c
        change (P.map (regularFunctionRestrictFrom X U W.unop.left (leOfHom W.unop.hom))).mulVec
          ((X.presheaf.map h.unop.left.op).hom ∘ c) =
          (X.presheaf.map h.unop.left.op).hom ∘
            (P.map (regularFunctionRestrictFrom X U V.unop.left (leOfHom V.unop.hom))).mulVec c
        have he : (P.map (regularFunctionRestrictFrom X U V.unop.left (leOfHom V.unop.hom))).map
            (X.presheaf.map h.unop.left.op).hom =
            P.map (regularFunctionRestrictFrom X U W.unop.left (leOfHom W.unop.hom)) := by
          funext i j
          exact regularFunctionRestrictFrom_trans X U V.unop.left W.unop.left
            (leOfHom V.unop.hom) (leOfHom h.unop.left) (P i j)
        rw [← he]
        funext i
        exact (RingHom.map_mulVec (X.presheaf.map h.unop.left.op).hom _ c i).symm }

end
end PfaffianDescent
