import PfaffianDescent.SchemeModuleLocallyRankOneTensor
import Mathlib.AlgebraicGeometry.FunctionField

/-! Actual restriction into an open containing the generic point is
injective for an integral scheme's actual locally rank-one coefficient.
The proof uses original unit charts, original ring restriction injectivity
and the genuine sheaf section law, not a dense-restriction certificate.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}} [IsIntegral X]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Ordinary additive-presheaf composition without scheme-module
restriction-scalar wrappers. Its maps are the original maps. -/
private theorem additiveRestriction_comp_apply
    {C : Type*} [Category C] (F : C ⥤ AddCommGrpCat.{u})
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D)
    (hcomp : f ≫ g = h) (s : F.obj A) :
    F.map g (F.map f s) = F.map h s := by
  have he : F.map (f ≫ g) s = F.map g (F.map f s) :=
    ConcreteCategory.congr_hom (F.map_comp f g) s
  exact he.symm.trans (congrArg (fun k : A ⟶ D => F.map k s) hcomp)

/-- Genuine section injectivity on the actual generic-point open. This
supplies the field-valued section map's injectivity for constructed duals
and later actual tensor words once their rank-one geometry is internal. -/
theorem schemeModuleLocallyRankOne_topRestriction_injective
    (M : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (U : X.Opens) (hgU : genericPoint X ∈ U) :
    Function.Injective (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op) := by
  classical
  intro s t hst
  apply TopCat.Presheaf.IsSheaf.section_ext M.isSheaf
  intro x hx
  obtain ⟨V, hxV, ⟨e⟩⟩ := hM x
  refine ⟨V, le_top, hxV, ?_⟩
  let W := V ⊓ U
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hgV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using (inferInstance : Nonempty V))
  letI : Nonempty W := ⟨⟨genericPoint X, ⟨hgV, hgU⟩⟩⟩
  let sV := M.val.map (homOfLE (show V ≤ ⊤ from le_top)).op s
  let tV := M.val.map (homOfLE (show V ≤ ⊤ from le_top)).op t
  have hleft (v : M.val.obj (op ⊤)) :
      M.val.map (homOfLE (show W ≤ V from inf_le_left)).op
          (M.val.map (homOfLE (show V ≤ ⊤ from le_top)).op v) =
        M.val.map (homOfLE (show W ≤ ⊤ from le_top)).op v := by
    have he : (homOfLE (show V ≤ ⊤ from le_top)).op ≫
        (homOfLE (show W ≤ V from inf_le_left)).op =
        (homOfLE (show W ≤ ⊤ from le_top)).op := Subsingleton.elim _ _
    exact additiveRestriction_comp_apply M.val.presheaf
      (homOfLE (show V ≤ ⊤ from le_top)).op
      (homOfLE (show W ≤ V from inf_le_left)).op
      (homOfLE (show W ≤ ⊤ from le_top)).op he v
  have hright (v : M.val.obj (op ⊤)) :
      M.val.map (homOfLE (show W ≤ U from inf_le_right)).op
          (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op v) =
        M.val.map (homOfLE (show W ≤ ⊤ from le_top)).op v := by
    have he : (homOfLE (show U ≤ ⊤ from le_top)).op ≫
        (homOfLE (show W ≤ U from inf_le_right)).op =
        (homOfLE (show W ≤ ⊤ from le_top)).op := Subsingleton.elim _ _
    exact additiveRestriction_comp_apply M.val.presheaf
      (homOfLE (show U ≤ ⊤ from le_top)).op
      (homOfLE (show W ≤ U from inf_le_right)).op
      (homOfLE (show W ≤ ⊤ from le_top)).op he v
  have hW : M.val.map (homOfLE (show W ≤ V from inf_le_left)).op sV =
      M.val.map (homOfLE (show W ≤ V from inf_le_left)).op tV := by
    exact (hleft s).trans ((hright s).symm.trans
      ((congrArg (M.val.map (homOfLE (show W ≤ U from inf_le_right)).op) hst).trans
        ((hright t).trans (hleft t).symm)))
  let a : Over.mk (homOfLE (show W ≤ V from inf_le_left)) ⟶ Over.mk (𝟙 V) :=
    Over.homMk (homOfLE (show W ≤ V from inf_le_left))
  have hnat (v : M.val.obj (op V)) :
      X.presheaf.map (homOfLE (show W ≤ V from inf_le_left)).op
          (e.hom.val.app (op (Over.mk (𝟙 V))) v) =
        e.hom.val.app (op (Over.mk (homOfLE (show W ≤ V from inf_le_left))))
          (M.val.map (homOfLE (show W ≤ V from inf_le_left)).op v) :=
    (PresheafOfModules.naturality_apply e.hom.val a.op v).symm
  have hi : Function.Injective (e.hom.val.app (op (Over.mk (𝟙 V)))) :=
    (SchemeModuleInternalHom.overTopLinearEquiv M V e).injective
  apply hi
  apply map_injective_of_isIntegral X (homOfLE (show W ≤ V from inf_le_left))
  exact (hnat sV).trans ((congrArg
    (e.hom.val.app (op (Over.mk (homOfLE (show W ≤ V from inf_le_left))))) hW).trans
      (hnat tV).symm)

end PfaffianDescent
