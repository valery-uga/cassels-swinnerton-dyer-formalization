import PfaffianDescent.CorayAffineOriginalTopSections
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! Original open sections versus actual restricted top sections.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual sections over the ORIGINAL open, with ORIGINAL Γ(X,U) scalars. -/
def schemeOpenModuleFunctor (X : Scheme.{u}) (U : X.Opens) :
    X.Modules ⥤ ModuleCat Γ(X, U) where
  obj M := ModuleCat.of Γ(X, U) Γ(M, U)
  map φ := ModuleCat.ofHom (φ.val.app (op U)).hom
  map_id M := by apply ModuleCat.hom_ext; rfl
  map_comp φ ψ := by apply ModuleCat.hom_ext; rfl

/-- The actual top-section comparison over an open retains the original
open-ring action, proved by the actual module restriction formula. -/
def originalOpenRestrictTopSectionsIso (X : Scheme.{u}) (U : X.Opens)
    (M : X.Modules) :
    (ModuleCat.restrictScalars U.topIso.inv.hom).obj
      ((schemeTopModuleFunctor U.toScheme).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj M)) ≅
      (schemeOpenModuleFunctor X U).obj M := by
  dsimp only [schemeTopModuleFunctor, schemeOpenModuleFunctor]
  let e :
      (forget₂ (ModuleCat Γ(X, U)) Ab).obj
        ((ModuleCat.restrictScalars U.topIso.inv.hom).obj
          (ModuleCat.of Γ(U.toScheme, ⊤) Γ(M.restrict U.ι, ⊤))) ≅
      (forget₂ (ModuleCat Γ(X, U)) Ab).obj
        (ModuleCat.of Γ(X, U) Γ(M, U)) :=
    M.restrictAppIso U.ι ⊤ ≪≫
      M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op
  refine ModuleCat.isoMk e ?_
  intro r
  let T := ModuleCat.of Γ(U.toScheme, ⊤) Γ(M.restrict U.ι, ⊤)
  have hscalar : ((ModuleCat.restrictScalars U.topIso.inv.hom).obj T).smul r =
      T.smul (U.topIso.inv r) :=
    ModuleCat.smul_restrictScalars U.topIso.inv.hom r T
  have hsquare : e.hom ≫ (ModuleCat.of Γ(X, U) Γ(M, U)).smul r =
      T.smul (U.topIso.inv r) ≫ e.hom := by
    let a := M.restrictAppIso U.ι ⊤
    let b := M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op
    change (a.hom ≫ b.hom) ≫ M.smul r =
      (M.restrict U.ι).smul (U.topIso.inv r) ≫ (a.hom ≫ b.hom)
    have hι : (U.ι.appIso ⊤).inv (U.topIso.inv r) = U.topIso.inv r := by
      simp only [Scheme.Opens.ι_appIso]
      rfl
    have hs : (M.restrict U.ι).smul (U.topIso.inv r) ≫ a.hom =
        a.hom ≫ M.smul (U.topIso.inv r) := by
      have h := M.smul_restrictAppIso_hom U.ι ⊤ (U.topIso.inv r)
      rw [hι] at h
      exact h
    have hr : X.presheaf.map (eqToHom U.ι_image_top.symm).op (U.topIso.inv r) = r := by
      change U.topIso.hom (U.topIso.inv r) = r
      exact ConcreteCategory.congr_hom U.topIso.inv_hom_id r
    have hn : M.smul (U.topIso.inv r) ≫ b.hom = b.hom ≫ M.smul r := by
      have h := M.map_comp_smul (eqToHom U.ι_image_top.symm) (U.topIso.inv r)
      rw [hr] at h
      exact h
    calc
      (a.hom ≫ b.hom) ≫ M.smul r = a.hom ≫ (b.hom ≫ M.smul r) :=
        Category.assoc _ _ _
      _ = a.hom ≫ (M.smul (U.topIso.inv r) ≫ b.hom) :=
        congrArg (fun k ↦ a.hom ≫ k) hn.symm
      _ = (a.hom ≫ M.smul (U.topIso.inv r)) ≫ b.hom :=
        (Category.assoc _ _ _).symm
      _ = ((M.restrict U.ι).smul (U.topIso.inv r) ≫ a.hom) ≫ b.hom :=
        congrArg (fun k ↦ k ≫ b.hom) hs.symm
      _ = (M.restrict U.ι).smul (U.topIso.inv r) ≫ (a.hom ≫ b.hom) :=
        Category.assoc _ _ _
  exact hsquare.trans (congrArg (fun k ↦ k ≫ e.hom) hscalar.symm)

/-- The comparison is natural for actual module maps, including the actual
normalization inclusion and its actual quotient projection. -/
def originalOpenRestrictTopSectionsNatIso (X : Scheme.{u}) (U : X.Opens) :
    Scheme.Modules.restrictFunctor U.ι ⋙ schemeTopModuleFunctor U.toScheme ⋙
      ModuleCat.restrictScalars U.topIso.inv.hom ≅ schemeOpenModuleFunctor X U := by
  refine NatIso.ofComponents (originalOpenRestrictTopSectionsIso X U) ?_
  intro M N φ
  let F := Scheme.Modules.restrictFunctor U.ι ⋙ schemeTopModuleFunctor U.toScheme ⋙
    ModuleCat.restrictScalars U.topIso.inv.hom
  let G := schemeOpenModuleFunctor X U
  let A := forget₂ (ModuleCat Γ(X, U)) Ab
  have hcomponent (L : X.Modules) :
      A.map (originalOpenRestrictTopSectionsIso X U L).hom =
        L.presheaf.map (eqToHom U.ι_image_top.symm).op := by
    dsimp only [A, originalOpenRestrictTopSectionsIso,
      schemeTopModuleFunctor, schemeOpenModuleFunctor]
    simp only [id, ModuleCat.isoMk_hom, ModuleCat.forget₂_map_homMk,
      Iso.trans_hom, Scheme.Modules.restrictAppIso, Iso.refl_hom,
      Category.id_comp, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]
    exact Category.id_comp _
  have hmap : A.map (F.map φ) = φ.mapPresheaf.app (op (U.ι ''ᵁ ⊤)) := by
    dsimp only [A, F, Functor.comp_map, Functor.comp_obj,
      schemeTopModuleFunctor]
    simp only [ModuleCat.forget₂_map_restrictScalars, ModuleCat.ofHom_hom,
      Scheme.Modules.restrictFunctor, SheafOfModules.pushforward_map_val,
      Scheme.Modules.mapPresheaf_app, Scheme.Modules.Hom.app]
    apply AddCommGrpCat.hom_ext
    rfl
  have hG : A.map (G.map φ) = φ.mapPresheaf.app (op U) := by
    simp only [A, G, schemeOpenModuleFunctor, ModuleCat.ofHom_hom,
      Scheme.Modules.mapPresheaf_app, Scheme.Modules.Hom.app]
    apply AddCommGrpCat.hom_ext
    rfl
  apply A.map_injective
  rw [Functor.map_comp, Functor.map_comp, hcomponent, hcomponent, hmap, hG]
  exact (φ.mapPresheaf.naturality (eqToHom U.ι_image_top.symm).op).symm

end PfaffianDescent.Coray
