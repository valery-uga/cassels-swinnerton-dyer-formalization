import PfaffianDescent.SchemeModuleGlobalSectionsTop
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# A section on an open subset as a section of the restricted module

The section on an open of a scheme module can be read as a categorical
global section after restricting the module to that open subscheme.
The comparison is explicit, so it can be used to construct the morphism
from the structure sheaf defined by a local generator.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

/-- Transport a section on an open of `X` to a categorical global section
of the module restricted to that open subscheme. -/
noncomputable def schemeModuleSectionOnOpen {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (t : M.presheaf.obj (Opposite.op U)) :
    (M.restrict U.ι).sections := by
  let e := schemeModuleSectionsEquivTop (M.restrict U.ι)
  let e₂ := M.restrictAppIso U.ι ⊤
  exact e.symm
    (e₂.inv ((M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op).inv t))

/-- Reading the transported section on the whole open subscheme recovers
the original section on the open of `X`. -/
theorem schemeModuleSectionOnOpen_value {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (t : M.presheaf.obj (Opposite.op U)) :
    (M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op).hom
      ((M.restrictAppIso U.ι ⊤).hom
        (schemeModuleSectionsEquivTop (M.restrict U.ι)
          (schemeModuleSectionOnOpen M U t))) = t := by
  simp [schemeModuleSectionOnOpen]

/-- The structure-sheaf morphism defined by a section on an open. -/
noncomputable def schemeModuleSectionOnOpenHom {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (t : M.presheaf.obj (Opposite.op U)) :
    SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf ⟶ M.restrict U.ι :=
  (M.restrict U.ι).unitHomEquiv.symm (schemeModuleSectionOnOpen M U t)

/-- The morphism from the structure sheaf corresponds to the transported
section under Mathlib's unit-module adjunction. -/
theorem schemeModuleSectionOnOpenHom_section {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (t : M.presheaf.obj (Opposite.op U)) :
    (M.restrict U.ι).unitHomEquiv (schemeModuleSectionOnOpenHom M U t) =
      schemeModuleSectionOnOpen M U t := by
  exact (M.restrict U.ι).unitHomEquiv.apply_symm_apply _

/-- Applied to `1` on the whole open subscheme, the structure-sheaf
morphism returns the section from which it was constructed. -/
theorem schemeModuleSectionOnOpenHom_value {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (t : M.presheaf.obj (Opposite.op U)) :
    (M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op).hom
      ((M.restrictAppIso U.ι ⊤).hom
        (((schemeModuleSectionOnOpenHom M U t).val.app
          (Opposite.op ⊤)) (1 : Γ((U : Scheme.{u}), ⊤)))) = t := by
  change (M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op).hom
    ((M.restrictAppIso U.ι ⊤).hom
      (((M.restrict U.ι).unitHomEquiv (schemeModuleSectionOnOpenHom M U t)).val
        (Opposite.op ⊤))) = t
  rw [schemeModuleSectionOnOpenHom_section]
  exact schemeModuleSectionOnOpen_value M U t

/-- The image of `1` under a morphism from the structure sheaf restricts
to the image of `1` on every smaller open. -/
theorem schemeModuleUnitHom_restrict_one {X : Scheme.{u}} (M : X.Modules)
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) (V : X.Opens) :
    φ.val.app (Opposite.op V) (1 : Γ(X, V)) =
      M.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (φ.val.app (Opposite.op ⊤) (1 : Γ(X, ⊤))) := by
  have hnat := PresheafOfModules.naturality_apply φ.val
    (homOfLE (show V ≤ ⊤ from le_top)).op (1 : Γ(X, ⊤))
  have hunit : ((SheafOfModules.unit X.ringCatSheaf).val.map
      (homOfLE (show V ≤ ⊤ from le_top)).op) (1 : Γ(X, ⊤)) =
      (1 : Γ(X, V)) := by
    change (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op).hom 1 = 1
    exact map_one _
  rw [hunit] at hnat
  exact hnat

set_option linter.style.haveILetI false in
/-- A structure-sheaf-to-module morphism acts on any section by scalar
multiplication with its value at `1`. -/
theorem schemeModuleUnitHom_apply_eq_smul_one {X : Scheme.{u}} (M : X.Modules)
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) (V : X.Opens)
    (a : Γ(X, V)) :
    letI : Module (Γ(X, V)) ((M.val.obj (Opposite.op V) : ModuleCat _)) :=
      (M.val.obj (Opposite.op V)).isModule
    φ.val.app (Opposite.op V) a =
      a • φ.val.app (Opposite.op V) (1 : Γ(X, V)) := by
  dsimp only
  letI : Module (Γ(X, V)) ((M.val.obj (Opposite.op V) : ModuleCat _)) :=
    (M.val.obj (Opposite.op V)).isModule
  calc
    φ.val.app (Opposite.op V) a =
        φ.val.app (Opposite.op V) (a • (1 : Γ(X, V))) := by simp [smul_eq_mul]
    _ = a • φ.val.app (Opposite.op V) (1 : Γ(X, V)) := by
      exact (φ.val.app (Opposite.op V)).hom.map_smul a (1 : Γ(X, V))

/-- On every smaller open of `U`, the section morphism takes `1` to the
restriction of its original section, after the canonical comparison of
restricted-module sections with sections on the image open in `X`. -/
theorem schemeModuleSectionOnOpenHom_restrict_value {X : Scheme.{u}}
    (M : X.Modules) (U : X.Opens)
    (t : M.presheaf.obj (Opposite.op U)) (V : (U : Scheme.{u}).Opens) :
    (M.restrictAppIso U.ι V).hom
      (((schemeModuleSectionOnOpenHom M U t).val.app (Opposite.op V))
        (1 : Γ((U : Scheme.{u}), V))) =
    M.presheaf.map
      (homOfLE (Scheme.Hom.image_mono U.ι (show V ≤ ⊤ from le_top))).op
      ((M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op).inv t) := by
  let φ := schemeModuleSectionOnOpenHom M U t
  have hres := schemeModuleUnitHom_restrict_one (M.restrict U.ι) φ V
  have hres' := congrArg (fun m => (M.restrictAppIso U.ι V).hom m) hres
  have htop := schemeModuleSectionOnOpenHom_value M U t
  have htop' : (M.restrictAppIso U.ι ⊤).hom
      (φ.val.app (Opposite.op ⊤) (1 : Γ((U : Scheme.{u}), ⊤))) =
      (M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op).inv t := by
    apply (ConcreteCategory.bijective_of_isIso
      (M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op).hom).1
    simpa [φ] using htop
  change (M.restrictAppIso U.ι V).hom
      (φ.val.app (Opposite.op V) (1 : Γ((U : Scheme.{u}), V))) =
    M.presheaf.map
      (homOfLE (Scheme.Hom.image_mono U.ι (show V ≤ ⊤ from le_top))).op
      ((M.restrictAppIso U.ι ⊤).hom
        (φ.val.app (Opposite.op ⊤) (1 : Γ((U : Scheme.{u}), ⊤)))) at hres'
  rw [htop'] at hres'
  exact hres'

/-- The preceding formula with the image of the top open identified with
`U` itself. This is the form used with ideal generators on affine subopens
of the ambient scheme. -/
theorem schemeModuleSectionOnOpenHom_restrict_value' {X : Scheme.{u}}
    (M : X.Modules) (U : X.Opens)
    (t : M.presheaf.obj (Opposite.op U)) (V : (U : Scheme.{u}).Opens) :
    let hVU : U.ι ''ᵁ V ≤ U := by
      simpa only [U.ι_image_top] using
        (Scheme.Hom.image_mono U.ι (show V ≤ ⊤ from le_top))
    (M.restrictAppIso U.ι V).hom
      (((schemeModuleSectionOnOpenHom M U t).val.app (Opposite.op V))
        (1 : Γ((U : Scheme.{u}), V))) =
    M.presheaf.map (homOfLE hVU).op t := by
  dsimp only
  have h := schemeModuleSectionOnOpenHom_restrict_value M U t V
  have hmap :
      M.presheaf.map
        (homOfLE (Scheme.Hom.image_mono U.ι (show V ≤ ⊤ from le_top))).op
        ((M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op).inv t) =
      M.presheaf.map (homOfLE (by
        simpa only [U.ι_image_top] using
          (Scheme.Hom.image_mono U.ι (show V ≤ ⊤ from le_top)))).op t := by
    change (M.presheaf.map
        (homOfLE (Scheme.Hom.image_mono U.ι (show V ≤ ⊤ from le_top))).op).hom
        ((M.presheaf.map (eqToIso U.ι_image_top.symm).op.inv).hom t) =
      (M.presheaf.map (homOfLE (by
        simpa only [U.ι_image_top] using
          (Scheme.Hom.image_mono U.ι (show V ≤ ⊤ from le_top)))).op).hom t
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    congr 1
  rw [hmap] at h
  exact h

/-- An isomorphism of scheme modules can be checked on a basis of opens.
The passage through the underlying sheaf of additive groups avoids any
quasicoherence hypothesis. -/
theorem schemeModuleHom_isIso_of_basis {X : Scheme.{u}} (M N : X.Modules)
    (φ : M ⟶ N) {ι : Type v} (B : ι → X.Opens)
    (hB : Opens.IsBasis (Set.range B))
    (h : ∀ i, IsIso (φ.val.app (Opposite.op (B i)))) : IsIso φ := by
  apply (isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf X.ringCatSheaf)).mp
  apply TopCat.Sheaf.isIso_iff_isIso_basis hB
  intro i
  rw [ConcreteCategory.isIso_iff_bijective]
  have hh := h i
  rw [ConcreteCategory.isIso_iff_bijective] at hh
  exact hh

end PfaffianDescent
