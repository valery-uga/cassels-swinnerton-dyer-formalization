import PfaffianDescent.VoisinSheafStalk
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Adjunction.Additive

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

local instance schemeModuleSkyscraperDecidableMem
    {X : Scheme.{u}} (x : X) (U : X.Opens) : Decidable (x ∈ U) :=
  Classical.dec _

def schemeModuleSkyscraperSection
    {X : Scheme.{u}} (x : X)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) :
    ModuleCat.{u} Γ(X, U) := by
  classical
  exact if h : x ∈ U then
      (ModuleCat.restrictScalars (X.presheaf.germ U x h).hom).obj A
    else
      ModuleCat.of Γ(X, U) PUnit

@[simp]
lemma schemeModuleSkyscraperSection_coe_of_mem
    {X : Scheme.{u}} (x : X)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) (hx : x ∈ U) :
    (schemeModuleSkyscraperSection x A U : Type u) = A := by
  simp [schemeModuleSkyscraperSection, hx]
  rfl

@[simp]
lemma schemeModuleSkyscraperSection_coe_of_not_mem
    {X : Scheme.{u}} (x : X)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) (hx : x ∉ U) :
    (schemeModuleSkyscraperSection x A U : Type u) = PUnit := by
  simp [schemeModuleSkyscraperSection, hx]

noncomputable def schemeModuleSkyscraperAbPresheaf
    {X : Scheme.{u}} (x : X)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) :
    TopCat.Presheaf AddCommGrpCat.{u} X.toTopCat :=
  skyscraperPresheaf x ((forget₂ _ AddCommGrpCat).obj A)

noncomputable def schemeModuleSkyscraperAbPresheafIsoOfMem
    {X : Scheme.{u}} (x : X)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) (hx : x ∈ U) :
    (schemeModuleSkyscraperAbPresheaf x A).obj (op U) ≅
      (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj A :=
  eqToIso (by simp [schemeModuleSkyscraperAbPresheaf, hx])

noncomputable def schemeModuleSkyscraperAbPresheafAddEquivOfMem
    {X : Scheme.{u}} (x : X)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) (hx : x ∈ U) :
    (schemeModuleSkyscraperAbPresheaf x A).obj (op U) ≃+ A :=
  (schemeModuleSkyscraperAbPresheafIsoOfMem x A U hx).addCommGroupIsoToAddEquiv

noncomputable instance schemeModuleSkyscraperAbPresheaf_module
    {X : Scheme.{u}} (x : X)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opensᵒᵖ) :
    Module (X.presheaf.obj U) ((schemeModuleSkyscraperAbPresheaf x A).obj U) := by
  rcases U with ⟨U⟩
  by_cases hx : x ∈ U
  · let e := schemeModuleSkyscraperAbPresheafAddEquivOfMem x A U hx
    letI : Module Γ(X, U) A :=
      Module.compHom A (X.presheaf.germ U x hx).hom
    exact e.module Γ(X, U)
  · let eCat : (schemeModuleSkyscraperAbPresheaf x A).obj (op U) ≅
        AddCommGrpCat.of PUnit :=
      eqToIso (by simp [schemeModuleSkyscraperAbPresheaf, hx]) ≪≫
        terminalIsTerminal.uniqueUpToIso
          (AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of PUnit)).isTerminal
    let e := eCat.addCommGroupIsoToAddEquiv
    exact e.module Γ(X, U)

set_option linter.style.haveILetI false in
@[simp]
theorem schemeModuleSkyscraperAbPresheafAddEquivOfMem_smul
    {X : Scheme.{u}} (x : X)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) (hx : x ∈ U)
    (r : Γ(X, U)) (m : (schemeModuleSkyscraperAbPresheaf x A).obj (op U)) :
    schemeModuleSkyscraperAbPresheafAddEquivOfMem x A U hx
        (letI := schemeModuleSkyscraperAbPresheaf_module x A (op U); r • m) =
      X.presheaf.germ U x hx r •
        schemeModuleSkyscraperAbPresheafAddEquivOfMem x A U hx m := by
  let e := schemeModuleSkyscraperAbPresheafAddEquivOfMem x A U hx
  letI : Module Γ(X, U) A :=
    Module.compHom A (X.presheaf.germ U x hx).hom
  have hmod : schemeModuleSkyscraperAbPresheaf_module x A (op U) =
      e.module Γ(X, U) := by
    unfold schemeModuleSkyscraperAbPresheaf_module
    dsimp only [Opposite.casesOn]
    rw [dif_pos hx]
  rw [hmod]
  change e (e.symm (r • e m)) = _
  rw [e.apply_symm_apply]
  rfl

@[simp]
theorem schemeModuleSkyscraperAbPresheafAddEquivOfMem_map
    {X : Scheme.{u}} (x : X)
    (A : ModuleCat.{u} (X.presheaf.stalk x))
    {U V : X.Opensᵒᵖ} (f : U ⟶ V) (hV : x ∈ V.unop)
    (m : (schemeModuleSkyscraperAbPresheaf x A).obj U) :
    schemeModuleSkyscraperAbPresheafAddEquivOfMem x A V.unop hV
        ((schemeModuleSkyscraperAbPresheaf x A).map f m) =
      schemeModuleSkyscraperAbPresheafAddEquivOfMem x A U.unop (f.unop.le hV) m := by
  let B := (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj A
  let pU : (schemeModuleSkyscraperAbPresheaf x A).obj U = B := by
    simp [B, schemeModuleSkyscraperAbPresheaf, f.unop.le hV]
  let pV : (schemeModuleSkyscraperAbPresheaf x A).obj V = B := by
    simp [B, schemeModuleSkyscraperAbPresheaf, hV]
  let q : (schemeModuleSkyscraperAbPresheaf x A).obj U =
      (schemeModuleSkyscraperAbPresheaf x A).obj V := pU.trans pV.symm
  have hmap : (schemeModuleSkyscraperAbPresheaf x A).map f = eqToHom q := by
    unfold schemeModuleSkyscraperAbPresheaf
    dsimp only [skyscraperPresheaf]
    rw [dif_pos hV]
  have heU : (schemeModuleSkyscraperAbPresheafIsoOfMem
      x A U.unop (f.unop.le hV)).hom = eqToHom pU := by
    unfold schemeModuleSkyscraperAbPresheafIsoOfMem
    congr
  have heV : (schemeModuleSkyscraperAbPresheafIsoOfMem
      x A V.unop hV).hom = eqToHom pV := by
    unfold schemeModuleSkyscraperAbPresheafIsoOfMem
    congr
  unfold schemeModuleSkyscraperAbPresheafAddEquivOfMem
  rw [Iso.addCommGroupIsoToAddEquiv_apply,
    Iso.addCommGroupIsoToAddEquiv_apply, ← ConcreteCategory.comp_apply,
    hmap, heU, heV]
  change ConcreteCategory.hom (eqToHom q ≫ eqToHom pV) m =
    ConcreteCategory.hom (eqToHom pU) m
  rw [eqToHom_trans]

noncomputable def schemeModuleSkyscraperAbPresheafMap
    {X : Scheme.{u}} (x : X)
    {A B : ModuleCat.{u} (X.presheaf.stalk x)} (f : A ⟶ B) :
    schemeModuleSkyscraperAbPresheaf x A ⟶
      schemeModuleSkyscraperAbPresheaf x B :=
  (skyscraperPresheafFunctor x).map
    ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map f)

@[simp]
theorem schemeModuleSkyscraperAbPresheafMap_id
    {X : Scheme.{u}} (x : X)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) :
    schemeModuleSkyscraperAbPresheafMap x (𝟙 A) = 𝟙 _ := by
  unfold schemeModuleSkyscraperAbPresheafMap
  rw [(forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map_id,
    (skyscraperPresheafFunctor x).map_id]
  rfl

@[simp]
theorem schemeModuleSkyscraperAbPresheafMap_comp
    {X : Scheme.{u}} (x : X)
    {A B C : ModuleCat.{u} (X.presheaf.stalk x)}
    (f : A ⟶ B) (g : B ⟶ C) :
    schemeModuleSkyscraperAbPresheafMap x (f ≫ g) =
      schemeModuleSkyscraperAbPresheafMap x f ≫
        schemeModuleSkyscraperAbPresheafMap x g := by
  unfold schemeModuleSkyscraperAbPresheafMap
  rw [(forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map_comp,
    (skyscraperPresheafFunctor x).map_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem schemeModuleSkyscraperAbPresheafAddEquivOfMem_map_moduleHom
    {X : Scheme.{u}} (x : X)
    {A B : ModuleCat.{u} (X.presheaf.stalk x)} (f : A ⟶ B)
    (U : X.Opens) (hx : x ∈ U)
    (m : (schemeModuleSkyscraperAbPresheaf x A).obj (op U)) :
    schemeModuleSkyscraperAbPresheafAddEquivOfMem x B U hx
        ((schemeModuleSkyscraperAbPresheafMap x f).app (op U) m) =
      f (schemeModuleSkyscraperAbPresheafAddEquivOfMem x A U hx m) := by
  change ConcreteCategory.hom
      ((schemeModuleSkyscraperAbPresheafMap x f).app (op U) ≫
        (schemeModuleSkyscraperAbPresheafIsoOfMem x B U hx).hom) m =
    ConcreteCategory.hom
      ((schemeModuleSkyscraperAbPresheafIsoOfMem x A U hx).hom ≫
        (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map f) m
  apply ConcreteCategory.congr_hom
  let eA := schemeModuleSkyscraperAbPresheafIsoOfMem x A U hx
  let eB := schemeModuleSkyscraperAbPresheafIsoOfMem x B U hx
  let fAb := (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map f
  have happ : (schemeModuleSkyscraperAbPresheafMap x f).app (op U) =
      eA.hom ≫ fAb ≫ eB.inv := by
    unfold schemeModuleSkyscraperAbPresheafMap
    simp only [skyscraperPresheafFunctor_map,
      SkyscraperPresheafFunctor.map'_app]
    split
    · unfold eA eB schemeModuleSkyscraperAbPresheafIsoOfMem
      congr
    · contradiction
  change (schemeModuleSkyscraperAbPresheafMap x f).app (op U) ≫ eB.hom =
    eA.hom ≫ fAb
  rw [happ, Category.assoc, Category.assoc, eB.inv_hom_id,
    Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem schemeModuleSkyscraperAbPresheafMap_smul
    {X : Scheme.{u}} (x : X)
    {A B : ModuleCat.{u} (X.presheaf.stalk x)} (f : A ⟶ B)
    (U : X.Opens) (r : Γ(X, U))
    (m : (schemeModuleSkyscraperAbPresheaf x A).obj (op U)) :
    letI := schemeModuleSkyscraperAbPresheaf_module x A (op U)
    letI := schemeModuleSkyscraperAbPresheaf_module x B (op U)
    (schemeModuleSkyscraperAbPresheafMap x f).app (op U) (r • m) =
      r • (schemeModuleSkyscraperAbPresheafMap x f).app (op U) m := by
  dsimp
  by_cases hx : x ∈ U
  · apply (schemeModuleSkyscraperAbPresheafAddEquivOfMem x B U hx).injective
    rw [schemeModuleSkyscraperAbPresheafAddEquivOfMem_map_moduleHom,
      schemeModuleSkyscraperAbPresheafAddEquivOfMem_smul,
      schemeModuleSkyscraperAbPresheafAddEquivOfMem_smul,
      schemeModuleSkyscraperAbPresheafAddEquivOfMem_map_moduleHom]
    exact f.hom.map_smul _ _
  · have hzero : IsZero ((schemeModuleSkyscraperAbPresheaf x B).obj (op U)) := by
      let hterminal : IsZero (⊤_ AddCommGrpCat.{u}) :=
        (isZero_zero AddCommGrpCat.{u}).of_iso
          ((isZero_zero AddCommGrpCat.{u}).isoIsTerminal terminalIsTerminal).symm
      exact hterminal.of_iso
        (eqToIso (by simp [schemeModuleSkyscraperAbPresheaf, hx]))
    exact @Subsingleton.elim _
      (AddCommGrpCat.subsingleton_of_isZero hzero) _ _

def schemeModuleSkyscraperPresheaf
    {X : Scheme.{u}} (x : X)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) :
    PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) := by
  letI : ∀ U : X.Opensᵒᵖ,
      Module ((X.presheaf ⋙ forget₂ CommRingCat RingCat).obj U)
        ((schemeModuleSkyscraperAbPresheaf x A).obj U) := fun U ↦ by
    change Module (X.presheaf.obj U)
      ((schemeModuleSkyscraperAbPresheaf x A).obj U)
    exact schemeModuleSkyscraperAbPresheaf_module x A U
  apply PresheafOfModules.ofPresheaf (schemeModuleSkyscraperAbPresheaf x A)
  intro U V f r m
  by_cases hV : x ∈ V.unop
  · apply (schemeModuleSkyscraperAbPresheafAddEquivOfMem
      x A V.unop hV).injective
    rw [schemeModuleSkyscraperAbPresheafAddEquivOfMem_map,
      schemeModuleSkyscraperAbPresheafAddEquivOfMem_smul,
      schemeModuleSkyscraperAbPresheafAddEquivOfMem_smul,
      schemeModuleSkyscraperAbPresheafAddEquivOfMem_map]
    change X.presheaf.germ U.unop x (f.unop.le hV) r • _ =
      X.presheaf.germ V.unop x hV (X.presheaf.map f r) • _
    rw [X.presheaf.germ_res_apply' f x hV r]
  · have hzero : IsZero ((schemeModuleSkyscraperAbPresheaf x A).obj V) := by
      let hterminal : IsZero (⊤_ AddCommGrpCat.{u}) :=
        (isZero_zero AddCommGrpCat.{u}).of_iso
          ((isZero_zero AddCommGrpCat.{u}).isoIsTerminal terminalIsTerminal).symm
      exact hterminal.of_iso
        (eqToIso (by simp [schemeModuleSkyscraperAbPresheaf, hV]))
    exact @Subsingleton.elim _
      (AddCommGrpCat.subsingleton_of_isZero hzero) _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable def schemeModuleSkyscraperPresheafMap
    {X : Scheme.{u}} (x : X)
    {A B : ModuleCat.{u} (X.presheaf.stalk x)} (f : A ⟶ B) :
    schemeModuleSkyscraperPresheaf x A ⟶
      schemeModuleSkyscraperPresheaf x B := by
  refine PresheafOfModules.homMk
    (M₁ := schemeModuleSkyscraperPresheaf x A)
    (M₂ := schemeModuleSkyscraperPresheaf x B)
    (schemeModuleSkyscraperAbPresheafMap x f) ?_
  rintro ⟨U⟩ r m
  exact schemeModuleSkyscraperAbPresheafMap_smul x f U r m

/-- The scheme module supported at `x` with prescribed local-ring module
value `A`. -/
noncomputable def schemeModuleSkyscraper
    {X : Scheme.{u}} (x : X)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) : X.Modules where
  val := schemeModuleSkyscraperPresheaf x A
  isSheaf := by
    change (schemeModuleSkyscraperAbPresheaf x A).IsSheaf
    exact skyscraperPresheaf_isSheaf x
      ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj A)

noncomputable def schemeModuleSkyscraperMap
    {X : Scheme.{u}} (x : X)
    {A B : ModuleCat.{u} (X.presheaf.stalk x)} (f : A ⟶ B) :
    schemeModuleSkyscraper x A ⟶ schemeModuleSkyscraper x B where
  val := schemeModuleSkyscraperPresheafMap x f

noncomputable def schemeModuleSkyscraperFunctor
    (X : Scheme.{u}) (x : X) :
    ModuleCat.{u} (X.presheaf.stalk x) ⥤ X.Modules where
  obj A := schemeModuleSkyscraper x A
  map f := schemeModuleSkyscraperMap x f
  map_id A := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (schemeModuleSkyscraperAbPresheafMap x (𝟙 A)).app U m = m
    rw [schemeModuleSkyscraperAbPresheafMap_id]
    rfl
  map_comp f g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (schemeModuleSkyscraperAbPresheafMap x (f ≫ g)).app U m =
      (schemeModuleSkyscraperAbPresheafMap x g).app U
        ((schemeModuleSkyscraperAbPresheafMap x f).app U m)
    rw [schemeModuleSkyscraperAbPresheafMap_comp]
    rfl

@[simp]
theorem schemeModuleSkyscraper_presheaf
    {X : Scheme.{u}} (x : X)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) :
    (schemeModuleSkyscraper x A).presheaf =
      schemeModuleSkyscraperAbPresheaf x A := rfl

set_option linter.style.haveILetI false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable def schemeModuleSkyscraperStalkLinearMap
    {X : Scheme.{u}} (x : X)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) :
    (schemeModuleStalkModuleFunctor X x).obj
        (schemeModuleSkyscraper x A) ⟶ A := by
  letI : Module (X.presheaf.stalk x)
      ((schemeModuleSkyscraper x A).presheaf.stalk x) :=
    schemeModuleStalkModule (schemeModuleSkyscraper x A) x
  letI : Module (X.presheaf.stalk x)
      ((schemeModuleSkyscraperAbPresheaf x A).stalk x) := by
    change Module (X.presheaf.stalk x)
      ((schemeModuleSkyscraper x A).presheaf.stalk x)
    exact schemeModuleStalkModule (schemeModuleSkyscraper x A) x
  letI : Module (X.presheaf.stalk x)
      ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj A) := by
    change Module (X.presheaf.stalk x) A
    infer_instance
  let e : (schemeModuleSkyscraperAbPresheaf x A).stalk x ≅
      (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj A :=
    skyscraperPresheafStalkOfSpecializes x
      ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj A)
      specializes_rfl
  refine ModuleCat.ofHom
    { toFun := e.hom
      map_add' := e.hom.hom.map_add
      map_smul' := ?_ }
  intro a n
  obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq a
  change (schemeModuleSkyscraperAbPresheaf x A).stalk x at n
  obtain ⟨V, hVU, hxV, m, rfl⟩ :=
    TopCat.Presheaf.exists_le_germ_eq
      (schemeModuleSkyscraperAbPresheaf x A) n hxU
  erw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV r]
  change e.hom
      (X.presheaf.germ V x hxV (X.presheaf.map (homOfLE hVU).op r) •
        (schemeModuleSkyscraperAbPresheaf x A).germ V x hxV m) =
    X.presheaf.germ V x hxV (X.presheaf.map (homOfLE hVU).op r) •
      e.hom ((schemeModuleSkyscraperAbPresheaf x A).germ V x hxV m)
  have hgerm := PresheafOfModules.germ_smul
    (schemeModuleSkyscraper x A).val x V hxV
      (X.presheaf.map (homOfLE hVU).op r) m
  change (schemeModuleSkyscraperAbPresheaf x A).germ V x hxV
      ((X.presheaf.map (homOfLE hVU).op r) • m) =
    X.presheaf.germ V x hxV (X.presheaf.map (homOfLE hVU).op r) •
      (schemeModuleSkyscraperAbPresheaf x A).germ V x hxV m at hgerm
  rw [← hgerm]
  change e.hom
      ((schemeModuleSkyscraperAbPresheaf x A).germ V x hxV
        ((X.presheaf.map (homOfLE hVU).op r) • m)) = _
  have he : (schemeModuleSkyscraperAbPresheaf x A).germ V x hxV ≫ e.hom =
      eqToHom (if_pos hxV) := by
    exact germ_skyscraperPresheafStalkOfSpecializes_hom
      (p₀ := x)
      (A := (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj A)
      specializes_rfl V hxV
  rw [← ConcreteCategory.comp_apply, he]
  change schemeModuleSkyscraperAbPresheafAddEquivOfMem x A V hxV
      ((X.presheaf.map (homOfLE hVU).op r) • m) = _
  rw [schemeModuleSkyscraperAbPresheafAddEquivOfMem_smul]
  change _ = X.presheaf.germ V x hxV (X.presheaf.map (homOfLE hVU).op r) • _
  congr 1
  symm
  rw [← ConcreteCategory.comp_apply, he]
  rfl

noncomputable def schemeModuleSkyscraperStalkLinearEquiv
    {X : Scheme.{u}} (x : X)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) :
    ((schemeModuleStalkModuleFunctor X x).obj
        (schemeModuleSkyscraper x A) : Type u) ≃ₗ[X.presheaf.stalk x] A := by
  letI : Module (X.presheaf.stalk x)
      ((schemeModuleSkyscraper x A).presheaf.stalk x) :=
    schemeModuleStalkModule (schemeModuleSkyscraper x A) x
  refine LinearEquiv.ofBijective
    (schemeModuleSkyscraperStalkLinearMap x A).hom ?_
  change Function.Bijective
    (skyscraperPresheafStalkOfSpecializes x
      ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj A)
      specializes_rfl).hom
  exact ConcreteCategory.bijective_of_isIso _

noncomputable def schemeModuleSkyscraperStalkIso
    {X : Scheme.{u}} (x : X)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) :
    (schemeModuleStalkModuleFunctor X x).obj
        (schemeModuleSkyscraper x A) ≅ A :=
  (schemeModuleSkyscraperStalkLinearEquiv x A).toModuleIso

noncomputable def schemeModuleToSkyscraperAbPresheafMap
    {X : Scheme.{u}} (x : X) {M : X.Modules}
    {A : ModuleCat.{u} (X.presheaf.stalk x)}
    (f : (schemeModuleStalkModuleFunctor X x).obj M ⟶ A) :
    M.presheaf ⟶ schemeModuleSkyscraperAbPresheaf x A :=
  StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf x
    ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map f)

set_option linter.style.haveILetI false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem schemeModuleToSkyscraperAbPresheafMap_smul
    {X : Scheme.{u}} (x : X) {M : X.Modules}
    {A : ModuleCat.{u} (X.presheaf.stalk x)}
    (f : (schemeModuleStalkModuleFunctor X x).obj M ⟶ A)
    (U : X.Opens) (r : Γ(X, U)) (m : M.presheaf.obj (op U)) :
    letI := schemeModuleSkyscraperAbPresheaf_module x A (op U)
    (schemeModuleToSkyscraperAbPresheafMap x f).app (op U) (r • m) =
      r • (schemeModuleToSkyscraperAbPresheafMap x f).app (op U) m := by
  dsimp
  letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
    schemeModuleStalkModule M x
  by_cases hx : x ∈ U
  · apply (schemeModuleSkyscraperAbPresheafAddEquivOfMem x A U hx).injective
    have happ (n : M.presheaf.obj (op U)) :
        schemeModuleSkyscraperAbPresheafAddEquivOfMem x A U hx
          ((schemeModuleToSkyscraperAbPresheafMap x f).app (op U) n) =
        f (M.presheaf.germ U x hx n) := by
      unfold schemeModuleSkyscraperAbPresheafAddEquivOfMem
      simp only [schemeModuleToSkyscraperAbPresheafMap,
        StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf_app,
        dif_pos hx, ConcreteCategory.comp_apply]
      let eU := schemeModuleSkyscraperAbPresheafIsoOfMem x A U hx
      have hcancel : eqToHom (if_pos hx).symm ≫ eU.hom = 𝟙 _ := by
        change eU.inv ≫ eU.hom = 𝟙 _
        exact eU.inv_hom_id
      change ConcreteCategory.hom
          (eqToHom (if_pos hx).symm ≫ eU.hom)
          (((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map f)
            (M.presheaf.germ U x hx n)) = _
      rw [hcancel]
      rfl
    rw [schemeModuleSkyscraperAbPresheafAddEquivOfMem_smul]
    rw [happ, happ]
    have hgerm := PresheafOfModules.germ_smul M.val x U hx r m
    change M.presheaf.germ U x hx (r • m) =
      X.presheaf.germ U x hx r • M.presheaf.germ U x hx m at hgerm
    rw [hgerm]
    exact f.hom.map_smul _ _
  · have hzero : IsZero ((schemeModuleSkyscraperAbPresheaf x A).obj (op U)) := by
      let hterminal : IsZero (⊤_ AddCommGrpCat.{u}) :=
        (isZero_zero AddCommGrpCat.{u}).of_iso
          ((isZero_zero AddCommGrpCat.{u}).isoIsTerminal terminalIsTerminal).symm
      exact hterminal.of_iso
        (eqToIso (by simp [schemeModuleSkyscraperAbPresheaf, hx]))
    exact @Subsingleton.elim _
      (AddCommGrpCat.subsingleton_of_isZero hzero) _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable def schemeModuleToSkyscraper
    {X : Scheme.{u}} (x : X) {M : X.Modules}
    {A : ModuleCat.{u} (X.presheaf.stalk x)}
    (f : (schemeModuleStalkModuleFunctor X x).obj M ⟶ A) :
    M ⟶ schemeModuleSkyscraper x A where
  val := by
    refine PresheafOfModules.homMk
      (schemeModuleToSkyscraperAbPresheafMap x f) ?_
    rintro ⟨U⟩ r m
    exact schemeModuleToSkyscraperAbPresheafMap_smul x f U r m

noncomputable def schemeModuleFromSkyscraper
    {X : Scheme.{u}} (x : X) {M : X.Modules}
    {A : ModuleCat.{u} (X.presheaf.stalk x)}
    (g : M ⟶ schemeModuleSkyscraper x A) :
    (schemeModuleStalkModuleFunctor X x).obj M ⟶ A :=
  (schemeModuleStalkModuleFunctor X x).map g ≫
    schemeModuleSkyscraperStalkLinearMap x A

@[simp]
theorem schemeModuleToSkyscraper_forget
    {X : Scheme.{u}} (x : X) {M : X.Modules}
    {A : ModuleCat.{u} (X.presheaf.stalk x)}
    (f : (schemeModuleStalkModuleFunctor X x).obj M ⟶ A) :
    (Scheme.Modules.toPresheaf X).map
        (schemeModuleToSkyscraper x f) =
      schemeModuleToSkyscraperAbPresheafMap x f := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- On an open containing the center, the section of the adjoint skyscraper
map is obtained by applying the local-module morphism to the germ. -/
theorem schemeModuleSkyscraperAbPresheafAddEquivOfMem_toSkyscraper_app
    {X : Scheme.{u}} (x : X) {M : X.Modules}
    {A : ModuleCat.{u} (X.presheaf.stalk x)}
    (f : (schemeModuleStalkModuleFunctor X x).obj M ⟶ A)
    (U : X.Opens) (hx : x ∈ U) (n : M.presheaf.obj (op U)) :
    schemeModuleSkyscraperAbPresheafAddEquivOfMem x A U hx
        ((schemeModuleToSkyscraperAbPresheafMap x f).app (op U) n) =
      f (M.presheaf.germ U x hx n) := by
  unfold schemeModuleSkyscraperAbPresheafAddEquivOfMem
  simp only [schemeModuleToSkyscraperAbPresheafMap,
    StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf_app,
    dif_pos hx, ConcreteCategory.comp_apply]
  let eU := schemeModuleSkyscraperAbPresheafIsoOfMem x A U hx
  have hcancel : eqToHom (if_pos hx).symm ≫ eU.hom = 𝟙 _ := by
    change eU.inv ≫ eU.hom = 𝟙 _
    exact eU.inv_hom_id
  change ConcreteCategory.hom
      (eqToHom (if_pos hx).symm ≫ eU.hom)
      (((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map f)
        (M.presheaf.germ U x hx n)) = _
  rw [hcancel]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem schemeModuleFromSkyscraper_forget
    {X : Scheme.{u}} (x : X) {M : X.Modules}
    {A : ModuleCat.{u} (X.presheaf.stalk x)}
    (g : M ⟶ schemeModuleSkyscraper x A) :
    (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map
        (schemeModuleFromSkyscraper x g) =
      StalkSkyscraperPresheafAdjunctionAuxs.fromStalk x
        ((Scheme.Modules.toPresheaf X).map g) := by
  let e : (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj
        ((Scheme.Modules.toPresheaf X).obj (schemeModuleSkyscraper x A)) ≅
      (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj A :=
    skyscraperPresheafStalkOfSpecializes x
      ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj A)
      specializes_rfl
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((Scheme.Modules.toPresheaf X).map g) ≫ e.hom =
    StalkSkyscraperPresheafAdjunctionAuxs.fromStalk x
      ((Scheme.Modules.toPresheaf X).map g)
  apply ((Scheme.Modules.toPresheaf X).obj M).stalk_hom_ext
  intro U hx
  rw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
  have he : ((Scheme.Modules.toPresheaf X).obj
      (schemeModuleSkyscraper x A)).germ U x hx ≫ e.hom =
      eqToHom (if_pos hx) := by
    exact germ_skyscraperPresheafStalkOfSpecializes_hom
      (p₀ := x)
      (A := (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj A)
      specializes_rfl U hx
  rw [he,
    StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk]

noncomputable def schemeModuleStalkSkyscraperHomEquiv
    {X : Scheme.{u}} (x : X) (M : X.Modules)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) :
    ((schemeModuleStalkModuleFunctor X x).obj M ⟶ A) ≃
      (M ⟶ schemeModuleSkyscraper x A) where
  toFun := schemeModuleToSkyscraper x
  invFun := schemeModuleFromSkyscraper x
  left_inv f := by
    apply (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map_injective
    rw [schemeModuleFromSkyscraper_forget,
      schemeModuleToSkyscraper_forget]
    exact StalkSkyscraperPresheafAdjunctionAuxs.fromStalk_to_skyscraper
      (p₀ := x) (𝓕 := M.presheaf)
      (c := (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj A)
      ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map f)
  right_inv g := by
    apply (Scheme.Modules.toPresheaf X).map_injective
    rw [schemeModuleToSkyscraper_forget]
    change StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf x
        ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map
          (schemeModuleFromSkyscraper x g)) =
      (Scheme.Modules.toPresheaf X).map g
    rw [schemeModuleFromSkyscraper_forget]
    exact StalkSkyscraperPresheafAdjunctionAuxs.to_skyscraper_fromStalk
      (p₀ := x) (𝓕 := (Scheme.Modules.toPresheaf X).obj M)
      (c := (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj A)
      ((Scheme.Modules.toPresheaf X).map g)

theorem schemeModuleFromSkyscraper_comp
    {X : Scheme.{u}} (x : X) {M N : X.Modules}
    {A : ModuleCat.{u} (X.presheaf.stalk x)}
    (a : M ⟶ N) (g : N ⟶ schemeModuleSkyscraper x A) :
    schemeModuleFromSkyscraper x (a ≫ g) =
      (schemeModuleStalkModuleFunctor X x).map a ≫
        schemeModuleFromSkyscraper x g := by
  unfold schemeModuleFromSkyscraper
  rw [(schemeModuleStalkModuleFunctor X x).map_comp, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem schemeModuleToSkyscraper_comp
    {X : Scheme.{u}} (x : X) {M : X.Modules}
    {A B : ModuleCat.{u} (X.presheaf.stalk x)}
    (f : (schemeModuleStalkModuleFunctor X x).obj M ⟶ A) (g : A ⟶ B) :
    schemeModuleToSkyscraper x (f ≫ g) =
      schemeModuleToSkyscraper x f ≫ schemeModuleSkyscraperMap x g := by
  apply (Scheme.Modules.toPresheaf X).map_injective
  rw [(Scheme.Modules.toPresheaf X).map_comp,
    schemeModuleToSkyscraper_forget,
    schemeModuleToSkyscraper_forget]
  change StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf x
      ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map (f ≫ g)) =
    schemeModuleToSkyscraperAbPresheafMap x f ≫
      schemeModuleSkyscraperAbPresheafMap x g
  rw [(forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map_comp]
  apply NatTrans.ext
  funext U
  dsimp [schemeModuleToSkyscraperAbPresheafMap,
    schemeModuleSkyscraperAbPresheafMap,
    StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf]
  by_cases h : x ∈ U.unop
  · simp only [dif_pos h, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
  · apply ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext

set_option linter.style.haveILetI false in
/-- Naturality of the canonical identification between the stalk of a
scheme-module skyscraper and its prescribed local module. -/
theorem schemeModuleSkyscraperStalkLinearMap_naturality
    {X : Scheme.{u}} (x : X)
    {A B : ModuleCat.{u} (X.presheaf.stalk x)} (f : A ⟶ B) :
    (schemeModuleStalkModuleFunctor X x).map
        (schemeModuleSkyscraperMap x f) ≫
      schemeModuleSkyscraperStalkLinearMap x B =
    schemeModuleSkyscraperStalkLinearMap x A ≫ f := by
  let e := schemeModuleStalkSkyscraperHomEquiv x
    (schemeModuleSkyscraper x A) B
  change e.symm (schemeModuleSkyscraperMap x f) =
    schemeModuleSkyscraperStalkLinearMap x A ≫ f
  apply e.injective
  rw [e.apply_symm_apply]
  symm
  change schemeModuleToSkyscraper x
      (schemeModuleSkyscraperStalkLinearMap x A ≫ f) = _
  rw [schemeModuleToSkyscraper_comp]
  let eA := schemeModuleStalkSkyscraperHomEquiv x
    (schemeModuleSkyscraper x A) A
  have hc : eA.invFun (𝟙 _) =
      schemeModuleSkyscraperStalkLinearMap x A := by
    dsimp [eA, schemeModuleStalkSkyscraperHomEquiv,
      schemeModuleFromSkyscraper]
    rw [(schemeModuleStalkModuleFunctor X x).map_id, Category.id_comp]
  have hunit : schemeModuleToSkyscraper x
      (schemeModuleSkyscraperStalkLinearMap x A) = 𝟙 _ := by
    rw [← hc]
    exact eA.apply_symm_apply (𝟙 _)
  rw [hunit, Category.id_comp]

/-- Taking the central stalk after forming a scheme-module skyscraper is
naturally isomorphic to the identity functor on local modules. -/
noncomputable def schemeModuleSkyscraperStalkNatIso
    (X : Scheme.{u}) (x : X) :
    schemeModuleSkyscraperFunctor X x ⋙
        schemeModuleStalkModuleFunctor X x ≅
      𝟭 (ModuleCat (X.presheaf.stalk x)) :=
  NatIso.ofComponents
    (fun A => schemeModuleSkyscraperStalkIso x A)
    (fun f => schemeModuleSkyscraperStalkLinearMap_naturality x f)

/-- On underlying additive groups, the central stalk of the scheme-module
skyscraper is naturally isomorphic to the original local module. -/
noncomputable def schemeModuleSkyscraperStalkAbNatIso
    (X : Scheme.{u}) (x : X) :
    schemeModuleSkyscraperFunctor X x ⋙ schemeModuleStalkFunctor X x ≅
      forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat :=
  Functor.isoWhiskerRight (schemeModuleSkyscraperStalkNatIso X x)
    (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat)

set_option linter.style.haveILetI false in
/-- Away from every specialization of the center, a scheme-module
skyscraper has zero stalk. -/
theorem schemeModuleSkyscraper_stalk_isZero_of_not_specializes
    {X : Scheme.{u}} (x y : X) (hxy : ¬ x ⤳ y)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) :
    IsZero ((schemeModuleStalkFunctor X y).obj
      (schemeModuleSkyscraper x A)) := by
  classical
  letI : (U : X.Opens) → Decidable (x ∈ U) := fun U ↦ Classical.dec _
  change IsZero ((schemeModuleSkyscraperAbPresheaf x A).stalk y)
  exact (skyscraperPresheafStalkOfNotSpecializesIsTerminal x
    ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj A)
    hxy).isZero


noncomputable def schemeModuleStalkSkyscraperCoreHomEquiv
    (X : Scheme.{u}) (x : X) :
    Adjunction.CoreHomEquiv
      (schemeModuleStalkModuleFunctor X x)
      (schemeModuleSkyscraperFunctor X x) where
  homEquiv M A := schemeModuleStalkSkyscraperHomEquiv x M A
  homEquiv_naturality_left_symm a g :=
    schemeModuleFromSkyscraper_comp x a g
  homEquiv_naturality_right f g :=
    schemeModuleToSkyscraper_comp x f g

noncomputable def schemeModuleStalkSkyscraperAdjunction
    (X : Scheme.{u}) (x : X) :
    schemeModuleStalkModuleFunctor X x ⊣
      schemeModuleSkyscraperFunctor X x :=
  Adjunction.mkOfHomEquiv
    (schemeModuleStalkSkyscraperCoreHomEquiv X x)

/-- The unit of the stalk--skyscraper adjunction is the canonical map from a
scheme module to the skyscraper of its stalk. -/
theorem schemeModuleStalkSkyscraperAdjunction_unit_app
    {X : Scheme.{u}} (x : X) (N : X.Modules) :
    (schemeModuleStalkSkyscraperAdjunction X x).unit.app N =
      schemeModuleToSkyscraper x
        (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N)) := by
  rfl

/-- The counit of the stalk--skyscraper adjunction is the canonical central
stalk isomorphism. -/
theorem schemeModuleStalkSkyscraperAdjunction_counit_app
    {X : Scheme.{u}} (x : X)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) :
    (schemeModuleStalkSkyscraperAdjunction X x).counit.app A =
      schemeModuleSkyscraperStalkLinearMap x A := by
  change schemeModuleFromSkyscraper x (𝟙 _) = _
  unfold schemeModuleFromSkyscraper
  rw [(schemeModuleStalkModuleFunctor X x).map_id, Category.id_comp]
  rfl

/-- The scheme-module skyscraper functor is fully faithful. -/
noncomputable def schemeModuleSkyscraperFunctorFullyFaithful
    (X : Scheme.{u}) (x : X) :
    (schemeModuleSkyscraperFunctor X x).FullyFaithful :=
  (schemeModuleStalkSkyscraperAdjunction X x).fullyFaithfulROfCompIsoId
    (schemeModuleSkyscraperStalkNatIso X x)

noncomputable instance (X : Scheme.{u}) (x : X) :
    (schemeModuleSkyscraperFunctor X x).Additive :=
  (schemeModuleStalkSkyscraperAdjunction X x).right_adjoint_additive

noncomputable instance (X : Scheme.{u}) (x : X) :
    (schemeModuleSkyscraperFunctor X x).IsRightAdjoint :=
  (schemeModuleStalkSkyscraperAdjunction X x).isRightAdjoint

set_option linter.style.haveILetI false in
/-- At a closed point, the scheme-module skyscraper functor preserves
exactness.  At the center this is the natural stalk identification; every
other stalk is zero because the center is closed. -/
theorem schemeModuleSkyscraperFunctor_map_exact
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    (S : ShortComplex (ModuleCat (X.presheaf.stalk x))) (hS : S.Exact) :
    (S.map (schemeModuleSkyscraperFunctor X x)).Exact := by
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  letI : T.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive T
  apply Functor.reflects_exact_of_faithful T
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr
  intro y
  let U := TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
  letI : U.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive U
  change ((S.map (schemeModuleSkyscraperFunctor X x)).map
    (schemeModuleStalkFunctor X y)).Exact
  by_cases hy : y = x
  · subst y
    let e := ShortComplex.mapNatIso S
      (schemeModuleSkyscraperStalkAbNatIso X x)
    apply ShortComplex.exact_of_iso e.symm
    rw [ShortComplex.ab_exact_iff_function_exact]
    change Function.Exact S.f S.g
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS
  · apply ShortComplex.exact_of_isZero_X₂
    apply schemeModuleSkyscraper_stalk_isZero_of_not_specializes x y
    exact hx.not_specializes (Set.mem_singleton x)
      (by simpa [Set.mem_singleton_iff, eq_comm] using hy)

/-- At a closed point, the skyscraper functor preserves homology. -/
theorem schemeModuleSkyscraperFunctorPreservesHomology
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X)) :
    (schemeModuleSkyscraperFunctor X x).PreservesHomology :=
  Functor.preservesHomology_of_map_exact
    (schemeModuleSkyscraperFunctor X x)
    (schemeModuleSkyscraperFunctor_map_exact x hx)

set_option linter.style.haveILetI false in
/-- At a closed point, the skyscraper functor preserves finite limits. -/
theorem schemeModuleSkyscraperFunctorPreservesFiniteLimits
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X)) :
    PreservesFiniteLimits (schemeModuleSkyscraperFunctor X x) := by
  letI := schemeModuleSkyscraperFunctorPreservesHomology x hx
  exact Functor.preservesFiniteLimits_of_preservesHomology
    (schemeModuleSkyscraperFunctor X x)

set_option linter.style.haveILetI false in
/-- At a closed point, the skyscraper functor preserves finite colimits. -/
theorem schemeModuleSkyscraperFunctorPreservesFiniteColimits
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X)) :
    PreservesFiniteColimits (schemeModuleSkyscraperFunctor X x) := by
  letI := schemeModuleSkyscraperFunctorPreservesHomology x hx
  exact Functor.preservesFiniteColimits_of_preservesHomology
    (schemeModuleSkyscraperFunctor X x)


/-- Because taking a module stalk preserves monomorphisms, its right-adjoint
skyscraper functor sends injective local modules to injective scheme modules. -/
noncomputable instance (X : Scheme.{u}) (x : X) :
    (schemeModuleSkyscraperFunctor X x).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (schemeModuleStalkSkyscraperAdjunction X x)

theorem schemeModuleSkyscraper_injective
    {X : Scheme.{u}} (x : X)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) [Injective A] :
    Injective (schemeModuleSkyscraper x A) :=
  (schemeModuleSkyscraperFunctor X x).injective_obj_of_injective inferInstance

set_option linter.style.haveILetI false in
/-- The raw stalk map on morphisms into a scheme-module skyscraper is
bijective.  The adjunction gives the same comparison followed by the
canonical isomorphism from the skyscraper stalk to its value. -/
theorem schemeModuleStalkModuleFunctor_map_bijective_to_skyscraper
    {X : Scheme.{u}} (x : X) (M : X.Modules)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) :
    Function.Bijective
      (fun f : M ⟶ schemeModuleSkyscraper x A ↦
        (schemeModuleStalkModuleFunctor X x).map f) := by
  let c := schemeModuleSkyscraperStalkLinearMap x A
  have hc : IsIso c := (schemeModuleSkyscraperStalkIso x A).isIso_hom
  letI : IsIso c := hc
  constructor
  · intro f g hfg
    apply (schemeModuleStalkSkyscraperHomEquiv x M A).symm.injective
    change (schemeModuleStalkModuleFunctor X x).map f ≫ c =
      (schemeModuleStalkModuleFunctor X x).map g ≫ c
    change (schemeModuleStalkModuleFunctor X x).map f =
      (schemeModuleStalkModuleFunctor X x).map g at hfg
    rw [hfg]
  · intro h
    refine ⟨schemeModuleToSkyscraper x (h ≫ c), ?_⟩
    apply (cancel_mono c).1
    change schemeModuleFromSkyscraper x
      (schemeModuleToSkyscraper x (h ≫ c)) = h ≫ c
    exact (schemeModuleStalkSkyscraperHomEquiv x M A).left_inv (h ≫ c)

/-- If the local value is injective, the stalk of its scheme-module
skyscraper is injective as well. -/
theorem schemeModuleSkyscraper_stalk_injective
    {X : Scheme.{u}} (x : X)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) [Injective A] :
    Injective ((schemeModuleStalkModuleFunctor X x).obj
      (schemeModuleSkyscraper x A)) :=
  Injective.of_iso (schemeModuleSkyscraperStalkIso x A).symm inferInstance

set_option linter.style.haveILetI false in
/-- The adjunction unit from a scheme module to the skyscraper of its stalk
becomes an isomorphism after taking the stalk at the center. -/
theorem schemeModuleToSkyscraper_stalk_isIso
    {X : Scheme.{u}} (x : X) (N : X.Modules) :
    IsIso ((schemeModuleStalkModuleFunctor X x).map
      (schemeModuleToSkyscraper x
        (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N)))) := by
  let f := schemeModuleToSkyscraper x
    (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N))
  let c := schemeModuleSkyscraperStalkLinearMap x
    ((schemeModuleStalkModuleFunctor X x).obj N)
  have hc : IsIso c :=
    (schemeModuleSkyscraperStalkIso x
      ((schemeModuleStalkModuleFunctor X x).obj N)).isIso_hom
  letI : IsIso c := hc
  have hcomp : (schemeModuleStalkModuleFunctor X x).map f ≫ c = 𝟙 _ := by
    exact (schemeModuleStalkSkyscraperHomEquiv x N
      ((schemeModuleStalkModuleFunctor X x).obj N)).left_inv (𝟙 _)
  haveI : IsIso ((schemeModuleStalkModuleFunctor X x).map f ≫ c) := by
    rw [hcomp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ c

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- At a closed point, the adjunction unit from a scheme module to the
skyscraper of its stalk is an epimorphism.  At the distinguished point its
stalk is an isomorphism; at every other point the target stalk is zero.

This is the target-side exact sequence needed to reduce the remaining
point-supported Ext comparison to the kernel away from the point. -/
theorem schemeModuleToSkyscraper_epi_of_isClosed
    {X : Scheme.{u}} (x : X) (N : X.Modules)
    (hx : IsClosed ({x} : Set X)) :
    Epi (schemeModuleToSkyscraper x
      (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N))) := by
  classical
  let f := schemeModuleToSkyscraper x
    (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N))
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have hsurj : ∀ y : X, Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
        ((T.map f).hom)) := by
    intro y
    by_cases hy : y = x
    · subst y
      letI : IsIso ((schemeModuleStalkModuleFunctor X x).map f) :=
        schemeModuleToSkyscraper_stalk_isIso x N
      exact (ConcreteCategory.bijective_of_isIso
        ((schemeModuleStalkModuleFunctor X x).map f)).surjective
    · have hnot : ¬ x ⤳ y :=
        hx.not_specializes (by simp) (by simpa using hy)
      have htgt : IsZero
          ((schemeModuleSkyscraper x
            ((schemeModuleStalkModuleFunctor X x).obj N)).presheaf.stalk y) :=
        (skyscraperPresheafStalkOfNotSpecializesIsTerminal x
          ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj
            ((schemeModuleStalkModuleFunctor X x).obj N)) hnot).isZero
      intro z
      refine ⟨0, ?_⟩
      exact (AddCommGrpCat.subsingleton_of_isZero htgt).elim _ _
  have hloc : TopCat.Presheaf.IsLocallySurjective ((T.map f).hom) :=
    (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
      ((T.map f).hom)).mpr hsurj
  have hsheafEpi : Epi (T.map f) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi (T.map f)).mp hloc
  letI : Epi (T.map f) := hsheafEpi
  exact (Functor.reflectsEpimorphisms_of_faithful T).reflects f inferInstance

set_option linter.style.haveILetI false in
/-- The kernel of the map to the skyscraper of the stalk has zero stalk at
the center.  Thus this kernel is precisely the off-point term whose Ext
vanishing controls the global-to-local comparison. -/
theorem schemeModuleToSkyscraper_kernel_stalk_isZero
    {X : Scheme.{u}} (x : X) (N : X.Modules) :
    IsZero ((schemeModuleStalkModuleFunctor X x).obj
      (kernel (schemeModuleToSkyscraper x
        (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N))))) := by
  let f := schemeModuleToSkyscraper x
    (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N))
  let F := schemeModuleStalkModuleFunctor X x
  letI : IsIso (F.map f) := schemeModuleToSkyscraper_stalk_isIso x N
  have hz : IsZero (kernel (F.map f)) := isZero_kernel_of_mono (F.map f)
  exact hz.of_iso (PreservesKernel.iso F f)

set_option linter.style.haveILetI false in
/-- Away from every specialization of the center, the kernel of the
canonical map to the skyscraper has the same stalk as the original module.
Together with `schemeModuleToSkyscraper_kernel_stalk_isZero`, this identifies
the kernel as the part of the module supported off the center. -/
theorem schemeModuleToSkyscraper_kernel_ι_stalk_isIso_of_not_specializes
    {X : Scheme.{u}} (x y : X) (hxy : ¬ x ⤳ y) (N : X.Modules) :
    IsIso ((schemeModuleStalkModuleFunctor X y).map
      (kernel.ι (schemeModuleToSkyscraper x
        (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N))))) := by
  let f := schemeModuleToSkyscraper x
    (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N))
  let F := schemeModuleStalkModuleFunctor X y
  have hzAb :=
    schemeModuleSkyscraper_stalk_isZero_of_not_specializes x y hxy
      ((schemeModuleStalkModuleFunctor X x).obj N)
  letI : Subsingleton
      ((schemeModuleSkyscraper x
        ((schemeModuleStalkModuleFunctor X x).obj N)).presheaf.stalk y) :=
    AddCommGrpCat.subsingleton_of_isZero hzAb
  letI : Subsingleton (F.obj (schemeModuleSkyscraper x
      ((schemeModuleStalkModuleFunctor X x).obj N))) := by
    change Subsingleton
      ((schemeModuleSkyscraper x
        ((schemeModuleStalkModuleFunctor X x).obj N)).presheaf.stalk y)
    infer_instance
  have hf : F.map f = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact Subsingleton.elim _ _
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hE : (S.map F).Exact := (ShortComplex.exact_kernel f).map F
  have hFg : (S.map F).g = 0 := by
    change F.map f = 0
    exact hf
  have hepi : Epi (F.map (kernel.ι f)) := by
    exact ((S.map F).exact_iff_epi hFg).mp hE
  letI : Epi (F.map (kernel.ι f)) := hepi
  exact isIso_of_mono_of_epi _

/-- At a closed center, the preceding off-specialization comparison applies
at every distinct point. -/
theorem schemeModuleToSkyscraper_kernel_ι_stalk_isIso_of_ne
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    (y : X) (hy : y ≠ x) (N : X.Modules) :
    IsIso ((schemeModuleStalkModuleFunctor X y).map
      (kernel.ι (schemeModuleToSkyscraper x
        (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N))))) :=
  schemeModuleToSkyscraper_kernel_ι_stalk_isIso_of_not_specializes
    x y (hx.not_specializes (Set.mem_singleton x)
      (by simpa [Set.mem_singleton_iff, eq_comm] using hy)) N

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
theorem schemeModuleToSkyscraper_isIso_of_subsingleton_off
    {X : Scheme.{u}} (x : X) (M : X.Modules)
    (hx : IsClosed ({x} : Set X))
    (hM : ∀ y : X, y ≠ x → Subsingleton (M.presheaf.stalk y)) :
    IsIso (schemeModuleToSkyscraper x
      (𝟙 ((schemeModuleStalkModuleFunctor X x).obj M))) := by
  letI : ∀ U : X.Opens, Decidable (x ∈ U) := fun U ↦ Classical.dec _
  let f := schemeModuleToSkyscraper x
    (𝟙 ((schemeModuleStalkModuleFunctor X x).obj M))
  suffices IsIso ((Scheme.Modules.toPresheaf X).map f) by
    exact isIso_of_reflects_iso f (Scheme.Modules.toPresheaf X)
  have hsheaf : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map f) := by
    letI (y : X) : IsIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map f).hom) := by
      have hmod : IsIso ((schemeModuleStalkModuleFunctor X y).map f) := by
        by_cases hy : y = x
        · subst y
          let c := schemeModuleSkyscraperStalkLinearMap x
            ((schemeModuleStalkModuleFunctor X x).obj M)
          have hc : IsIso c :=
            (schemeModuleSkyscraperStalkIso x
              ((schemeModuleStalkModuleFunctor X x).obj M)).isIso_hom
          letI : IsIso c := hc
          have hcomp : (schemeModuleStalkModuleFunctor X x).map f ≫ c = 𝟙 _ := by
            exact (schemeModuleStalkSkyscraperHomEquiv x M
              ((schemeModuleStalkModuleFunctor X x).obj M)).left_inv (𝟙 _)
          haveI : IsIso ((schemeModuleStalkModuleFunctor X x).map f ≫ c) := by
            rw [hcomp]
            infer_instance
          exact IsIso.of_isIso_comp_right _ c
        · have hnot : ¬ x ⤳ y :=
            hx.not_specializes (by simp) (by simpa using hy)
          let src := (schemeModuleStalkModuleFunctor X y).obj M
          let tgt := (schemeModuleStalkModuleFunctor X y).obj
            (schemeModuleSkyscraper x
              ((schemeModuleStalkModuleFunctor X x).obj M))
          have hsrcSub : Subsingleton src := by
            change Subsingleton (M.presheaf.stalk y)
            exact hM y hy
          letI : Subsingleton src := hsrcSub
          have hsrc : IsZero src := ModuleCat.isZero_of_subsingleton src
          have htgtAdd : IsZero
              ((schemeModuleSkyscraper x
                ((schemeModuleStalkModuleFunctor X x).obj M)).presheaf.stalk y) :=
            (skyscraperPresheafStalkOfNotSpecializesIsTerminal x
              ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj
                ((schemeModuleStalkModuleFunctor X x).obj M)) hnot).isZero
          have htgtSub : Subsingleton tgt := by
            change Subsingleton
              ((schemeModuleSkyscraper x
                ((schemeModuleStalkModuleFunctor X x).obj M)).presheaf.stalk y)
            exact AddCommGrpCat.subsingleton_of_isZero htgtAdd
          letI : Subsingleton tgt := htgtSub
          have htgt : IsZero tgt := ModuleCat.isZero_of_subsingleton tgt
          let e : src ≅ tgt := hsrc.iso htgt
          have he : (schemeModuleStalkModuleFunctor X y).map f = e.hom :=
            hsrc.eq_of_src _ _
          rw [he]
          infer_instance
      letI : IsIso ((schemeModuleStalkModuleFunctor X y).map f) := hmod
      exact Functor.map_isIso
        (forget₂ (ModuleCat (X.presheaf.stalk y)) AddCommGrpCat)
        ((schemeModuleStalkModuleFunctor X y).map f)
    exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _
  letI : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map f) := hsheaf
  letI (U : (Opens X)ᵒᵖ) :
      IsIso (((Scheme.Modules.toPresheaf X).map f).app U) := by
    change IsIso (((SheafOfModules.toSheaf X.ringCatSheaf).map f).hom.app U)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end

end PfaffianDescent
