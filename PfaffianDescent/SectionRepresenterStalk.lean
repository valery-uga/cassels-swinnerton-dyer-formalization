import PfaffianDescent.SectionRepresenterScalar
import PfaffianDescent.SchemeModuleSkyscraper

/-!
# Stalks of section representers

At a point contained in an open `U`, the stalk of the sheaf representing
sections on `U` is a free rank-one module over the local ring.  The proof uses
the stalk--skyscraper adjunction and the defining Yoneda property of the
section representer.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace PfaffianDescent

universe u

variable (X : Scheme.{u})

/-- The germ of the universal section is the canonical generator of the
section-representer stalk. -/
noncomputable def sectionRepresenterStalkGenerator
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    ((schemeModuleStalkModuleFunctor X x).obj
      (show X.Modules from sectionRepresenter X.ringCatSheaf U) : Type u) :=
  (show X.Modules from sectionRepresenter X.ringCatSheaf U).presheaf.germ U x hx
    (sectionRepresenterGenerator X.ringCatSheaf U)

/-- The local ring maps to the section-representer stalk by sending `1` to
the universal germ. -/
noncomputable def sectionRepresenterStalkGeneratorHom
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) ⟶
      (schemeModuleStalkModuleFunctor X x).obj
        (sectionRepresenter X.ringCatSheaf U) := by
  let P : X.Modules := sectionRepresenter X.ringCatSheaf U
  letI : Module (X.presheaf.stalk x) (P.presheaf.stalk x) :=
    schemeModuleStalkModule P x
  exact ModuleCat.ofHom <|
    (LinearMap.ringLmapEquivSelf (X.presheaf.stalk x)
      (X.presheaf.stalk x) (P.presheaf.stalk x)).symm
        (sectionRepresenterStalkGenerator X U x hx)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem sectionRepresenterStalkGeneratorHom_apply_one
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    sectionRepresenterStalkGeneratorHom X U x hx (1 : X.presheaf.stalk x) =
      sectionRepresenterStalkGenerator X U x hx := by
  let P : X.Modules := sectionRepresenter X.ringCatSheaf U
  letI : Module (X.presheaf.stalk x) (P.presheaf.stalk x) :=
    schemeModuleStalkModule P x
  change ((LinearMap.ringLmapEquivSelf (X.presheaf.stalk x)
      (X.presheaf.stalk x) (P.presheaf.stalk x)).symm
        (sectionRepresenterStalkGenerator X U x hx)) 1 = _
  exact (LinearEquiv.apply_symm_apply
    (LinearMap.ringLmapEquivSelf (X.presheaf.stalk x)
      (X.presheaf.stalk x) (P.presheaf.stalk x))
    (sectionRepresenterStalkGenerator X U x hx))

/-- Maps from the section-representer stalk are evaluated on its universal
germ.  This equivalence is assembled from the stalk--skyscraper adjunction
and the section-representer Yoneda equivalence. -/
noncomputable def sectionRepresenterStalkHomEquiv
    (U : X.Opens) (x : X) (hx : x ∈ U)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) :
    ((schemeModuleStalkModuleFunctor X x).obj
        (sectionRepresenter X.ringCatSheaf U) ⟶ A) ≃ A :=
  (schemeModuleStalkSkyscraperHomEquiv x
      (sectionRepresenter X.ringCatSheaf U) A).trans <|
    (sectionRepresenterHomEquiv X.ringCatSheaf U
      (schemeModuleSkyscraper x A)).trans <|
      (schemeModuleSkyscraperAbPresheafAddEquivOfMem x A U hx).toEquiv

set_option backward.isDefEq.respectTransparency false in
theorem sectionRepresenterStalkHomEquiv_apply
    (U : X.Opens) (x : X) (hx : x ∈ U)
    (A : ModuleCat.{u} (X.presheaf.stalk x))
    (g : (schemeModuleStalkModuleFunctor X x).obj
        (sectionRepresenter X.ringCatSheaf U) ⟶ A) :
    sectionRepresenterStalkHomEquiv X U x hx A g =
      g (sectionRepresenterStalkGenerator X U x hx) := by
  change schemeModuleSkyscraperAbPresheafAddEquivOfMem x A U hx
      (sectionRepresenterHomEquiv X.ringCatSheaf U
        (schemeModuleSkyscraper x A) (schemeModuleToSkyscraper x g)) = _
  rw [← sectionRepresenterHom_apply_generator X.ringCatSheaf U]
  change schemeModuleSkyscraperAbPresheafAddEquivOfMem x A U hx
      ((schemeModuleToSkyscraperAbPresheafMap x g).app (op U)
        (sectionRepresenterGenerator X.ringCatSheaf U)) = _
  exact schemeModuleSkyscraperAbPresheafAddEquivOfMem_toSkyscraper_app
    x g U hx (sectionRepresenterGenerator X.ringCatSheaf U)

theorem sectionRepresenterStalkGeneratorHom_comp_coordinate
    (U : X.Opens) (x : X) (hx : x ∈ U)
    (A : ModuleCat.{u} (X.presheaf.stalk x))
    (g : (schemeModuleStalkModuleFunctor X x).obj
        (sectionRepresenter X.ringCatSheaf U) ⟶ A) :
    (LinearMap.ringLmapEquivSelf (X.presheaf.stalk x)
      (X.presheaf.stalk x) A)
        (sectionRepresenterStalkGeneratorHom X U x hx ≫ g).hom =
      g (sectionRepresenterStalkGenerator X U x hx) := by
  change g (sectionRepresenterStalkGeneratorHom X U x hx 1) = _
  rw [sectionRepresenterStalkGeneratorHom_apply_one]

/-- The generator map from the local ring to the stalk is an isomorphism. -/
noncomputable def sectionRepresenterStalkIso
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) ≅
      (schemeModuleStalkModuleFunctor X x).obj
        (sectionRepresenter X.ringCatSheaf U) := by
  let f := sectionRepresenterStalkGeneratorHom X U x hx
  letI : IsIso f := isIso_of_coyoneda_map_bijective f (fun A ↦ by
    constructor
    · intro g h hgh
      apply (sectionRepresenterStalkHomEquiv X U x hx A).injective
      rw [sectionRepresenterStalkHomEquiv_apply,
        sectionRepresenterStalkHomEquiv_apply]
      have hc := congrArg
        (fun k : ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) ⟶ A ↦
          (LinearMap.ringLmapEquivSelf (X.presheaf.stalk x)
            (X.presheaf.stalk x) A) k.hom) hgh
      rw [sectionRepresenterStalkGeneratorHom_comp_coordinate,
        sectionRepresenterStalkGeneratorHom_comp_coordinate] at hc
      exact hc
    · intro h
      let E := sectionRepresenterStalkHomEquiv X U x hx A
      let e := LinearMap.ringLmapEquivSelf (X.presheaf.stalk x)
        (X.presheaf.stalk x) A
      let g : (schemeModuleStalkModuleFunctor X x).obj
          (sectionRepresenter X.ringCatSheaf U) ⟶ A := E.symm (e h.hom)
      refine ⟨g, ?_⟩
      apply ModuleCat.hom_ext
      apply e.injective
      rw [sectionRepresenterStalkGeneratorHom_comp_coordinate,
        ← sectionRepresenterStalkHomEquiv_apply]
      exact E.apply_symm_apply (e h.hom))
  exact asIso f

set_option backward.isDefEq.respectTransparency false in
/-- The stalk of a section augmentation sends the universal germ to the
germ of its coefficient section. -/
theorem sectionRepresenterAugmentation_stalk_generator
    (U : X.Opens) (x : X) (hx : x ∈ U)
    (Y : X.Modules) (y : Γ(Y, U)) :
    (schemeModuleStalkModuleFunctor X x).map
        (sectionRepresenterAugmentation X.ringCatSheaf U Y y)
        (sectionRepresenterStalkGenerator X U x hx) =
      Y.presheaf.germ U x hx y := by
  change (schemeModuleStalkFunctor X x).map
      (sectionRepresenterAugmentation X.ringCatSheaf U Y y)
      ((show X.Modules from sectionRepresenter X.ringCatSheaf U).presheaf.germ
        U x hx (sectionRepresenterGenerator X.ringCatSheaf U)) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change Y.presheaf.germ U x hx
      ((sectionRepresenterAugmentation X.ringCatSheaf U Y y).val.app
        (op U) (sectionRepresenterGenerator X.ringCatSheaf U)) = _
  rw [sectionRepresenterHom_apply_generator,
    sectionRepresenterHomEquiv_augmentation]

set_option backward.isDefEq.respectTransparency false in
/-- On the universal stalk generator, the stalk of a scalar endomorphism is
multiplication by the germ of that scalar. -/
theorem sectionRepresenterScalarEndomorphism_stalk_generator
    (U : X.Opens) (x : X) (hx : x ∈ U) (a : Γ(X, U)) :
    (schemeModuleStalkModuleFunctor X x).map
        (sectionRepresenterScalarEndomorphism X.ringCatSheaf U a)
        (sectionRepresenterStalkGenerator X U x hx) =
      X.presheaf.germ U x hx a •
        sectionRepresenterStalkGenerator X U x hx := by
  change (schemeModuleStalkFunctor X x).map
      (sectionRepresenterScalarEndomorphism X.ringCatSheaf U a)
      ((show X.Modules from sectionRepresenter X.ringCatSheaf U).presheaf.germ
        U x hx (sectionRepresenterGenerator X.ringCatSheaf U)) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change (show X.Modules from sectionRepresenter X.ringCatSheaf U).presheaf.germ
      U x hx
      ((sectionRepresenterScalarEndomorphism X.ringCatSheaf U a).val.app
        (op U) (sectionRepresenterGenerator X.ringCatSheaf U)) = _
  rw [sectionRepresenterHom_apply_generator,
    sectionRepresenterHomEquiv_scalarEndomorphism]
  exact PresheafOfModules.germ_smul
    (show X.Modules from sectionRepresenter X.ringCatSheaf U).val
    x U hx a (sectionRepresenterGenerator X.ringCatSheaf U)

@[simp]
theorem sectionRepresenterStalkIso_hom
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    (sectionRepresenterStalkIso X U x hx).hom =
      sectionRepresenterStalkGeneratorHom X U x hx := by
  rfl

theorem sectionRepresenterStalkGeneratorHom_precomp_scalar_coordinate
    (U : X.Opens) (x : X) (hx : x ∈ U)
    (r : X.presheaf.stalk x) :
    (LinearMap.ringLmapEquivSelf (X.presheaf.stalk x)
      (X.presheaf.stalk x)
      ((schemeModuleStalkModuleFunctor X x).obj
        (sectionRepresenter X.ringCatSheaf U)))
        ((r • 𝟙 (ModuleCat.of (X.presheaf.stalk x)
          (X.presheaf.stalk x))) ≫
            sectionRepresenterStalkGeneratorHom X U x hx).hom =
      r • sectionRepresenterStalkGenerator X U x hx := by
  change sectionRepresenterStalkGeneratorHom X U x hx (r • 1) = _
  rw [map_smul, sectionRepresenterStalkGeneratorHom_apply_one]

/-- The stalk isomorphism conjugates the global scalar endomorphism to scalar
multiplication by the corresponding local germ. -/
theorem sectionRepresenterStalkIso_hom_naturality_scalar
    (U : X.Opens) (x : X) (hx : x ∈ U) (a : Γ(X, U)) :
    (X.presheaf.germ U x hx a •
        𝟙 (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))) ≫
        (sectionRepresenterStalkIso X U x hx).hom =
      (sectionRepresenterStalkIso X U x hx).hom ≫
        (schemeModuleStalkModuleFunctor X x).map
          (sectionRepresenterScalarEndomorphism X.ringCatSheaf U a) := by
  rw [sectionRepresenterStalkIso_hom]
  apply ModuleCat.hom_ext
  apply (LinearMap.ringLmapEquivSelf (X.presheaf.stalk x)
    (X.presheaf.stalk x)
    ((schemeModuleStalkModuleFunctor X x).obj
      (sectionRepresenter X.ringCatSheaf U))).injective
  rw [sectionRepresenterStalkGeneratorHom_precomp_scalar_coordinate,
    sectionRepresenterStalkGeneratorHom_comp_coordinate,
    sectionRepresenterScalarEndomorphism_stalk_generator]

/-- Maps from the section-representer stalk at a point outside `U` are
equivalent to sections over `U` of the corresponding skyscraper.  The latter
object is zero because its center does not lie in `U`. -/
noncomputable def sectionRepresenterStalkHomEquivOutside
    (U : X.Opens) (x : X)
    (A : ModuleCat.{u} (X.presheaf.stalk x)) :
    ((schemeModuleStalkModuleFunctor X x).obj
        (sectionRepresenter X.ringCatSheaf U) ⟶ A) ≃
      (schemeModuleSkyscraper x A).val.obj (op U) :=
  (schemeModuleStalkSkyscraperHomEquiv x
      (sectionRepresenter X.ringCatSheaf U) A).trans
    (sectionRepresenterHomEquiv X.ringCatSheaf U
      (schemeModuleSkyscraper x A))

/-- Outside the represented open, the stalk of the section representer is
zero. -/
theorem sectionRepresenterStalk_isZero_of_not_mem
    (U : X.Opens) (x : X) (hx : x ∉ U) :
    IsZero ((schemeModuleStalkModuleFunctor X x).obj
      (sectionRepresenter X.ringCatSheaf U)) := by
  let P := (schemeModuleStalkModuleFunctor X x).obj
    (sectionRepresenter X.ringCatSheaf U)
  let E := sectionRepresenterStalkHomEquivOutside X U x P
  apply (IsZero.iff_id_eq_zero P).mpr
  apply E.injective
  have hsub : Subsingleton
      ((schemeModuleSkyscraper x P).val.obj (op U) : Type u) := by
    change Subsingleton
      ((schemeModuleSkyscraperAbPresheaf x P).obj (op U) : Type u)
    simp [schemeModuleSkyscraperAbPresheaf, hx]
    exact AddCommGrpCat.subsingleton_of_isZero <|
      (isZero_zero AddCommGrpCat.{u}).of_iso
        ((isZero_zero AddCommGrpCat.{u}).isoIsTerminal
          terminalIsTerminal).symm
  exact @Subsingleton.elim _ hsub _ _

end PfaffianDescent
