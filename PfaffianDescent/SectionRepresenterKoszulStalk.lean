import PfaffianDescent.SectionRepresenterStalk
import PfaffianDescent.SectionRepresenterKoszul
import PfaffianDescent.TwoGeneratorKoszul
import PfaffianDescent.SchemeModuleStalkMono
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Pi

/-!
# Stalkwise form of the section-representer Koszul complex

On a point of the represented open, the two middle summands identify with
two copies of the local ring.  Under this identification the global
section-representer differentials are the ordinary two-generator Koszul
maps.  Outside the open all three stalks vanish.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped nonZeroDivisors

namespace PfaffianDescent

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

universe u

variable (X : Scheme.{u})

noncomputable local instance : HasFiniteBiproducts X.Modules :=
  CategoryTheory.Abelian.hasFiniteBiproducts

noncomputable local instance (x : X) :
    (schemeModuleStalkModuleFunctor X x).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

noncomputable local instance sectionRepresenterPairHasBiproduct
    (U : X.Opens) :
    HasBiproduct (fun _ : Fin 2 ↦
      (show X.Modules from sectionRepresenter X.ringCatSheaf U)) :=
  (CategoryTheory.Abelian.hasFiniteBiproducts (C := X.Modules)).out 2 |>.has_biproduct _

noncomputable abbrev sectionRepresenterKoszulPairObject (U : X.Opens) :
    X.Modules :=
  ⨁ fun _ : Fin 2 ↦
    (show X.Modules from sectionRepresenter X.ringCatSheaf U)

/-- The stalk of the two-summand section-representer term, written as the
ordinary product of two copies of the local ring. -/
noncomputable def sectionRepresenterKoszulPairStalkIso
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    (schemeModuleStalkModuleFunctor X x).obj
        (sectionRepresenterKoszulPairObject X U) ≅
      ModuleCat.of (X.presheaf.stalk x)
        (X.presheaf.stalk x × X.presheaf.stalk x) := by
  let F := schemeModuleStalkModuleFunctor X x
  let P : Fin 2 → X.Modules := sectionRepresenterKoszulPair X.ringCatSheaf U
  let Q : Fin 2 → ModuleCat (X.presheaf.stalk x) :=
    fun _ ↦ ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)
  letI : PreservesBiproduct P F := by infer_instance
  exact F.mapBiproduct P ≪≫
    biproduct.mapIso (fun _ ↦ (sectionRepresenterStalkIso X U x hx).symm) ≪≫
    ModuleCat.biproductIsoPi Q ≪≫
    (LinearEquiv.piFinTwo (X.presheaf.stalk x)
      (fun _ : Fin 2 ↦ X.presheaf.stalk x)).toModuleIso

private theorem ModuleCat.biproductIsoPi_hom_comp_proj
    {R : Type u} [Ring R] {J : Type} [Finite J]
    (Q : J → ModuleCat.{u} R) (j : J) :
    (ModuleCat.biproductIsoPi Q).hom ≫
        ModuleCat.ofHom (LinearMap.proj j :
          ((i : J) → Q i) →ₗ[R] Q j) =
      biproduct.π Q j := by
  rw [← cancel_epi (ModuleCat.biproductIsoPi Q).inv]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem sectionRepresenterKoszulPairStalkIso_hom_comp_fst
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    (sectionRepresenterKoszulPairStalkIso X U x hx).hom ≫
        ModuleCat.ofHom (LinearMap.fst (X.presheaf.stalk x)
          (X.presheaf.stalk x) (X.presheaf.stalk x)) =
      (schemeModuleStalkModuleFunctor X x).map
          (biproduct.π (sectionRepresenterKoszulPair X.ringCatSheaf U) 0) ≫
        (sectionRepresenterStalkIso X U x hx).inv := by
  simp only [sectionRepresenterKoszulPairStalkIso, Iso.trans_hom,
    Category.assoc]
  rw [show (LinearEquiv.piFinTwo (X.presheaf.stalk x)
        (fun _ : Fin 2 ↦ X.presheaf.stalk x)).toModuleIso.hom ≫
        ModuleCat.ofHom (LinearMap.fst (X.presheaf.stalk x)
          (X.presheaf.stalk x) (X.presheaf.stalk x)) =
      ModuleCat.ofHom (LinearMap.proj 0 :
        ((i : Fin 2) → X.presheaf.stalk x) →ₗ[X.presheaf.stalk x]
          X.presheaf.stalk x) by rfl,
    ModuleCat.biproductIsoPi_hom_comp_proj]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem sectionRepresenterKoszulPairStalkIso_hom_comp_snd
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    (sectionRepresenterKoszulPairStalkIso X U x hx).hom ≫
        ModuleCat.ofHom (LinearMap.snd (X.presheaf.stalk x)
          (X.presheaf.stalk x) (X.presheaf.stalk x)) =
      (schemeModuleStalkModuleFunctor X x).map
          (biproduct.π (sectionRepresenterKoszulPair X.ringCatSheaf U) 1) ≫
        (sectionRepresenterStalkIso X U x hx).inv := by
  simp only [sectionRepresenterKoszulPairStalkIso, Iso.trans_hom,
    Category.assoc]
  rw [show (LinearEquiv.piFinTwo (X.presheaf.stalk x)
        (fun _ : Fin 2 ↦ X.presheaf.stalk x)).toModuleIso.hom ≫
        ModuleCat.ofHom (LinearMap.snd (X.presheaf.stalk x)
          (X.presheaf.stalk x) (X.presheaf.stalk x)) =
      ModuleCat.ofHom (LinearMap.proj 1 :
        ((i : Fin 2) → X.presheaf.stalk x) →ₗ[X.presheaf.stalk x]
          X.presheaf.stalk x) by rfl,
    ModuleCat.biproductIsoPi_hom_comp_proj]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem sectionRepresenterKoszulPairStalkIso_inl_comp_inv
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    ModuleCat.ofHom (LinearMap.inl (X.presheaf.stalk x)
        (X.presheaf.stalk x) (X.presheaf.stalk x)) ≫
        (sectionRepresenterKoszulPairStalkIso X U x hx).inv =
      (sectionRepresenterStalkIso X U x hx).hom ≫
        (schemeModuleStalkModuleFunctor X x).map
          (biproduct.ι (sectionRepresenterKoszulPair X.ringCatSheaf U) 0) := by
  rw [← cancel_mono (sectionRepresenterKoszulPairStalkIso X U x hx).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  apply Prod.ext
  · change r = (((sectionRepresenterStalkIso X U x hx).hom ≫
        (schemeModuleStalkModuleFunctor X x).map
          (biproduct.ι (sectionRepresenterKoszulPair X.ringCatSheaf U) 0) ≫
        (sectionRepresenterKoszulPairStalkIso X U x hx).hom) ≫
          ModuleCat.ofHom (LinearMap.fst (X.presheaf.stalk x)
            (X.presheaf.stalk x) (X.presheaf.stalk x))) r
    simp only [Category.assoc]
    rw [sectionRepresenterKoszulPairStalkIso_hom_comp_fst]
    simp only [← Category.assoc, ← Functor.map_comp]
    simp
    rw [← sectionRepresenterStalkIso_hom]
    have h := ConcreteCategory.congr_hom
      (sectionRepresenterStalkIso X U x hx).hom_inv_id r
    exact h.symm
  · change 0 = (((sectionRepresenterStalkIso X U x hx).hom ≫
        (schemeModuleStalkModuleFunctor X x).map
          (biproduct.ι (sectionRepresenterKoszulPair X.ringCatSheaf U) 0) ≫
        (sectionRepresenterKoszulPairStalkIso X U x hx).hom) ≫
          ModuleCat.ofHom (LinearMap.snd (X.presheaf.stalk x)
            (X.presheaf.stalk x) (X.presheaf.stalk x))) r
    simp only [Category.assoc]
    rw [sectionRepresenterKoszulPairStalkIso_hom_comp_snd]
    simp only [← Category.assoc, ← Functor.map_comp]
    simp

set_option backward.isDefEq.respectTransparency false in
theorem sectionRepresenterKoszulPairStalkIso_inr_comp_inv
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    ModuleCat.ofHom (LinearMap.inr (X.presheaf.stalk x)
        (X.presheaf.stalk x) (X.presheaf.stalk x)) ≫
        (sectionRepresenterKoszulPairStalkIso X U x hx).inv =
      (sectionRepresenterStalkIso X U x hx).hom ≫
        (schemeModuleStalkModuleFunctor X x).map
          (biproduct.ι (sectionRepresenterKoszulPair X.ringCatSheaf U) 1) := by
  rw [← cancel_mono (sectionRepresenterKoszulPairStalkIso X U x hx).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  apply Prod.ext
  · change 0 = (((sectionRepresenterStalkIso X U x hx).hom ≫
        (schemeModuleStalkModuleFunctor X x).map
          (biproduct.ι (sectionRepresenterKoszulPair X.ringCatSheaf U) 1) ≫
        (sectionRepresenterKoszulPairStalkIso X U x hx).hom) ≫
          ModuleCat.ofHom (LinearMap.fst (X.presheaf.stalk x)
            (X.presheaf.stalk x) (X.presheaf.stalk x))) r
    simp only [Category.assoc]
    rw [sectionRepresenterKoszulPairStalkIso_hom_comp_fst]
    simp only [← Category.assoc, ← Functor.map_comp]
    simp
  · change r = (((sectionRepresenterStalkIso X U x hx).hom ≫
        (schemeModuleStalkModuleFunctor X x).map
          (biproduct.ι (sectionRepresenterKoszulPair X.ringCatSheaf U) 1) ≫
        (sectionRepresenterKoszulPairStalkIso X U x hx).hom) ≫
          ModuleCat.ofHom (LinearMap.snd (X.presheaf.stalk x)
            (X.presheaf.stalk x) (X.presheaf.stalk x))) r
    simp only [Category.assoc]
    rw [sectionRepresenterKoszulPairStalkIso_hom_comp_snd]
    simp only [← Category.assoc, ← Functor.map_comp]
    simp
    rw [← sectionRepresenterStalkIso_hom]
    have h := ConcreteCategory.congr_hom
      (sectionRepresenterStalkIso X U x hx).hom_inv_id r
    exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- At a point of `U`, the stalk of the first global Koszul differential is
the ordinary first two-generator Koszul map. -/
theorem sectionRepresenterKoszulFirst_stalk_conjugacy
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U)) :
    (sectionRepresenterStalkIso X U x hx).hom ≫
        (schemeModuleStalkModuleFunctor X x).map
          (sectionRepresenterKoszulFirst X.ringCatSheaf U q f) ≫
        (sectionRepresenterKoszulPairStalkIso X U x hx).hom =
      ModuleCat.ofHom (twoGeneratorFirst
        (X.presheaf.germ U x hx q) (X.presheaf.germ U x hx f)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  simp only [twoGeneratorFirst]
  apply Prod.ext
  · change (ModuleCat.ofHom (LinearMap.fst (X.presheaf.stalk x)
        (X.presheaf.stalk x) (X.presheaf.stalk x)))
      (((sectionRepresenterStalkIso X U x hx).hom ≫
        (schemeModuleStalkModuleFunctor X x).map
          (sectionRepresenterKoszulFirst X.ringCatSheaf U q f) ≫
        (sectionRepresenterKoszulPairStalkIso X U x hx).hom) r) = _
    rw [← ConcreteCategory.comp_apply]
    simp only [Category.assoc]
    rw [sectionRepresenterKoszulPairStalkIso_hom_comp_fst]
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [sectionRepresenterKoszulFirst, biproduct.lift_π]
    simp only [Matrix.cons_val_zero]
    rw [← sectionRepresenterStalkIso_hom_naturality_scalar]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simp [twoGeneratorFirst]
  · change (ModuleCat.ofHom (LinearMap.snd (X.presheaf.stalk x)
        (X.presheaf.stalk x) (X.presheaf.stalk x)))
      (((sectionRepresenterStalkIso X U x hx).hom ≫
        (schemeModuleStalkModuleFunctor X x).map
          (sectionRepresenterKoszulFirst X.ringCatSheaf U q f) ≫
        (sectionRepresenterKoszulPairStalkIso X U x hx).hom) r) = _
    rw [← ConcreteCategory.comp_apply]
    simp only [Category.assoc]
    rw [sectionRepresenterKoszulPairStalkIso_hom_comp_snd]
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [sectionRepresenterKoszulFirst, biproduct.lift_π]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [← sectionRepresenterStalkIso_hom_naturality_scalar]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simp [twoGeneratorFirst]

set_option backward.isDefEq.respectTransparency false in
/-- At a point of `U`, the stalk of the last global Koszul differential is
the ordinary last two-generator Koszul map. -/
theorem sectionRepresenterKoszulLast_stalk_conjugacy
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U)) :
    (sectionRepresenterKoszulPairStalkIso X U x hx).inv ≫
        (schemeModuleStalkModuleFunctor X x).map
          (sectionRepresenterKoszulLast X.ringCatSheaf U q f) ≫
        (sectionRepresenterStalkIso X U x hx).inv =
      ModuleCat.ofHom (twoGeneratorLast
        (X.presheaf.germ U x hx q) (X.presheaf.germ U x hx f)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.prod_ext
  · have hcat :
        ModuleCat.ofHom (LinearMap.inl (X.presheaf.stalk x)
            (X.presheaf.stalk x) (X.presheaf.stalk x)) ≫
          ((sectionRepresenterKoszulPairStalkIso X U x hx).inv ≫
            (schemeModuleStalkModuleFunctor X x).map
              (sectionRepresenterKoszulLast X.ringCatSheaf U q f) ≫
            (sectionRepresenterStalkIso X U x hx).inv) =
        ModuleCat.ofHom (LinearMap.inl (X.presheaf.stalk x)
            (X.presheaf.stalk x) (X.presheaf.stalk x)) ≫
          ModuleCat.ofHom (twoGeneratorLast
            (X.presheaf.germ U x hx q)
            (X.presheaf.germ U x hx f)) := by
      rw [← Category.assoc]
      rw [sectionRepresenterKoszulPairStalkIso_inl_comp_inv]
      simp only [Category.assoc, ← Functor.map_comp_assoc]
      rw [sectionRepresenterKoszulLast, biproduct.ι_desc]
      simp only [Matrix.cons_val_zero]
      rw [← Category.assoc]
      rw [← sectionRepresenterStalkIso_hom_naturality_scalar]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      apply ModuleCat.hom_ext
      ext r
      simp [twoGeneratorLast]
    exact congrArg ModuleCat.Hom.hom hcat
  · have hcat :
        ModuleCat.ofHom (LinearMap.inr (X.presheaf.stalk x)
            (X.presheaf.stalk x) (X.presheaf.stalk x)) ≫
          ((sectionRepresenterKoszulPairStalkIso X U x hx).inv ≫
            (schemeModuleStalkModuleFunctor X x).map
              (sectionRepresenterKoszulLast X.ringCatSheaf U q f) ≫
            (sectionRepresenterStalkIso X U x hx).inv) =
        ModuleCat.ofHom (LinearMap.inr (X.presheaf.stalk x)
            (X.presheaf.stalk x) (X.presheaf.stalk x)) ≫
          ModuleCat.ofHom (twoGeneratorLast
            (X.presheaf.germ U x hx q)
            (X.presheaf.germ U x hx f)) := by
      rw [← Category.assoc]
      rw [sectionRepresenterKoszulPairStalkIso_inr_comp_inv]
      simp only [Category.assoc, ← Functor.map_comp_assoc]
      rw [sectionRepresenterKoszulLast, biproduct.ι_desc]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [← Category.assoc]
      rw [← sectionRepresenterStalkIso_hom_naturality_scalar]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      apply ModuleCat.hom_ext
      ext r
      simp [twoGeneratorLast]
    exact congrArg ModuleCat.Hom.hom hcat

/-- The ordinary two-generator Koszul short complex in a module category. -/
noncomputable def twoGeneratorModuleShortComplex
    (R : Type u) [CommRing R] (q f : R) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    (ModuleCat.ofHom (twoGeneratorFirst q f))
    (ModuleCat.ofHom (twoGeneratorLast q f)) (by
      apply ModuleCat.hom_ext
      exact twoGenerator_comp_zero q f)

/-- Relatively prime generators in a decomposition domain give an exact
ordinary Koszul short complex. -/
theorem twoGeneratorModuleShortComplex_exact
    {R : Type u} [CommRing R] [IsDomain R] [DecompositionMonoid R]
    {q f : R} (hq : q ≠ 0) (hrel : IsRelPrime q f) :
    (twoGeneratorModuleShortComplex R q f).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact twoGenerator_exact hq hrel

/-- The section-representer Koszul complex after taking the local-module
stalk. -/
noncomputable def sectionRepresenterKoszulStalkShortComplex
    (U : X.Opens) (x : X) (q f : Γ(X, U)) :
    ShortComplex (ModuleCat.{u} (X.presheaf.stalk x)) := by
  let F := schemeModuleStalkModuleFunctor X x
  let pzero : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  exact @ShortComplex.map _ _ _ _ _ _
    (sectionRepresenterKoszulShortComplex X.ringCatSheaf U q f
      (Commute.all q f)) F pzero

set_option backward.isDefEq.respectTransparency false in
/-- At a point of `U`, the stalked section-representer Koszul complex is
isomorphic to the ordinary local-ring Koszul complex. -/
noncomputable def sectionRepresenterKoszulStalkShortComplexIso
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U)) :
    sectionRepresenterKoszulStalkShortComplex X U x q f ≅
      twoGeneratorModuleShortComplex (X.presheaf.stalk x)
        (X.presheaf.germ U x hx q) (X.presheaf.germ U x hx f) := by
  refine ShortComplex.isoMk
    (sectionRepresenterStalkIso X U x hx).symm
    (sectionRepresenterKoszulPairStalkIso X U x hx)
    (sectionRepresenterStalkIso X U x hx).symm ?_ ?_
  all_goals dsimp [sectionRepresenterKoszulStalkShortComplex]
  · rw [← cancel_epi (sectionRepresenterStalkIso X U x hx).hom]
    simp only [Iso.hom_inv_id_assoc]
    exact (sectionRepresenterKoszulFirst_stalk_conjugacy X U x hx q f).symm
  · rw [← cancel_epi (sectionRepresenterKoszulPairStalkIso X U x hx).inv]
    simp only [Iso.inv_hom_id_assoc]
    exact (sectionRepresenterKoszulLast_stalk_conjugacy X U x hx q f).symm

/-- Local relative primality of the two germs proves exactness of the
stalked global Koszul complex at a point of `U`. -/
theorem sectionRepresenterKoszul_stalk_exact_of_mem
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U))
    [IsDomain (X.presheaf.stalk x)]
    [DecompositionMonoid (X.presheaf.stalk x)]
    (hq : X.presheaf.germ U x hx q ≠ 0)
    (hrel : IsRelPrime (X.presheaf.germ U x hx q)
      (X.presheaf.germ U x hx f)) :
    (sectionRepresenterKoszulStalkShortComplex X U x q f).Exact := by
  apply ShortComplex.exact_of_iso
    (sectionRepresenterKoszulStalkShortComplexIso X U x hx q f).symm
  exact twoGeneratorModuleShortComplex_exact hq hrel

/-- Without assuming that the point lies in `U`, the stalk of the two middle
summands is the product of the two individual stalks. -/
noncomputable def sectionRepresenterKoszulPairStalkIsoPi
    (U : X.Opens) (x : X) :
    (schemeModuleStalkModuleFunctor X x).obj
        (sectionRepresenterKoszulPairObject X U) ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((i : Fin 2) →
          (schemeModuleStalkModuleFunctor X x).obj
            (sectionRepresenter X.ringCatSheaf U)) := by
  let F := schemeModuleStalkModuleFunctor X x
  let P : Fin 2 → X.Modules := sectionRepresenterKoszulPair X.ringCatSheaf U
  letI : PreservesBiproduct P F := by infer_instance
  exact F.mapBiproduct P ≪≫ ModuleCat.biproductIsoPi (F.obj ∘ P)

/-- At a point outside `U`, the stalk of the two-summand middle term is
zero. -/
theorem sectionRepresenterKoszulPairStalk_isZero_of_not_mem
    (U : X.Opens) (x : X) (hx : x ∉ U) :
    IsZero ((schemeModuleStalkModuleFunctor X x).obj
      (sectionRepresenterKoszulPairObject X U)) := by
  let e := sectionRepresenterKoszulPairStalkIsoPi X U x
  apply e.isZero_iff.mpr
  rw [ModuleCat.isZero_iff_subsingleton]
  let hzero := sectionRepresenterStalk_isZero_of_not_mem X U x hx
  letI : Subsingleton
      ((schemeModuleStalkModuleFunctor X x).obj
        (sectionRepresenter X.ringCatSheaf U) : Type u) :=
    ModuleCat.subsingleton_of_isZero hzero
  constructor
  intro a b
  funext i
  exact Subsingleton.elim _ _

/-- Outside `U`, the stalked Koszul short complex is exact because its
middle object is zero. -/
theorem sectionRepresenterKoszul_stalk_exact_of_not_mem
    (U : X.Opens) (x : X) (hx : x ∉ U) (q f : Γ(X, U)) :
    (sectionRepresenterKoszulStalkShortComplex X U x q f).Exact := by
  apply ShortComplex.exact_of_isZero_X₂
  dsimp [sectionRepresenterKoszulStalkShortComplex]
  exact sectionRepresenterKoszulPairStalk_isZero_of_not_mem X U x hx

set_option linter.style.haveILetI false in
/-- If the two germs form a relatively prime pair at every point of `U`, the
global section-representer Koszul short complex is exact.  Points outside
`U` contribute the zero complex. -/
theorem sectionRepresenterKoszul_exact
    (U : X.Opens) (q f : Γ(X, U))
    (hdom : ∀ (x : X) (hx : x ∈ U), IsDomain (X.presheaf.stalk x))
    (hdecomp : ∀ (x : X) (hx : x ∈ U),
      DecompositionMonoid (X.presheaf.stalk x))
    (hq : ∀ (x : X) (hx : x ∈ U),
      X.presheaf.germ U x hx q ≠ 0)
    (hrel : ∀ (x : X) (hx : x ∈ U),
      IsRelPrime (X.presheaf.germ U x hx q)
        (X.presheaf.germ U x hx f)) :
    (sectionRepresenterKoszulShortComplex X.ringCatSheaf U q f
      (Commute.all q f)).Exact := by
  let S := sectionRepresenterKoszulShortComplex X.ringCatSheaf U q f
    (Commute.all q f)
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  letI : T.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive T
  apply Functor.reflects_exact_of_faithful T
  let pzeroT : T.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive T
  let ST := @ShortComplex.map _ _ _ _ _ _ S T pzeroT
  change ST.Exact
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact ST).mpr
  intro x
  let A := TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  letI : A.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive A
  let F := schemeModuleStalkFunctor X x
  let pzeroF : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive F
  let SF := @ShortComplex.map _ _ _ _ _ _ S F pzeroF
  change SF.Exact
  have hlocal : (sectionRepresenterKoszulStalkShortComplex X U x q f).Exact := by
    by_cases hx : x ∈ U
    · letI : IsDomain (X.presheaf.stalk x) := hdom x hx
      letI : DecompositionMonoid (X.presheaf.stalk x) := hdecomp x hx
      exact sectionRepresenterKoszul_stalk_exact_of_mem X U x hx q f
        (hq x hx) (hrel x hx)
    · exact sectionRepresenterKoszul_stalk_exact_of_not_mem X U x hx q f
  rw [ShortComplex.ab_exact_iff_function_exact]
  change Function.Exact
    (sectionRepresenterKoszulStalkShortComplex X U x q f).f
    (sectionRepresenterKoszulStalkShortComplex X U x q f).g
  exact
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (sectionRepresenterKoszulStalkShortComplex X U x q f)).mp hlocal

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Nonvanishing of the first local generator on `U` makes the first global
Koszul differential monic.  Outside `U` its source stalk is zero. -/
theorem sectionRepresenterKoszulFirst_mono
    (U : X.Opens) (q f : Γ(X, U))
    (hdom : ∀ (x : X) (hx : x ∈ U), IsDomain (X.presheaf.stalk x))
    (hdecomp : ∀ (x : X) (hx : x ∈ U),
      DecompositionMonoid (X.presheaf.stalk x))
    (hq : ∀ (x : X) (hx : x ∈ U),
      X.presheaf.germ U x hx q ≠ 0) :
    Mono (sectionRepresenterKoszulFirst X.ringCatSheaf U q f) := by
  apply schemeModule_mono_of_stalk_mono
  intro x
  by_cases hx : x ∈ U
  · letI : IsDomain (X.presheaf.stalk x) := hdom x hx
    letI : DecompositionMonoid (X.presheaf.stalk x) := hdecomp x hx
    let Q := sectionRepresenterStalkIso X U x hx
    let P := sectionRepresenterKoszulPairStalkIso X U x hx
    let s := (schemeModuleStalkModuleFunctor X x).map
      (sectionRepresenterKoszulFirst X.ringCatSheaf U q f)
    let t := ModuleCat.ofHom (twoGeneratorFirst
      (X.presheaf.germ U x hx q) (X.presheaf.germ U x hx f))
    letI : Mono t := (ModuleCat.mono_iff_injective t).mpr
      (twoGeneratorFirst_injective (hq x hx))
    have hconj := sectionRepresenterKoszulFirst_stalk_conjugacy
      X U x hx q f
    have hs : s = Q.inv ≫ t ≫ P.inv := by
      apply (cancel_epi Q.hom).1
      apply (cancel_mono P.hom).1
      simp only [Category.assoc, Iso.hom_inv_id_assoc,
        Iso.inv_hom_id, Category.comp_id]
      exact hconj
    haveI : Mono s := by rw [hs]; infer_instance
    change Mono ((forget₂ (ModuleCat (X.presheaf.stalk x))
      AddCommGrpCat).map s)
    infer_instance
  · rw [AddCommGrpCat.mono_iff_injective]
    intro a b _
    let hzero := sectionRepresenterStalk_isZero_of_not_mem X U x hx
    letI : Subsingleton
        ((schemeModuleStalkModuleFunctor X x).obj
          (sectionRepresenter X.ringCatSheaf U) : Type u) :=
      ModuleCat.subsingleton_of_isZero hzero
    exact @Subsingleton.elim _
      (ModuleCat.subsingleton_of_isZero hzero) a b

/-- A regular parameter pair gives an exact ordinary Koszul short complex. -/
theorem twoGeneratorModuleShortComplex_exact_of_regular
    {R : Type u} [CommRing R] {q f : R} (hq : q ∈ R⁰)
    (hf : Ideal.Quotient.mk (Ideal.span {q}) f ∈ (R ⧸ Ideal.span {q})⁰) :
    (twoGeneratorModuleShortComplex R q f).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact twoGenerator_exact_of_regular hq hf

/-- Away from the common-zero locus, the ordinary Koszul complex is exact. -/
theorem twoGeneratorModuleShortComplex_exact_of_span_eq_top
    {R : Type u} [CommRing R] {q f : R}
    (hspan : Ideal.span ({q, f} : Set R) = ⊤) :
    (twoGeneratorModuleShortComplex R q f).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact twoGenerator_exact_of_span_eq_top hspan

set_option linter.style.haveILetI false in
/-- A regular pair at the supported point and a unit ideal elsewhere prove
global Koszul exactness, without domain or decomposition assumptions. -/
theorem sectionRepresenterKoszul_exact_of_regularPairAtPoint
    (U : X.Opens) (q f : Γ(X, U))
    (x₀ : X) (hx₀ : x₀ ∈ U)
    (hqreg : X.presheaf.germ U x₀ hx₀ q ∈ (X.presheaf.stalk x₀)⁰)
    (hfreg : Ideal.Quotient.mk (Ideal.span {X.presheaf.germ U x₀ hx₀ q})
        (X.presheaf.germ U x₀ hx₀ f) ∈
      ((X.presheaf.stalk x₀) ⧸ Ideal.span {X.presheaf.germ U x₀ hx₀ q})⁰)
    (hspan : ∀ (x : X) (hx : x ∈ U), x ≠ x₀ →
      Ideal.span ({X.presheaf.germ U x hx q,
        X.presheaf.germ U x hx f} : Set (X.presheaf.stalk x)) = ⊤) :
    (sectionRepresenterKoszulShortComplex X.ringCatSheaf U q f
      (Commute.all q f)).Exact := by
  let S := sectionRepresenterKoszulShortComplex X.ringCatSheaf U q f
    (Commute.all q f)
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  letI : T.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive T
  apply Functor.reflects_exact_of_faithful T
  let pzeroT : T.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive T
  let ST := @ShortComplex.map _ _ _ _ _ _ S T pzeroT
  change ST.Exact
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact ST).mpr
  intro x
  let A := TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  letI : A.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive A
  let F := schemeModuleStalkFunctor X x
  let pzeroF : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive F
  let SF := @ShortComplex.map _ _ _ _ _ _ S F pzeroF
  change SF.Exact
  have hlocal : (sectionRepresenterKoszulStalkShortComplex X U x q f).Exact := by
    by_cases hx : x ∈ U
    · apply ShortComplex.exact_of_iso
        (sectionRepresenterKoszulStalkShortComplexIso X U x hx q f).symm
      by_cases hxx : x = x₀
      · subst x
        exact twoGeneratorModuleShortComplex_exact_of_regular hqreg hfreg
      · exact twoGeneratorModuleShortComplex_exact_of_span_eq_top (hspan x hx hxx)
    · exact sectionRepresenterKoszul_stalk_exact_of_not_mem X U x hx q f
  rw [ShortComplex.ab_exact_iff_function_exact]
  change Function.Exact
    (sectionRepresenterKoszulStalkShortComplex X U x q f).f
    (sectionRepresenterKoszulStalkShortComplex X U x q f).g
  exact
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (sectionRepresenterKoszulStalkShortComplex X U x q f)).mp hlocal

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The first differential is monic for a regular pair at the supported
point and a unit ideal everywhere else on the represented open. -/
theorem sectionRepresenterKoszulFirst_mono_of_regularPairAtPoint
    (U : X.Opens) (q f : Γ(X, U))
    (x₀ : X) (hx₀ : x₀ ∈ U)
    (hqreg : X.presheaf.germ U x₀ hx₀ q ∈ (X.presheaf.stalk x₀)⁰)
    (hfreg : Ideal.Quotient.mk (Ideal.span {X.presheaf.germ U x₀ hx₀ q})
        (X.presheaf.germ U x₀ hx₀ f) ∈
      ((X.presheaf.stalk x₀) ⧸ Ideal.span {X.presheaf.germ U x₀ hx₀ q})⁰)
    (hspan : ∀ (x : X) (hx : x ∈ U), x ≠ x₀ →
      Ideal.span ({X.presheaf.germ U x hx q,
        X.presheaf.germ U x hx f} : Set (X.presheaf.stalk x)) = ⊤) :
    Mono (sectionRepresenterKoszulFirst X.ringCatSheaf U q f) := by
  apply schemeModule_mono_of_stalk_mono
  intro x
  by_cases hx : x ∈ U
  · let Q := sectionRepresenterStalkIso X U x hx
    let P := sectionRepresenterKoszulPairStalkIso X U x hx
    let s := (schemeModuleStalkModuleFunctor X x).map
      (sectionRepresenterKoszulFirst X.ringCatSheaf U q f)
    let t := ModuleCat.ofHom (twoGeneratorFirst
      (X.presheaf.germ U x hx q) (X.presheaf.germ U x hx f))
    letI : Mono t := (ModuleCat.mono_iff_injective t).mpr (by
      by_cases hxx : x = x₀
      · subst x
        exact twoGeneratorFirst_injective_of_regular hqreg
      · exact twoGeneratorFirst_injective_of_span_eq_top (hspan x hx hxx))
    have hconj := sectionRepresenterKoszulFirst_stalk_conjugacy
      X U x hx q f
    have hs : s = Q.inv ≫ t ≫ P.inv := by
      apply (cancel_epi Q.hom).1
      apply (cancel_mono P.hom).1
      simp only [Category.assoc, Iso.hom_inv_id_assoc,
        Iso.inv_hom_id, Category.comp_id]
      exact hconj
    haveI : Mono s := by rw [hs]; infer_instance
    change Mono ((forget₂ (ModuleCat (X.presheaf.stalk x))
      AddCommGrpCat).map s)
    infer_instance
  · rw [AddCommGrpCat.mono_iff_injective]
    intro a b _
    let hzero := sectionRepresenterStalk_isZero_of_not_mem X U x hx
    letI : Subsingleton
        ((schemeModuleStalkModuleFunctor X x).obj
          (sectionRepresenter X.ringCatSheaf U) : Type u) :=
      ModuleCat.subsingleton_of_isZero hzero
    exact @Subsingleton.elim _
      (ModuleCat.subsingleton_of_isZero hzero) a b

end PfaffianDescent
