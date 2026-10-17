import PfaffianDescent.SectionRepresenterKoszulStalk
import PfaffianDescent.TwoGeneratorKoszulShortExact

/-!
# The augmented section-representer Koszul resolution of a closed point

Two functions on an open define a quotient of every local ring on that
open.  When their common scheme-theoretic zero locus is one closed point,
the final quotient is the corresponding skyscraper.  This file constructs
that augmentation, identifies its stalk map with the literal quotient map,
and proves exactness of the augmented complex stalk by stalk.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace PfaffianDescent

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

universe u

variable (X : Scheme.{u})

noncomputable local instance (x : X) :
    (schemeModuleStalkModuleFunctor X x).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- The local complete-intersection quotient defined by the germs of `q`
and `f` at `x`. -/
abbrev sectionRepresenterPointKoszulQuotient
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U)) :=
  X.presheaf.stalk x ⧸ Ideal.span
    ({X.presheaf.germ U x hx q, X.presheaf.germ U x hx f} :
      Set (X.presheaf.stalk x))

/-- The quotient local module placed as a skyscraper at `x`. -/
noncomputable def sectionRepresenterPointKoszulSkyscraper
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U)) : X.Modules :=
  schemeModuleSkyscraper x <|
    ModuleCat.of (X.presheaf.stalk x)
      (sectionRepresenterPointKoszulQuotient X U x hx q f)

/-- The section `1 mod (q,f)` over every open containing the center. -/
noncomputable def sectionRepresenterPointKoszulSection
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U)) :
    (sectionRepresenterPointKoszulSkyscraper X U x hx q f).val.obj (op U) :=
  (schemeModuleSkyscraperAbPresheafAddEquivOfMem x
    (ModuleCat.of (X.presheaf.stalk x)
      (sectionRepresenterPointKoszulQuotient X U x hx q f)) U hx).symm 1

set_option backward.isDefEq.respectTransparency false in
theorem sectionRepresenterPointKoszulSection_q_smul
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U)) :
    q • sectionRepresenterPointKoszulSection X U x hx q f = 0 := by
  let A := ModuleCat.of (X.presheaf.stalk x)
    (sectionRepresenterPointKoszulQuotient X U x hx q f)
  let e := schemeModuleSkyscraperAbPresheafAddEquivOfMem x A U hx
  apply e.injective
  rw [schemeModuleSkyscraperAbPresheafAddEquivOfMem_smul]
  change X.presheaf.germ U x hx q • e (e.symm 1) = e 0
  rw [e.apply_symm_apply, map_zero]
  change X.presheaf.germ U x hx q •
      (1 : sectionRepresenterPointKoszulQuotient X U x hx q f) = 0
  change Ideal.Quotient.mk _ (X.presheaf.germ U x hx q) * 1 = 0
  rw [mul_one]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (by simp))

set_option backward.isDefEq.respectTransparency false in
theorem sectionRepresenterPointKoszulSection_f_smul
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U)) :
    f • sectionRepresenterPointKoszulSection X U x hx q f = 0 := by
  let A := ModuleCat.of (X.presheaf.stalk x)
    (sectionRepresenterPointKoszulQuotient X U x hx q f)
  let e := schemeModuleSkyscraperAbPresheafAddEquivOfMem x A U hx
  apply e.injective
  rw [schemeModuleSkyscraperAbPresheafAddEquivOfMem_smul]
  change X.presheaf.germ U x hx f • e (e.symm 1) = e 0
  rw [e.apply_symm_apply, map_zero]
  change X.presheaf.germ U x hx f •
      (1 : sectionRepresenterPointKoszulQuotient X U x hx q f) = 0
  change Ideal.Quotient.mk _ (X.presheaf.germ U x hx f) * 1 = 0
  rw [mul_one]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (by simp))

/-- The literal local quotient map. -/
noncomputable def sectionRepresenterPointKoszulQuotientMap
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U)) :
    ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) ⟶
      ModuleCat.of (X.presheaf.stalk x)
        (sectionRepresenterPointKoszulQuotient X U x hx q f) :=
  ModuleCat.ofHom <| (Ideal.Quotient.mkₐ _
    (Ideal.span
      ({X.presheaf.germ U x hx q, X.presheaf.germ U x hx f} :
        Set (X.presheaf.stalk x)))).toLinearMap

set_option backward.isDefEq.respectTransparency false in
/-- The represented augmentation is the adjoint of the local quotient map. -/
theorem sectionRepresenterPointKoszul_augmentation_eq_toSkyscraper
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U)) :
    sectionRepresenterKoszulAugmentation X.ringCatSheaf U
        (sectionRepresenterPointKoszulSkyscraper X U x hx q f)
        (sectionRepresenterPointKoszulSection X U x hx q f) =
      schemeModuleToSkyscraper x
        ((sectionRepresenterStalkIso X U x hx).inv ≫
          sectionRepresenterPointKoszulQuotientMap X U x hx q f) := by
  apply (sectionRepresenterHomEquiv X.ringCatSheaf U
    (sectionRepresenterPointKoszulSkyscraper X U x hx q f)).injective
  change sectionRepresenterHomEquiv X.ringCatSheaf U _
      (sectionRepresenterAugmentation X.ringCatSheaf U _ _) = _
  rw [sectionRepresenterHomEquiv_augmentation]
  rw [← sectionRepresenterHom_apply_generator]
  change sectionRepresenterPointKoszulSection X U x hx q f =
    (schemeModuleToSkyscraperAbPresheafMap x
      ((sectionRepresenterStalkIso X U x hx).inv ≫
        sectionRepresenterPointKoszulQuotientMap X U x hx q f)).app (op U)
          (sectionRepresenterGenerator X.ringCatSheaf U)
  let A := ModuleCat.of (X.presheaf.stalk x)
    (sectionRepresenterPointKoszulQuotient X U x hx q f)
  let e := schemeModuleSkyscraperAbPresheafAddEquivOfMem x A U hx
  apply e.injective
  rw [schemeModuleSkyscraperAbPresheafAddEquivOfMem_toSkyscraper_app]
  have hsection : e (sectionRepresenterPointKoszulSection X U x hx q f) = 1 := by
    exact e.apply_symm_apply 1
  rw [hsection]
  change (1 : sectionRepresenterPointKoszulQuotient X U x hx q f) =
    sectionRepresenterPointKoszulQuotientMap X U x hx q f
      ((sectionRepresenterStalkIso X U x hx).inv
        (sectionRepresenterStalkGenerator X U x hx))
  have hgen : (sectionRepresenterStalkIso X U x hx).inv
      (sectionRepresenterStalkGenerator X U x hx) = 1 := by
    have h := ConcreteCategory.congr_hom
      (sectionRepresenterStalkIso X U x hx).hom_inv_id
      (1 : X.presheaf.stalk x)
    change (sectionRepresenterStalkIso X U x hx).inv
      ((sectionRepresenterStalkIso X U x hx).hom 1) = 1 at h
    rw [sectionRepresenterStalkIso_hom,
      sectionRepresenterStalkGeneratorHom_apply_one] at h
    exact h
  rw [hgen]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- At the center, the stalk of the global augmentation is the quotient map
under the canonical free-rank-one and skyscraper identifications. -/
theorem sectionRepresenterPointKoszul_augmentation_stalk_conjugacy
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U)) :
    (sectionRepresenterStalkIso X U x hx).hom ≫
        (schemeModuleStalkModuleFunctor X x).map
          (sectionRepresenterKoszulAugmentation X.ringCatSheaf U
            (sectionRepresenterPointKoszulSkyscraper X U x hx q f)
            (sectionRepresenterPointKoszulSection X U x hx q f)) ≫
        schemeModuleSkyscraperStalkLinearMap x
          (ModuleCat.of (X.presheaf.stalk x)
            (sectionRepresenterPointKoszulQuotient X U x hx q f)) =
      sectionRepresenterPointKoszulQuotientMap X U x hx q f := by
  rw [sectionRepresenterPointKoszul_augmentation_eq_toSkyscraper]
  change (sectionRepresenterStalkIso X U x hx).hom ≫
      schemeModuleFromSkyscraper x
        (schemeModuleToSkyscraper x
          ((sectionRepresenterStalkIso X U x hx).inv ≫
            sectionRepresenterPointKoszulQuotientMap X U x hx q f)) = _
  let A := ModuleCat.of (X.presheaf.stalk x)
    (sectionRepresenterPointKoszulQuotient X U x hx q f)
  let l : (schemeModuleStalkModuleFunctor X x).obj
        (show X.Modules from sectionRepresenter X.ringCatSheaf U) ⟶ A :=
    (sectionRepresenterStalkIso X U x hx).inv ≫
      sectionRepresenterPointKoszulQuotientMap X U x hx q f
  have hl := (schemeModuleStalkSkyscraperHomEquiv x
    (show X.Modules from sectionRepresenter X.ringCatSheaf U) A).left_inv l
  change (sectionRepresenterStalkIso X U x hx).hom ≫
      schemeModuleFromSkyscraper x (schemeModuleToSkyscraper x l) = _
  calc
    _ = (sectionRepresenterStalkIso X U x hx).hom ≫ l :=
      congrArg (fun k => (sectionRepresenterStalkIso X U x hx).hom ≫ k) hl
    _ = _ := by
      dsimp [l]
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The ordinary last two terms of the two-generator Koszul resolution. -/
noncomputable def twoGeneratorQuotientModuleShortComplex
    (R : Type u) [CommRing R] (q f : R) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    (ModuleCat.ofHom (twoGeneratorLast q f))
    (ModuleCat.ofHom <| (Ideal.Quotient.mkₐ R
      (Ideal.span ({q, f} : Set R))).toLinearMap) (by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        change Ideal.Quotient.mk (Ideal.span ({q, f} : Set R))
          (twoGeneratorLast q f z) = 0
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        rw [← twoGeneratorLast_range]
        exact LinearMap.mem_range_self (twoGeneratorLast q f) z)

/-- The quotient endpoint makes the last two Koszul terms exact for every
pair of elements. -/
theorem twoGeneratorQuotientModuleShortComplex_exact
    (R : Type u) [CommRing R] (q f : R) :
    (twoGeneratorQuotientModuleShortComplex R q f).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  apply le_antisymm
  · intro z hz
    change Ideal.Quotient.mk (Ideal.span ({q, f} : Set R)) z = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← twoGeneratorLast_range]
    exact hz
  · intro z hz
    change Ideal.Quotient.mk (Ideal.span ({q, f} : Set R)) z = 0 at hz
    change z ∈ LinearMap.range (twoGeneratorLast q f)
    rw [twoGeneratorLast_range]
    exact (Ideal.Quotient.eq_zero_iff_mem
      (I := Ideal.span ({q, f} : Set R)) (a := (z : R))).mp hz

/-- The augmented section-representer complex after taking a module stalk. -/
noncomputable def sectionRepresenterPointKoszulStalkShortComplex
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U)) (y : X) :
    ShortComplex (ModuleCat.{u} (X.presheaf.stalk y)) := by
  let F := schemeModuleStalkModuleFunctor X y
  let pzero : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  exact @ShortComplex.map _ _ _ _ _ _
    (sectionRepresenterKoszulAugmentedShortComplex X.ringCatSheaf U q f
      (sectionRepresenterPointKoszulSkyscraper X U x hx q f)
      (sectionRepresenterPointKoszulSection X U x hx q f)
      (sectionRepresenterPointKoszulSection_q_smul X U x hx q f)
      (sectionRepresenterPointKoszulSection_f_smul X U x hx q f)) F pzero

set_option backward.isDefEq.respectTransparency false in
/-- At its center, the stalked augmented complex is the ordinary quotient
Koszul complex. -/
noncomputable def sectionRepresenterPointKoszulStalkShortComplexIso
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U)) :
    sectionRepresenterPointKoszulStalkShortComplex X U x hx q f x ≅
      twoGeneratorQuotientModuleShortComplex (X.presheaf.stalk x)
        (X.presheaf.germ U x hx q) (X.presheaf.germ U x hx f) := by
  refine ShortComplex.isoMk
    (sectionRepresenterKoszulPairStalkIso X U x hx)
    (sectionRepresenterStalkIso X U x hx).symm
    (schemeModuleSkyscraperStalkIso x
      (ModuleCat.of (X.presheaf.stalk x)
        (sectionRepresenterPointKoszulQuotient X U x hx q f))) ?_ ?_
  all_goals dsimp [sectionRepresenterPointKoszulStalkShortComplex,
    twoGeneratorQuotientModuleShortComplex]
  · rw [← cancel_epi (sectionRepresenterKoszulPairStalkIso X U x hx).inv]
    simp only [Iso.inv_hom_id_assoc]
    exact (sectionRepresenterKoszulLast_stalk_conjugacy X U x hx q f).symm
  · rw [← cancel_epi (sectionRepresenterStalkIso X U x hx).hom]
    simp only [Iso.hom_inv_id_assoc]
    exact (sectionRepresenterPointKoszul_augmentation_stalk_conjugacy
      X U x hx q f).symm

/-- Exactness of the augmented complex at its central stalk. -/
theorem sectionRepresenterPointKoszul_stalk_exact_at_center
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U)) :
    (sectionRepresenterPointKoszulStalkShortComplex X U x hx q f x).Exact := by
  apply ShortComplex.exact_of_iso
    (sectionRepresenterPointKoszulStalkShortComplexIso X U x hx q f).symm
  exact twoGeneratorQuotientModuleShortComplex_exact _ _ _

/-- If the two local generators span the unit ideal, their last Koszul map
is an epimorphism. -/
theorem twoGeneratorLast_epi_of_span_eq_top
    {R : Type u} [CommRing R] (q f : R)
    (hspan : Ideal.span ({q, f} : Set R) = ⊤) :
    Epi (ModuleCat.ofHom (twoGeneratorLast q f)) := by
  rw [ModuleCat.epi_iff_range_eq_top]
  change LinearMap.range (twoGeneratorLast q f) = ⊤
  rw [twoGeneratorLast_range, hspan]

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- A surjective local-module map induces an epimorphism onto its
skyscraper when the center is closed. -/
theorem schemeModuleToSkyscraper_epi_of_isClosed_of_epi
    (x : X) (hx : IsClosed ({x} : Set X)) (M : X.Modules)
    (A : ModuleCat.{u} (X.presheaf.stalk x))
    (l : (schemeModuleStalkModuleFunctor X x).obj M ⟶ A) [Epi l] :
    Epi (schemeModuleToSkyscraper x l) := by
  classical
  let a := schemeModuleToSkyscraper x l
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have hsurj : ∀ y : X, Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
        ((T.map a).hom)) := by
    intro y
    by_cases hy : y = x
    · subst y
      let c := schemeModuleSkyscraperStalkLinearMap x A
      letI : IsIso c := (schemeModuleSkyscraperStalkIso x A).isIso_hom
      have hcomp : (schemeModuleStalkModuleFunctor X x).map a ≫ c = l := by
        exact (schemeModuleStalkSkyscraperHomEquiv x M A).left_inv l
      have heq : (schemeModuleStalkModuleFunctor X x).map a = l ≫ inv c := by
        apply (cancel_mono c).1
        rw [hcomp]
        simp
      haveI : Epi ((schemeModuleStalkModuleFunctor X x).map a) := by
        rw [heq]
        infer_instance
      change Function.Surjective
        ((schemeModuleStalkModuleFunctor X x).map a)
      exact (ModuleCat.epi_iff_surjective _).mp inferInstance
    · have hnot : ¬ x ⤳ y :=
        hx.not_specializes (Set.mem_singleton x)
          (by simpa [Set.mem_singleton_iff, eq_comm] using hy)
      have htgt : IsZero
          ((schemeModuleSkyscraper x A).presheaf.stalk y) :=
        (skyscraperPresheafStalkOfNotSpecializesIsTerminal x
          ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj A)
          hnot).isZero
      intro z
      refine ⟨0, ?_⟩
      exact (AddCommGrpCat.subsingleton_of_isZero htgt).elim _ _
  have hloc : TopCat.Presheaf.IsLocallySurjective ((T.map a).hom) :=
    (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
      ((T.map a).hom)).mpr hsurj
  have hsheafEpi : Epi (T.map a) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi (T.map a)).mp hloc
  letI : Epi (T.map a) := hsheafEpi
  exact (Functor.reflectsEpimorphisms_of_faithful T).reflects a inferInstance

set_option linter.style.haveILetI false in
/-- The closed-point Koszul augmentation is an epimorphism. -/
theorem sectionRepresenterPointKoszul_augmentation_epi
    (U : X.Opens) (x : X) (hx : x ∈ U)
    (hxclosed : IsClosed ({x} : Set X)) (q f : Γ(X, U)) :
    Epi (sectionRepresenterKoszulAugmentation X.ringCatSheaf U
      (sectionRepresenterPointKoszulSkyscraper X U x hx q f)
      (sectionRepresenterPointKoszulSection X U x hx q f)) := by
  let Q := sectionRepresenterPointKoszulQuotientMap X U x hx q f
  have hQsurj : Function.Surjective Q := by
    change Function.Surjective ((Ideal.Quotient.mkₐ (X.presheaf.stalk x)
      (Ideal.span
        ({X.presheaf.germ U x hx q, X.presheaf.germ U x hx f} :
          Set (X.presheaf.stalk x)))).toLinearMap)
    exact Ideal.Quotient.mkₐ_surjective (X.presheaf.stalk x)
      (Ideal.span
        ({X.presheaf.germ U x hx q, X.presheaf.germ U x hx f} :
          Set (X.presheaf.stalk x)))
  letI : Epi Q := (ModuleCat.epi_iff_surjective Q).mpr hQsurj
  let l := (sectionRepresenterStalkIso X U x hx).inv ≫ Q
  letI : Epi l := by dsimp [l]; infer_instance
  rw [sectionRepresenterPointKoszul_augmentation_eq_toSkyscraper]
  exact schemeModuleToSkyscraper_epi_of_isClosed_of_epi X x hxclosed
    (sectionRepresenter X.ringCatSheaf U)
    (ModuleCat.of (X.presheaf.stalk x)
      (sectionRepresenterPointKoszulQuotient X U x hx q f)) l

set_option backward.isDefEq.respectTransparency false in
/-- Away from the center but inside `U`, exactness says precisely that the
two germs generate the unit ideal; the target skyscraper stalk is zero. -/
theorem sectionRepresenterPointKoszul_stalk_exact_of_mem_ne
    (U : X.Opens) (x : X) (hx : x ∈ U)
    (hxclosed : IsClosed ({x} : Set X))
    (q f : Γ(X, U)) (y : X) (hy : y ∈ U) (hyx : y ≠ x)
    (hspan : Ideal.span
      ({X.presheaf.germ U y hy q, X.presheaf.germ U y hy f} :
        Set (X.presheaf.stalk y)) = ⊤) :
    (sectionRepresenterPointKoszulStalkShortComplex
      X U x hx q f y).Exact := by
  let S := sectionRepresenterPointKoszulStalkShortComplex X U x hx q f y
  let P := sectionRepresenterKoszulPairStalkIso X U y hy
  let Q := sectionRepresenterStalkIso X U y hy
  let t := ModuleCat.ofHom (twoGeneratorLast
    (X.presheaf.germ U y hy q) (X.presheaf.germ U y hy f))
  letI : Epi t := twoGeneratorLast_epi_of_span_eq_top _ _ hspan
  have hconj := sectionRepresenterKoszulLast_stalk_conjugacy
    X U y hy q f
  have hf : S.f = P.hom ≫ t ≫ Q.hom := by
    apply (cancel_epi P.inv).1
    apply (cancel_mono Q.inv).1
    simp only [Category.assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id, Category.comp_id]
    exact hconj
  have htarget : IsZero ((schemeModuleStalkModuleFunctor X y).obj
      (sectionRepresenterPointKoszulSkyscraper X U x hx q f)) := by
    let A := ModuleCat.of (X.presheaf.stalk x)
      (sectionRepresenterPointKoszulQuotient X U x hx q f)
    change IsZero ((schemeModuleStalkModuleFunctor X y).obj
      (schemeModuleSkyscraper x A))
    rw [ModuleCat.isZero_iff_subsingleton]
    exact AddCommGrpCat.subsingleton_of_isZero <|
      schemeModuleSkyscraper_stalk_isZero_of_not_specializes x y
        (hxclosed.not_specializes (Set.mem_singleton x)
          (by simpa [Set.mem_singleton_iff, eq_comm] using hyx)) A
  have hg : S.g = 0 := by
    exact htarget.eq_of_tgt _ _
  apply (S.exact_iff_epi hg).2
  rw [hf]
  infer_instance

/-- Outside `U`, the middle section-representer stalk is zero. -/
theorem sectionRepresenterPointKoszul_stalk_exact_of_not_mem
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U))
    (y : X) (hy : y ∉ U) :
    (sectionRepresenterPointKoszulStalkShortComplex
      X U x hx q f y).Exact := by
  apply ShortComplex.exact_of_isZero_X₂
  dsimp [sectionRepresenterPointKoszulStalkShortComplex]
  exact sectionRepresenterStalk_isZero_of_not_mem X U y hy

set_option linter.style.haveILetI false in
/-- If the two functions cut out exactly one closed point on `U`, the
augmented section-representer Koszul complex is globally exact. -/
theorem sectionRepresenterPointKoszul_augmented_exact
    (U : X.Opens) (x : X) (hx : x ∈ U)
    (hxclosed : IsClosed ({x} : Set X)) (q f : Γ(X, U))
    (hspan : ∀ (y : X) (hy : y ∈ U), y ≠ x →
      Ideal.span
        ({X.presheaf.germ U y hy q, X.presheaf.germ U y hy f} :
          Set (X.presheaf.stalk y)) = ⊤) :
    (sectionRepresenterKoszulAugmentedShortComplex X.ringCatSheaf U q f
      (sectionRepresenterPointKoszulSkyscraper X U x hx q f)
      (sectionRepresenterPointKoszulSection X U x hx q f)
      (sectionRepresenterPointKoszulSection_q_smul X U x hx q f)
      (sectionRepresenterPointKoszulSection_f_smul X U x hx q f)).Exact := by
  let S := sectionRepresenterKoszulAugmentedShortComplex X.ringCatSheaf U q f
    (sectionRepresenterPointKoszulSkyscraper X U x hx q f)
    (sectionRepresenterPointKoszulSection X U x hx q f)
    (sectionRepresenterPointKoszulSection_q_smul X U x hx q f)
    (sectionRepresenterPointKoszulSection_f_smul X U x hx q f)
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  letI : T.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive T
  apply Functor.reflects_exact_of_faithful T
  let pzeroT : T.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive T
  let ST := @ShortComplex.map _ _ _ _ _ _ S T pzeroT
  change ST.Exact
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact ST).mpr
  intro y
  let A := TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
  letI : A.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive A
  let F := schemeModuleStalkFunctor X y
  let pzeroF : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive F
  let SF := @ShortComplex.map _ _ _ _ _ _ S F pzeroF
  change SF.Exact
  have hlocal : (sectionRepresenterPointKoszulStalkShortComplex
      X U x hx q f y).Exact := by
    by_cases hyx : y = x
    · subst y
      exact sectionRepresenterPointKoszul_stalk_exact_at_center
        X U x hx q f
    · by_cases hy : y ∈ U
      · exact sectionRepresenterPointKoszul_stalk_exact_of_mem_ne
          X U x hx hxclosed q f y hy hyx (hspan y hy hyx)
      · exact sectionRepresenterPointKoszul_stalk_exact_of_not_mem
          X U x hx q f y hy
  rw [ShortComplex.ab_exact_iff_function_exact]
  change Function.Exact
    (sectionRepresenterPointKoszulStalkShortComplex X U x hx q f y).f
    (sectionRepresenterPointKoszulStalkShortComplex X U x hx q f y).g
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
    (sectionRepresenterPointKoszulStalkShortComplex X U x hx q f y)).mp hlocal

/-- Transport a point-supported module through its central-stalk
identification and the local complete-intersection quotient. -/
noncomputable def sectionRepresenterPointKoszulTargetIso
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U))
    (M : X.Modules)
    (eM : M ≅ schemeModuleSkyscraper x
      ((schemeModuleStalkModuleFunctor X x).obj M))
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        (sectionRepresenterPointKoszulQuotient X U x hx q f)) :
    M ≅ sectionRepresenterPointKoszulSkyscraper X U x hx q f :=
  eM ≪≫ (schemeModuleSkyscraperFunctor X x).mapIso qM

/-- The quotient generator transported back to the actual point-supported
module. -/
noncomputable def sectionRepresenterPointKoszulTransportedSection
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U))
    (M : X.Modules)
    (eM : M ≅ schemeModuleSkyscraper x
      ((schemeModuleStalkModuleFunctor X x).obj M))
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        (sectionRepresenterPointKoszulQuotient X U x hx q f)) :
    M.val.obj (op U) :=
  (sectionRepresenterPointKoszulTargetIso X U x hx q f M eM qM).inv.val.app
    (op U) (sectionRepresenterPointKoszulSection X U x hx q f)

theorem sectionRepresenterPointKoszulTransportedSection_q_smul
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U))
    (M : X.Modules)
    (eM : M ≅ schemeModuleSkyscraper x
      ((schemeModuleStalkModuleFunctor X x).obj M))
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        (sectionRepresenterPointKoszulQuotient X U x hx q f)) :
    letI : Module (Γ(X, U)) ((M.val.obj (op U) : ModuleCat _)) :=
      (M.val.obj (op U)).isModule
    q • sectionRepresenterPointKoszulTransportedSection
      X U x hx q f M eM qM = 0 := by
  letI : Module (Γ(X, U)) ((M.val.obj (op U) : ModuleCat _)) :=
    (M.val.obj (op U)).isModule
  letI : Module (Γ(X, U))
      (((sectionRepresenterPointKoszulSkyscraper
        X U x hx q f).val.obj (op U) : ModuleCat _)) :=
    ((sectionRepresenterPointKoszulSkyscraper
      X U x hx q f).val.obj (op U)).isModule
  change q • (sectionRepresenterPointKoszulTargetIso
    X U x hx q f M eM qM).inv.val.app (op U)
      (sectionRepresenterPointKoszulSection X U x hx q f) = 0
  rw [← map_smul,
    sectionRepresenterPointKoszulSection_q_smul, map_zero]

theorem sectionRepresenterPointKoszulTransportedSection_f_smul
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U))
    (M : X.Modules)
    (eM : M ≅ schemeModuleSkyscraper x
      ((schemeModuleStalkModuleFunctor X x).obj M))
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        (sectionRepresenterPointKoszulQuotient X U x hx q f)) :
    letI : Module (Γ(X, U)) ((M.val.obj (op U) : ModuleCat _)) :=
      (M.val.obj (op U)).isModule
    f • sectionRepresenterPointKoszulTransportedSection
      X U x hx q f M eM qM = 0 := by
  letI : Module (Γ(X, U)) ((M.val.obj (op U) : ModuleCat _)) :=
    (M.val.obj (op U)).isModule
  letI : Module (Γ(X, U))
      (((sectionRepresenterPointKoszulSkyscraper
        X U x hx q f).val.obj (op U) : ModuleCat _)) :=
    ((sectionRepresenterPointKoszulSkyscraper
      X U x hx q f).val.obj (op U)).isModule
  change f • (sectionRepresenterPointKoszulTargetIso
    X U x hx q f M eM qM).inv.val.app (op U)
      (sectionRepresenterPointKoszulSection X U x hx q f) = 0
  rw [← map_smul,
    sectionRepresenterPointKoszulSection_f_smul, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Augmentation commutes with transport from the quotient skyscraper to the
actual point-supported target. -/
theorem sectionRepresenterPointKoszulTransported_augmentation
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U))
    (M : X.Modules)
    (eM : M ≅ schemeModuleSkyscraper x
      ((schemeModuleStalkModuleFunctor X x).obj M))
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        (sectionRepresenterPointKoszulQuotient X U x hx q f)) :
    sectionRepresenterKoszulAugmentation X.ringCatSheaf U M
        (sectionRepresenterPointKoszulTransportedSection
          X U x hx q f M eM qM) =
      sectionRepresenterKoszulAugmentation X.ringCatSheaf U
          (sectionRepresenterPointKoszulSkyscraper X U x hx q f)
          (sectionRepresenterPointKoszulSection X U x hx q f) ≫
        (sectionRepresenterPointKoszulTargetIso
          X U x hx q f M eM qM).inv := by
  change sectionRepresenterAugmentation X.ringCatSheaf U M _ =
    sectionRepresenterAugmentation X.ringCatSheaf U _ _ ≫ _
  apply (sectionRepresenterHomEquiv X.ringCatSheaf U M).injective
  rw [sectionRepresenterHomEquiv_augmentation,
    sectionRepresenterHomEquiv_postcomp]
  rw [sectionRepresenterHomEquiv_augmentation]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual-target augmented complex is isomorphic to the quotient
skyscraper complex. -/
noncomputable def sectionRepresenterPointKoszulTransportedShortComplexIso
    (U : X.Opens) (x : X) (hx : x ∈ U) (q f : Γ(X, U))
    (M : X.Modules)
    (eM : M ≅ schemeModuleSkyscraper x
      ((schemeModuleStalkModuleFunctor X x).obj M))
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        (sectionRepresenterPointKoszulQuotient X U x hx q f)) :
    sectionRepresenterKoszulAugmentedShortComplex X.ringCatSheaf U q f M
        (sectionRepresenterPointKoszulTransportedSection
          X U x hx q f M eM qM)
        (sectionRepresenterPointKoszulTransportedSection_q_smul
          X U x hx q f M eM qM)
        (sectionRepresenterPointKoszulTransportedSection_f_smul
          X U x hx q f M eM qM) ≅
      sectionRepresenterKoszulAugmentedShortComplex X.ringCatSheaf U q f
        (sectionRepresenterPointKoszulSkyscraper X U x hx q f)
        (sectionRepresenterPointKoszulSection X U x hx q f)
        (sectionRepresenterPointKoszulSection_q_smul X U x hx q f)
        (sectionRepresenterPointKoszulSection_f_smul X U x hx q f) := by
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (sectionRepresenterPointKoszulTargetIso X U x hx q f M eM qM) ?_ ?_
  · dsimp [sectionRepresenterKoszulAugmentedShortComplex]
    simp only [Category.id_comp, Category.comp_id]
  · dsimp [sectionRepresenterKoszulAugmentedShortComplex]
    rw [sectionRepresenterPointKoszulTransported_augmentation]
    simp

/-- Exactness transported to the actual point-supported target. -/
theorem sectionRepresenterPointKoszulTransported_augmented_exact
    (U : X.Opens) (x : X) (hx : x ∈ U)
    (hxclosed : IsClosed ({x} : Set X)) (q f : Γ(X, U))
    (M : X.Modules)
    (eM : M ≅ schemeModuleSkyscraper x
      ((schemeModuleStalkModuleFunctor X x).obj M))
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        (sectionRepresenterPointKoszulQuotient X U x hx q f))
    (hspan : ∀ (y : X) (hy : y ∈ U), y ≠ x →
      Ideal.span
        ({X.presheaf.germ U y hy q, X.presheaf.germ U y hy f} :
          Set (X.presheaf.stalk y)) = ⊤) :
    (sectionRepresenterKoszulAugmentedShortComplex X.ringCatSheaf U q f M
      (sectionRepresenterPointKoszulTransportedSection
        X U x hx q f M eM qM)
      (sectionRepresenterPointKoszulTransportedSection_q_smul
        X U x hx q f M eM qM)
      (sectionRepresenterPointKoszulTransportedSection_f_smul
        X U x hx q f M eM qM)).Exact := by
  apply ShortComplex.exact_of_iso
    (sectionRepresenterPointKoszulTransportedShortComplexIso
      X U x hx q f M eM qM).symm
  exact sectionRepresenterPointKoszul_augmented_exact
    X U x hx hxclosed q f hspan

/-- The transported augmentation is an epimorphism. -/
theorem sectionRepresenterPointKoszulTransported_augmentation_epi
    (U : X.Opens) (x : X) (hx : x ∈ U)
    (hxclosed : IsClosed ({x} : Set X)) (q f : Γ(X, U))
    (M : X.Modules)
    (eM : M ≅ schemeModuleSkyscraper x
      ((schemeModuleStalkModuleFunctor X x).obj M))
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        (sectionRepresenterPointKoszulQuotient X U x hx q f)) :
    Epi (sectionRepresenterKoszulAugmentation X.ringCatSheaf U M
      (sectionRepresenterPointKoszulTransportedSection
        X U x hx q f M eM qM)) := by
  rw [sectionRepresenterPointKoszulTransported_augmentation]
  let e := sectionRepresenterPointKoszulTargetIso X U x hx q f M eM qM
  change Epi (sectionRepresenterKoszulAugmentation X.ringCatSheaf U
    (sectionRepresenterPointKoszulSkyscraper X U x hx q f)
    (sectionRepresenterPointKoszulSection X U x hx q f) ≫ e.inv)
  let hbase : Epi (sectionRepresenterKoszulAugmentation X.ringCatSheaf U
      (sectionRepresenterPointKoszulSkyscraper X U x hx q f)
      (sectionRepresenterPointKoszulSection X U x hx q f)) :=
    sectionRepresenterPointKoszul_augmentation_epi
    X U x hx hxclosed q f
  letI : IsIso e.inv := e.isIso_inv
  letI : IsSplitEpi e.inv := IsSplitEpi.of_iso e.inv
  let hinv : Epi e.inv := IsSplitEpi.epi e.inv
  exact @epi_comp _ _ _ _ _
    (sectionRepresenterKoszulAugmentation X.ringCatSheaf U
      (sectionRepresenterPointKoszulSkyscraper X U x hx q f)
      (sectionRepresenterPointKoszulSection X U x hx q f)) hbase e.inv hinv

end PfaffianDescent
