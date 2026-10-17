import PfaffianDescent.SheafModuleEnoughInjectives
import PfaffianDescent.SchemeModuleCohomology
import PfaffianDescent.VoisinSheafStalk
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator


/-!
# Flasque sheaves of modules and low-degree acyclicity

This file proves that injective scheme modules are flasque after forgetting
the module structure. It also proves that flasque scheme modules have
vanishing scheme-module cohomology in degrees one and two.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace PfaffianDescent

variable {C : Type u} [SmallCategory C]
variable {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

abbrev sectionRepresenter (U : C) : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((PresheafOfModules.free R.obj).obj (yoneda.obj U))

noncomputable def sectionRepresenterHomEquiv
    (U : C) (M : SheafOfModules.{u} R) :
    (sectionRepresenter R U ⟶ M) ≃ M.val.obj (op U) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).trans
    PresheafOfModules.freeYonedaEquiv

end PfaffianDescent

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type u} [SmallCategory C]
variable {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

noncomputable def sectionRepresenterMap {V U : C} (i : V ⟶ U) :
    sectionRepresenter R V ⟶ sectionRepresenter R U :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    ((PresheafOfModules.free R.obj).map (yoneda.map i))

lemma sectionRepresenterHomEquiv_comp
    {V U : C} (i : V ⟶ U) (M : SheafOfModules.{u} R)
    (f : sectionRepresenter R U ⟶ M) :
    (sectionRepresenterHomEquiv R V M) (sectionRepresenterMap R i ≫ f) =
      M.val.map i.op ((sectionRepresenterHomEquiv R U M) f) := by
  change PresheafOfModules.freeYonedaEquiv
      (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)
        ((PresheafOfModules.sheafification (𝟙 R.obj)).map
          ((PresheafOfModules.free R.obj).map (yoneda.map i)) ≫ f)) =
      M.val.map i.op (PresheafOfModules.freeYonedaEquiv
        (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) f))
  rw [show PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)
      ((PresheafOfModules.sheafification (𝟙 R.obj)).map
        ((PresheafOfModules.free R.obj).map (yoneda.map i)) ≫ f) =
      (PresheafOfModules.free R.obj).map (yoneda.map i) ≫
        PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) f from
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_left _ _]
  let q := PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) f
  change CategoryTheory.yonedaEquiv
      (PresheafOfModules.freeHomEquiv
        ((PresheafOfModules.free R.obj).map (yoneda.map i) ≫ q)) =
    M.val.map i.op (CategoryTheory.yonedaEquiv
      (PresheafOfModules.freeHomEquiv q))
  rw [show PresheafOfModules.freeHomEquiv
      ((PresheafOfModules.free R.obj).map (yoneda.map i) ≫ q) =
      yoneda.map i ≫ PresheafOfModules.freeHomEquiv q from
    (PresheafOfModules.freeAdjunction R.obj).homEquiv_naturality_left _ _]
  exact (CategoryTheory.yonedaEquiv_naturality
    (PresheafOfModules.freeHomEquiv q) i).symm

end PfaffianDescent

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits Opposite


variable {C : Type u} [SmallCategory C]
variable {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
lemma free_map_mono {F G : Cᵒᵖ ⥤ Type u} (φ : F ⟶ G)
    (hφ : ∀ (X : Cᵒᵖ), Function.Injective (φ.app X)) :
    Mono ((PresheafOfModules.free R.obj).map φ) := by
  apply PresheafOfModules.mono_of_injective
  intro X
  change Function.Injective (Finsupp.mapDomain (φ.app X))
  exact Finsupp.mapDomain_injective (hφ X)

lemma yoneda_map_injective {V U : C} (i : V ⟶ U) [Mono i] (W : Cᵒᵖ) :
    Function.Injective ((yoneda.map i).app W) := by
  intro f g h
  exact (cancel_mono i).1 h

instance sectionRepresenterMap_mono {V U : C} (i : V ⟶ U) [Mono i] :
    Mono (sectionRepresenterMap R i) := by
  unfold sectionRepresenterMap
  letI : Mono ((PresheafOfModules.free R.obj).map (yoneda.map i)) :=
    free_map_mono R _ (yoneda_map_injective i)
  infer_instance

end PfaffianDescent

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits Opposite
open TopCat TopologicalSpace
open AlgebraicGeometry

variable (X : Scheme.{u})

/-- An injective sheaf of modules on a scheme is flasque as an additive sheaf. -/
theorem injective_isFlasque_scheme (I : X.Modules) [Injective I] :
    TopCat.Presheaf.IsFlasque I.val.presheaf where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).2
    intro s
    let f : (show X.Modules from sectionRepresenter X.ringCatSheaf V.unop) ⟶ I :=
      (sectionRepresenterHomEquiv X.ringCatSheaf V.unop I).symm s
    let e : (show X.Modules from sectionRepresenter X.ringCatSheaf V.unop) ⟶
        (show X.Modules from sectionRepresenter X.ringCatSheaf U.unop) :=
      sectionRepresenterMap X.ringCatSheaf i.unop
    letI : Mono e := sectionRepresenterMap_mono X.ringCatSheaf i.unop
    let g : (show X.Modules from sectionRepresenter X.ringCatSheaf U.unop) ⟶ I :=
      Injective.factorThru f e
    refine ⟨(sectionRepresenterHomEquiv X.ringCatSheaf U.unop I) g, ?_⟩
    have hcomp := sectionRepresenterHomEquiv_comp X.ringCatSheaf i.unop I g
    have he : e ≫ g = f := Injective.comp_factorThru f e
    change I.val.map i ((sectionRepresenterHomEquiv X.ringCatSheaf U.unop I) g) = s
    have hcomp' :
        (sectionRepresenterHomEquiv X.ringCatSheaf V.unop I) (e ≫ g) =
          I.val.map i ((sectionRepresenterHomEquiv X.ringCatSheaf U.unop I) g) := by
      simpa only [Quiver.Hom.op_unop] using hcomp
    rw [← hcomp']
    have heq :
        (sectionRepresenterHomEquiv X.ringCatSheaf V.unop I) (e ≫ g) =
          (sectionRepresenterHomEquiv X.ringCatSheaf V.unop I) f :=
      congrArg (fun q : (show X.Modules from sectionRepresenter X.ringCatSheaf V.unop) ⟶ I =>
        (sectionRepresenterHomEquiv X.ringCatSheaf V.unop I) q) he
    exact heq.trans
      ((sectionRepresenterHomEquiv X.ringCatSheaf V.unop I).apply_symm_apply s)

end PfaffianDescent

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits Opposite
open TopCat TopologicalSpace
open AlgebraicGeometry

variable (X : Scheme.{u})

noncomputable def underlyingAdditiveSheafFunctor :
    X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  SheafOfModules.toSheaf.{u} X.ringCatSheaf

noncomputable instance underlyingAdditiveSheafFunctor_preservesZeroMorphisms :
    (underlyingAdditiveSheafFunctor X).PreservesZeroMorphisms where
  map_zero := by intros; rfl

/-- Forgetting module structure carries a short exact sequence of scheme modules
    to a short exact sequence of additive sheaves. -/
theorem shortExact_underlyingAdditiveSheaf
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (underlyingAdditiveSheafFunctor X)).ShortExact := by
  let hfin : PreservesFiniteLimits
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf) := by
    infer_instance
  letI : PreservesFiniteLimits (underlyingAdditiveSheafFunctor X) := hfin
  have hExact : (S.map (underlyingAdditiveSheafFunctor X)).Exact := by
    apply hS.exact.map_of_mono_of_preservesKernel
    · exact hS.mono_f
    · infer_instance
  have hMono : Mono ((underlyingAdditiveSheafFunctor X).map S.f) := by
    have := hS.mono_f
    exact Functor.map_mono (underlyingAdditiveSheafFunctor X) S.f
  have hEpi : Epi ((underlyingAdditiveSheafFunctor X).map S.g) := by
    rw [← TopCat.Sheaf.isLocallySurjective_iff_epi]
    change Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (↑X.toPresheafedSpace))
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map S.g.val)
    letI : Epi S.g := hS.epi_g
    exact schemeModule_epi_isLocallySurjective S.g
  exact { exact := hExact, mono_f := hMono, epi_g := hEpi }

end PfaffianDescent

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits Opposite
open TopCat TopologicalSpace
open AlgebraicGeometry

variable (X : Scheme.{u})

/-- A compatible family of sections of a module presheaf on a topological space
is determined by its section on the top open. -/
noncomputable def moduleSectionsEquivTop (M : X.Modules) :
    M.sections ≃ M.val.obj (op (⊤ : Opens X)) where
  toFun s := s.val _
  invFun x := M.val.sectionsMk
    (fun U => M.val.map
      (homOfLE (show U.unop ≤ (⊤ : Opens X) from le_top)).op x)
    (by
      intro U V i
      rw [← M.val.map_comp_apply]
      congr)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact M.val.sections_property s
      (homOfLE (show U.unop ≤ (⊤ : Opens X) from le_top)).op
  right_inv x := by
    change M.val.map
      (homOfLE (show (⊤ : Opens X) ≤ (⊤ : Opens X) from le_top)).op x = x
    rw [show (homOfLE (show (⊤ : Opens X) ≤ (⊤ : Opens X) from le_top)).op = 𝟙 _ from
      Subsingleton.elim _ _]
    simpa using ConcreteCategory.congr_hom (M.val.map_id (op (⊤ : Opens X))) x

lemma moduleSectionsEquivTop_naturality {M N : X.Modules} (f : M ⟶ N)
    (s : M.sections) :
    moduleSectionsEquivTop X N (SheafOfModules.sectionsMap f s) =
      f.val.app (op (⊤ : Opens X)) (moduleSectionsEquivTop X M s) := rfl

lemma sectionsMap_surjective_of_top_surjective {M N : X.Modules} (f : M ⟶ N)
    (h : Function.Surjective (f.val.app (op (⊤ : Opens X)))) :
    Function.Surjective (SheafOfModules.sectionsMap f) := by
  intro s
  obtain ⟨t, ht⟩ := h (moduleSectionsEquivTop X N s)
  refine ⟨(moduleSectionsEquivTop X M).symm t, ?_⟩
  apply (moduleSectionsEquivTop X N).injective
  rw [moduleSectionsEquivTop_naturality,
    (moduleSectionsEquivTop X M).apply_symm_apply t, ht]

end PfaffianDescent

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits Opposite
open TopCat TopologicalSpace
open AlgebraicGeometry
open CategoryTheory.Abelian

variable (X : Scheme.{u}) [HasExt.{u} X.Modules]

lemma extHomEquiv_zero_postcomp {L M N : X.Modules} (f : M ⟶ N)
    (x : Ext.{u} L M 0) :
    Ext.homEquiv₀ (x.comp (Ext.mk₀ f) (add_zero 0)) =
      Ext.homEquiv₀ x ≫ f := by
  apply (Ext.mk₀_bijective L N).injective
  rw [Ext.mk₀_homEquiv₀_apply, ← Ext.mk₀_comp_mk₀,
    Ext.mk₀_homEquiv₀_apply]

lemma schemeModuleCohomologyMap_zero_equiv_sections
    {M N : X.Modules} (f : M ⟶ N)
    (x : schemeModuleCohomology X M 0) :
    schemeModuleCohomologyZeroEquivSections X N
        (schemeModuleCohomologyMap X f 0 x) =
      SheafOfModules.sectionsMap f
        (schemeModuleCohomologyZeroEquivSections X M x) := by
  let L : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let q : L ⟶ N := Ext.homEquiv₀ (x.comp (Ext.mk₀ f) (add_zero 0))
  let p : L ⟶ M := Ext.homEquiv₀ x
  have hq : q = p ≫ f := extHomEquiv_zero_postcomp X f x
  change N.unitHomEquiv q = SheafOfModules.sectionsMap f (M.unitHomEquiv p)
  rw [hq]
  exact SheafOfModules.unitHomEquiv_comp_apply _ _

lemma schemeModuleCohomologyMap_zero_surjective_of_sectionsMap
    {M N : X.Modules} (f : M ⟶ N)
    (h : Function.Surjective (SheafOfModules.sectionsMap f)) :
    Function.Surjective (schemeModuleCohomologyMap X f 0) := by
  intro y
  obtain ⟨s, hs⟩ := h (schemeModuleCohomologyZeroEquivSections X N y)
  refine ⟨(schemeModuleCohomologyZeroEquivSections X M).symm s, ?_⟩
  apply (schemeModuleCohomologyZeroEquivSections X N).injective
  rw [schemeModuleCohomologyMap_zero_equiv_sections,
    (schemeModuleCohomologyZeroEquivSections X M).apply_symm_apply s, hs]

/-- The degree-zero cohomology map is surjective exactly when the induced map
on literal global sections is.  The reverse implication is useful when a
dimension count is carried out directly on spaces of sections. -/
lemma sectionsMap_surjective_of_schemeModuleCohomologyMap_zero
    {M N : X.Modules} (f : M ⟶ N)
    (h : Function.Surjective (schemeModuleCohomologyMap X f 0)) :
    Function.Surjective (SheafOfModules.sectionsMap f) := by
  intro y
  obtain ⟨x, hx⟩ := h ((schemeModuleCohomologyZeroEquivSections X N).symm y)
  refine ⟨schemeModuleCohomologyZeroEquivSections X M x, ?_⟩
  apply (schemeModuleCohomologyZeroEquivSections X N).symm.injective
  calc
    (schemeModuleCohomologyZeroEquivSections X N).symm
        (SheafOfModules.sectionsMap f
          (schemeModuleCohomologyZeroEquivSections X M x)) =
        schemeModuleCohomologyMap X f 0 x := by
          apply (schemeModuleCohomologyZeroEquivSections X N).injective
          rw [schemeModuleCohomologyMap_zero_equiv_sections]
          simp
    _ = (schemeModuleCohomologyZeroEquivSections X N).symm y := hx

/-- A nonsurjective map on literal global sections of the quotient in a
short exact sequence forces nonzero first cohomology of its kernel.  This is
the section-space form of the long-exact-sequence step in Voisin's argument. -/
theorem not_schemeModuleCohomology_one_subsingleton_of_sectionsMap_not_surjective
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hnot : ¬ Function.Surjective (SheafOfModules.sectionsMap S.g)) :
    ¬ Subsingleton (schemeModuleCohomology X S.X₁ 1) := by
  apply not_schemeModuleCohomology_one_subsingleton_of_zero_map_not_surjective
    X S hS
  intro hsurj
  exact hnot
    (sectionsMap_surjective_of_schemeModuleCohomologyMap_zero X S.g hsurj)

/-- It suffices to test a restriction map on surjective parameterizations of
its source and target section spaces.  This is the form used for a finite
projective subscheme: homogeneous forms parameterize source sections, while
an affine trivialization parameterizes target sections. -/
theorem not_schemeModuleCohomology_one_subsingleton_of_section_parameterizations
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {V T : Type*} (source : V → S.X₂.sections) (target : S.X₃.sections → T)
    (hsource : Function.Surjective source)
    (htarget : Function.Surjective target)
    (restriction : V → T)
    (hcompat : ∀ v, target (SheafOfModules.sectionsMap S.g (source v)) =
      restriction v)
    (hnot : ¬ Function.Surjective restriction) :
    ¬ Subsingleton (schemeModuleCohomology X S.X₁ 1) := by
  apply not_schemeModuleCohomology_one_subsingleton_of_sectionsMap_not_surjective
    X S hS
  intro hsurj
  apply hnot
  intro t
  obtain ⟨c, hc⟩ := htarget t
  obtain ⟨b, hb⟩ := hsurj c
  obtain ⟨v, hv⟩ := hsource b
  refine ⟨v, ?_⟩
  calc
    restriction v = target (SheafOfModules.sectionsMap S.g (source v)) :=
      (hcompat v).symm
    _ = target (SheafOfModules.sectionsMap S.g b) := by rw [hv]
    _ = target c := by rw [hb]
    _ = t := hc

end PfaffianDescent

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits Opposite
open TopCat TopologicalSpace
open AlgebraicGeometry
open CategoryTheory.Abelian

variable (X : Scheme.{u}) [EnoughInjectives X.Modules] [HasExt.{u} X.Modules]

/-- A flasque scheme module has vanishing first Ext from the structure sheaf. -/
theorem flasque_schemeModuleCohomology_one (F : X.Modules)
    [TopCat.Presheaf.IsFlasque F.val.presheaf] :
    Subsingleton (schemeModuleCohomology X F 1) := by
  let j : F ⟶ Injective.under F := Injective.ι F
  let S := ShortComplex.mk j (cokernel.π j) (cokernel.condition j)
  have hS : S.ShortExact := by
    dsimp [S]
    exact { exact := ShortComplex.exact_cokernel j }
  have hT := shortExact_underlyingAdditiveSheaf X S hS
  letI hIflasque : TopCat.Presheaf.IsFlasque (Injective.under F).val.presheaf :=
    injective_isFlasque_scheme X (Injective.under F)
  letI : TopCat.Sheaf.IsFlasque
      (S.map (underlyingAdditiveSheafFunctor X)).X₁ := by
    change TopCat.Presheaf.IsFlasque F.val.presheaf
    infer_instance
  have htopEpi : Epi
      ((S.map (underlyingAdditiveSheafFunctor X)).g.hom.app
        (op (⊤ : Opens X))) :=
    TopCat.Sheaf.IsFlasque.epi_of_shortExact hT
  have htopSurj : Function.Surjective
      ((S.map (underlyingAdditiveSheafFunctor X)).g.hom.app
        (op (⊤ : Opens X))) :=
    (AddCommGrpCat.epi_iff_surjective _).mp htopEpi
  have hsectionSurj : Function.Surjective
      (SheafOfModules.sectionsMap S.g) := by
    apply sectionsMap_surjective_of_top_surjective X S.g
    exact htopSurj
  have hzeroSurj : Function.Surjective
      (schemeModuleCohomologyMap X S.g 0) :=
    schemeModuleCohomologyMap_zero_surjective_of_sectionsMap X S.g hsectionSurj
  letI : Subsingleton (schemeModuleCohomology X S.X₂ 1) := by
    dsimp [S]
    exact Ext.subsingleton_of_injective
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
      (Injective.under F) 0
  exact schemeModuleCohomology_one_subsingleton_of_zero_map_surjective
    X S hS hzeroSurj

end PfaffianDescent

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits Opposite
open TopCat TopologicalSpace
open AlgebraicGeometry
open CategoryTheory.Abelian

variable (X : Scheme.{u}) [EnoughInjectives X.Modules] [HasExt.{u} X.Modules]

/-- A flasque scheme module has vanishing second Ext from the structure sheaf. -/
theorem flasque_schemeModuleCohomology_two (F : X.Modules)
    [TopCat.Presheaf.IsFlasque F.val.presheaf] :
    Subsingleton (schemeModuleCohomology X F 2) := by
  let j : F ⟶ Injective.under F := Injective.ι F
  let S := ShortComplex.mk j (cokernel.π j) (cokernel.condition j)
  have hS : S.ShortExact := by
    dsimp [S]
    exact { exact := ShortComplex.exact_cokernel j }
  have hT := shortExact_underlyingAdditiveSheaf X S hS
  letI : TopCat.Sheaf.IsFlasque
      (S.map (underlyingAdditiveSheafFunctor X)).X₁ := by
    change TopCat.Presheaf.IsFlasque F.val.presheaf
    infer_instance
  letI hIflasque : TopCat.Presheaf.IsFlasque (Injective.under F).val.presheaf :=
    injective_isFlasque_scheme X (Injective.under F)
  letI : TopCat.Sheaf.IsFlasque
      (S.map (underlyingAdditiveSheafFunctor X)).X₂ := by
    change TopCat.Presheaf.IsFlasque (Injective.under F).val.presheaf
    infer_instance
  letI hQflasqueSheaf : TopCat.Sheaf.IsFlasque
      (S.map (underlyingAdditiveSheafFunctor X)).X₃ :=
    TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hT
  letI hQflasque : TopCat.Presheaf.IsFlasque S.X₃.val.presheaf := by
    exact hQflasqueSheaf
  letI : Subsingleton (schemeModuleCohomology X S.X₃ 1) :=
    flasque_schemeModuleCohomology_one X S.X₃
  have hsurj : Function.Surjective (schemeModuleCohomologyMap X S.g 1) := by
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩
  letI : Subsingleton (schemeModuleCohomology X S.X₂ 2) := by
    dsimp [S]
    exact Ext.subsingleton_of_injective
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
      (Injective.under F) 1
  exact schemeModuleCohomology_succ_subsingleton_of_map_surjective
    X S hS 1 hsurj

/-- A flasque scheme module has vanishing cohomology in every positive
degree.  The induction uses the injective embedding of the module; its
cokernel is again flasque by exactness of the underlying additive sheaves. -/
theorem flasque_schemeModuleCohomology_succ (F : X.Modules)
    [TopCat.Presheaf.IsFlasque F.val.presheaf] (n : ℕ) :
    Subsingleton (schemeModuleCohomology X F (n + 1)) := by
  induction n generalizing F with
  | zero =>
      simpa using flasque_schemeModuleCohomology_one X F
  | succ n ih =>
      let j : F ⟶ Injective.under F := Injective.ι F
      let S := ShortComplex.mk j (cokernel.π j) (cokernel.condition j)
      have hS : S.ShortExact := by
        dsimp [S]
        exact { exact := ShortComplex.exact_cokernel j }
      have hT := shortExact_underlyingAdditiveSheaf X S hS
      letI : TopCat.Sheaf.IsFlasque
          (S.map (underlyingAdditiveSheafFunctor X)).X₁ := by
        change TopCat.Presheaf.IsFlasque F.val.presheaf
        infer_instance
      letI hIflasque : TopCat.Presheaf.IsFlasque
          (Injective.under F).val.presheaf :=
        injective_isFlasque_scheme X (Injective.under F)
      letI : TopCat.Sheaf.IsFlasque
          (S.map (underlyingAdditiveSheafFunctor X)).X₂ := by
        change TopCat.Presheaf.IsFlasque (Injective.under F).val.presheaf
        infer_instance
      letI hQflasqueSheaf : TopCat.Sheaf.IsFlasque
          (S.map (underlyingAdditiveSheafFunctor X)).X₃ :=
        TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hT
      letI hQflasque : TopCat.Presheaf.IsFlasque S.X₃.val.presheaf := by
        exact hQflasqueSheaf
      letI : Subsingleton
          (schemeModuleCohomology X S.X₃ (n + 1)) :=
        ih S.X₃
      letI : Subsingleton
          (schemeModuleCohomology X S.X₂ (n + 1)) := by
        dsimp [S]
        exact Ext.subsingleton_of_injective
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
          (Injective.under F) n
      have hsurj : Function.Surjective
          (schemeModuleCohomologyMap X S.g (n + 1)) := by
        intro y
        exact ⟨0, Subsingleton.elim _ _⟩
      letI : Subsingleton
          (schemeModuleCohomology X S.X₂ ((n + 1) + 1)) := by
        dsimp [S]
        exact Ext.subsingleton_of_injective
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
          (Injective.under F) (n + 1)
      have hvan := schemeModuleCohomology_succ_subsingleton_of_map_surjective
        X S hS (n + 1) hsurj
      simpa [Nat.succ_eq_add_one, add_assoc] using hvan

end PfaffianDescent
