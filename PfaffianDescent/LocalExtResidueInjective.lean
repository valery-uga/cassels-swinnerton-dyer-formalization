import PfaffianDescent.VoisinSheafStalk
import PfaffianDescent.FiniteSupportExtComponents
import PfaffianDescent.ExtMapFixedSource
import PfaffianDescent.SchemeModuleSkyscraper
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# Injectivity of the local complete-intersection residue coordinate

At a closed point of a smooth surface, two regular parameters generate the
maximal ideal.  In that case the standard residue coordinate on the local
degree-two Ext group is injective (indeed, it is an equivalence).
-/

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry
open TopologicalSpace
open scoped nonZeroDivisors

universe w u

variable {R : Type u} [CommRing R] [IsLocalRing R]

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- If every section object below one neighborhood is zero, then the stalk
at the center of that neighborhood is zero. -/
theorem stalk_subsingleton_of_exists_open
    {X : TopCat.{u}} (F : X.Sheaf AddCommGrpCat.{u}) (x : X)
    (V : Opens X) (hxV : x ∈ V)
    (hzero : ∀ (U : Opens X), U ≤ V →
      Subsingleton (F.obj.obj (Opposite.op U))) :
    Subsingleton (F.presheaf.stalk x) := by
  constructor
  intro a b
  obtain ⟨U, hUV, hxU, s, hs⟩ := F.presheaf.exists_le_germ_eq a hxV
  obtain ⟨W, hWV, hxW, t, ht⟩ := F.presheaf.exists_le_germ_eq b hxV
  rw [← hs, ← ht]
  letI : Subsingleton (F.obj.obj (Opposite.op U)) := hzero U hUV
  letI : Subsingleton (F.obj.obj (Opposite.op W)) := hzero W hWV
  rw [Subsingleton.elim s 0, Subsingleton.elim t 0]
  change F.presheaf.germ U x hxU 0 = F.presheaf.germ W x hxW 0
  rw [map_zero, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The pushforward of a sheaf of abelian groups along a closed embedding has
zero stalk away from the closed image. -/
theorem pushforward_stalk_subsingleton_of_isClosedEmbedding
    {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : Topology.IsClosedEmbedding f)
    (F : X.Sheaf AddCommGrpCat.{u}) (y : Y)
    (hy : y ∉ Set.range f) :
    Subsingleton
      (((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F).presheaf.stalk y) := by
  let V : Opens Y := ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩
  apply stalk_subsingleton_of_exists_open
    ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) y V hy
  intro U hUV
  have hpre : (Opens.map f).obj U = ⊥ := by
    ext z
    change (f z ∈ U) ↔ False
    constructor
    · intro hz
      exact (hUV hz) ⟨z, rfl⟩
    · intro hz
      exact hz.elim
  change Subsingleton (F.obj.obj (Opposite.op ((Opens.map f).obj U)))
  exact AddCommGrpCat.subsingleton_of_isZero
    ((F.isTerminalOfEqEmpty hpre).isZero)

set_option backward.isDefEq.respectTransparency false in
/-- Scheme-module form of the off-image vanishing theorem: a module
pushforward along a closed immersion has zero stalk away from the image. -/
theorem schemeModulePushforward_stalk_subsingleton_off_range
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (M : X.Modules) (y : Y) (hy : y ∉ Set.range f) :
    Subsingleton (((Scheme.Modules.pushforward f).obj M).presheaf.stalk y) := by
  exact pushforward_stalk_subsingleton_of_isClosedEmbedding
    f.base f.isClosedEmbedding
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) y hy

/-- A map of scheme modules is invertible when it is invertible on every
stalk. -/
theorem schemeModuleMap_isIso_of_stalk
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ x : X, IsIso ((schemeModuleStalkModuleFunctor X x).map f)) :
    IsIso f := by
  have hsheaf : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map f) := by
    apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
    intro x
    letI : IsIso ((schemeModuleStalkModuleFunctor X x).map f) := h x
    exact Functor.map_isIso
      (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat)
      ((schemeModuleStalkModuleFunctor X x).map f)
  letI : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map f) := hsheaf
  letI (U : (Opens X)ᵒᵖ) :
      IsIso (((Scheme.Modules.toPresheaf X).map f).app U) := by
    change IsIso (((SheafOfModules.toSheaf X.ringCatSheaf).map f).hom.app U)
    infer_instance
  suffices IsIso ((Scheme.Modules.toPresheaf X).map f) by
    exact isIso_of_reflects_iso f (Scheme.Modules.toPresheaf X)
  exact NatIso.isIso_of_isIso_app _

/-- Tensoring a closed-immersion pushforward with a module that is trivial on
an open cover does not enlarge its support.  This form works for an arbitrary
closed subscheme, rather than only a field-valued point. -/
theorem closedImmersionPushforwardTwist_stalk_subsingleton_off_range_of_coversTop_iso_unit
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) {I : Type u} (U : I → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    (eU : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (U j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (U j))))
    (y : X) (hy : y ∉ Set.range i) :
    Subsingleton ((closedImmersionIdealTwistSequence i T).X₃.presheaf.stalk y) := by
  have hcover : TopologicalSpace.IsOpenCover U :=
    (Opens.coversTop_iff X U).mp hU
  have hyCover : y ∈ ⨆ j, U j := by
    rw [hcover.iSup_eq_top]
    trivial
  rw [TopologicalSpace.Opens.mem_iSup] at hyCover
  obtain ⟨j, hyU⟩ := hyCover
  let yU : U j := ⟨y, hyU⟩
  change Subsingleton
    ((schemeModuleTensor
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) T).presheaf.stalk y)
  apply schemeModuleTensor_stalk_subsingleton_of_localTrivialization
    (U j) yU _ T (eU j)
  exact schemeModulePushforward_stalk_subsingleton_off_range i
    (SheafOfModules.unit Z.ringCatSheaf) y hy

/-- If the twisting module is globally trivial, the quotient term of the
twisted closed-immersion sequence is the actual pushforward module. -/
noncomputable def closedImmersionPushforwardTwistIsoOfIsoUnit
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) (eT : T ≅ SheafOfModules.unit X.ringCatSheaf) :
    (closedImmersionIdealTwistSequence i T).X₃ ≅
      (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf) := by
  change (schemeModuleTensorRight T).obj
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) ≅ _
  exact (schemeModuleTensorRightIsoUnit eT).app _

set_option linter.style.haveILetI false in
/-- Subsingleton stalks transport backwards across an isomorphism of scheme
modules. -/
theorem schemeModule_stalk_subsingleton_of_iso
    {X : Scheme.{u}} (x : X) {M N : X.Modules} (e : M ≅ N)
    (hN : Subsingleton (N.presheaf.stalk x)) :
    Subsingleton (M.presheaf.stalk x) := by
  letI : Subsingleton (N.presheaf.stalk x) := hN
  let es := (schemeModuleStalkModuleFunctor X x).mapIso e
  have hN' : Subsingleton ((schemeModuleStalkModuleFunctor X x).obj N) := by
    change Subsingleton (N.presheaf.stalk x)
    exact hN
  constructor
  intro a b
  apply (ConcreteCategory.bijective_of_isIso es.hom).injective
  exact @Subsingleton.elim _ hN' _ _

set_option linter.style.haveILetI false in
/-- The globally trivially twisted quotient sheaf of a closed field-valued
point has zero stalk at every other point. -/
theorem fieldPointPushforwardTwist_stalk_subsingleton_off
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) (eT : T ≅ SheafOfModules.unit X.ringCatSheaf)
    (y : X) (hy : y ≠ i default) :
    Subsingleton
      ((closedImmersionIdealTwistSequence i T).X₃.presheaf.stalk y) := by
  apply schemeModule_stalk_subsingleton_of_iso y
    (closedImmersionPushforwardTwistIsoOfIsoUnit i T eT)
  apply schemeModulePushforward_stalk_subsingleton_off_range
  intro hyRange
  obtain ⟨z, rfl⟩ := hyRange
  apply hy
  exact congr_arg i (Subsingleton.elim z default)

/-- A line-bundle twist of a closed field point is still supported at that
point.  Unlike `fieldPointPushforwardTwist_stalk_subsingleton_off`, this
version uses trivializations on an open cover and does not require the twist
to be globally trivial. -/
theorem fieldPointPushforwardTwist_stalk_subsingleton_off_of_coversTop_iso_unit
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) {I : Type u} (U : I → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    (eU : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (U j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (U j))))
    (y : X) (hy : y ≠ i default) :
    Subsingleton
      ((closedImmersionIdealTwistSequence i T).X₃.presheaf.stalk y) := by
  have hcover : TopologicalSpace.IsOpenCover U :=
    (Opens.coversTop_iff X U).mp hU
  have hyCover : y ∈ ⨆ j, U j := by
    rw [hcover.iSup_eq_top]
    trivial
  rw [TopologicalSpace.Opens.mem_iSup] at hyCover
  obtain ⟨j, hyU⟩ := hyCover
  let yU : U j := ⟨y, hyU⟩
  change Subsingleton
    ((schemeModuleTensor
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T).presheaf.stalk y)
  apply schemeModuleTensor_stalk_subsingleton_of_localTrivialization
    (U j) yU _ T (eU j)
  apply schemeModulePushforward_stalk_subsingleton_off_range
  intro hyRange
  obtain ⟨z, hz⟩ := hyRange
  apply hy
  exact (show y = (U j).ι yU from rfl) |>.trans <|
    hz.symm.trans (congr_arg i (Subsingleton.elim z default))

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- A morphism from a scheme module supported at a single point is
determined by its stalk at that point.  The support condition is stated in
the precise form needed here: every other source stalk is subsingleton. -/
theorem schemeModuleStalkModuleFunctor_map_injective_of_subsingleton_off
    {X : Scheme.{u}} (x : X) (M N : X.Modules)
    (hM : ∀ y : X, y ≠ x → Subsingleton (M.presheaf.stalk y)) :
    Function.Injective
      (fun f : M ⟶ N ↦ (schemeModuleStalkModuleFunctor X x).map f) := by
  intro f g hfg
  apply Scheme.Modules.hom_ext f g
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  apply TopCat.Presheaf.section_ext
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj N) U
      (f.app U s) (g.app U s)
  intro y hy
  change N.presheaf.germ U y hy (f.app U s) =
    N.presheaf.germ U y hy (g.app U s)
  have hfGerm := TopCat.Presheaf.stalkFunctor_map_germ_apply
    U y hy f.mapPresheaf s
  have hgGerm := TopCat.Presheaf.stalkFunctor_map_germ_apply
    U y hy g.mapPresheaf s
  simp only [Scheme.Modules.mapPresheaf_app] at hfGerm hgGerm
  rw [← hfGerm, ← hgGerm]
  by_cases hyx : y = x
  · subst y
    exact DFunLike.congr_fun (congr_arg ConcreteCategory.hom hfg) _
  · haveI : Subsingleton (M.presheaf.stalk y) := hM y hyx
    have hs : M.presheaf.germ U y hy s = 0 := Subsingleton.elim _ _
    rw [hs]
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
      f.mapPresheaf).hom 0 =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
        g.mapPresheaf).hom 0
    rw [map_zero, map_zero]

set_option linter.style.haveILetI false in
/-- Morphisms from a module supported at one point to a module whose stalk
at that point is zero vanish.  This is the degree-zero part of the
disjoint-support Ext statement needed below. -/
theorem schemeModule_hom_subsingleton_of_subsingleton_off_of_stalk_isZero
    {X : Scheme.{u}} (x : X) (M K : X.Modules)
    (hM : ∀ y : X, y ≠ x → Subsingleton (M.presheaf.stalk y))
    (hK : IsZero ((schemeModuleStalkModuleFunctor X x).obj K)) :
    Subsingleton (M ⟶ K) := by
  constructor
  intro f g
  apply schemeModuleStalkModuleFunctor_map_injective_of_subsingleton_off
    x M K hM
  haveI : Subsingleton ((schemeModuleStalkModuleFunctor X x).obj K) :=
    ModuleCat.subsingleton_of_isZero hK
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact Subsingleton.elim _ _

set_option linter.style.haveILetI false in
/-- Degree-zero Ext vanishes for a source supported at one point and a
target with zero stalk there. -/
theorem schemeModule_ext_zero_subsingleton_of_subsingleton_off_of_stalk_isZero
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    (M K : X.Modules)
    (hM : ∀ y : X, y ≠ x → Subsingleton (M.presheaf.stalk y))
    (hK : IsZero ((schemeModuleStalkModuleFunctor X x).obj K)) :
    Subsingleton (Ext M K 0) := by
  letI : Subsingleton (M ⟶ K) :=
    schemeModule_hom_subsingleton_of_subsingleton_off_of_stalk_isZero
      x M K hM hK
  exact Ext.homEquiv₀.injective.subsingleton

/-- The explicit off-point kernel in the stalk comparison has vanishing
degree-zero Ext from every source supported at the center. -/
theorem schemeModuleToSkyscraper_kernel_ext_zero_subsingleton
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    (M N : X.Modules)
    (hM : ∀ y : X, y ≠ x → Subsingleton (M.presheaf.stalk y)) :
    Subsingleton (Ext M
      (kernel (schemeModuleToSkyscraper x
        (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N)))) 0) :=
  schemeModule_ext_zero_subsingleton_of_subsingleton_off_of_stalk_isZero
    x M _ hM (schemeModuleToSkyscraper_kernel_stalk_isZero x N)

/-- For the actual quotient term supported at a closed field-valued point,
the Hom comparison with the stalk is injective. -/
theorem fieldPointPushforwardTwist_stalkHom_injective
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) (eT : T ≅ SheafOfModules.unit X.ringCatSheaf)
    (N : X.Modules) :
    Function.Injective
      (fun f : (closedImmersionIdealTwistSequence i T).X₃ ⟶ N ↦
        (schemeModuleStalkModuleFunctor X (i default)).map f) := by
  exact schemeModuleStalkModuleFunctor_map_injective_of_subsingleton_off
    (i default) (closedImmersionIdealTwistSequence i T).X₃ N
    (fun y hy ↦ fieldPointPushforwardTwist_stalk_subsingleton_off
      i T eT y hy)

/-- Hom comparison for a locally trivial twist.  The open-cover
trivializations supply the point-support statement used to detect a sheaf
morphism on the center stalk. -/
theorem fieldPointPushforwardTwist_stalkHom_injective_of_coversTop_iso_unit
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) {I : Type u} (U : I → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    (eU : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (U j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (U j))))
    (N : X.Modules) :
    Function.Injective
      (fun f : (closedImmersionIdealTwistSequence i T).X₃ ⟶ N ↦
        (schemeModuleStalkModuleFunctor X (i default)).map f) := by
  exact schemeModuleStalkModuleFunctor_map_injective_of_subsingleton_off
    (i default) (closedImmersionIdealTwistSequence i T).X₃ N
    (fun y hy ↦
      fieldPointPushforwardTwist_stalk_subsingleton_off_of_coversTop_iso_unit
        i T U hU eU y hy)

/-- The image point of a closed immersion from the spectrum of a field is a
closed point of the target scheme. -/
theorem fieldPoint_image_isClosed
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i] :
    IsClosed ({i default} : Set X) := by
  have hrange : Set.range i = ({i default} : Set X) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      simp only [Set.mem_singleton_iff]
      exact congr_arg i (Subsingleton.elim z default)
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      exact ⟨default, hy.symm⟩
  rw [← hrange]
  exact i.isClosedEmbedding.isClosed_range

/-- A globally trivially twisted quotient at a closed field-valued point is
canonically its scheme-module skyscraper. -/
theorem fieldPointPushforwardTwist_toSkyscraper_isIso
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) (eT : T ≅ SheafOfModules.unit X.ringCatSheaf) :
    IsIso (schemeModuleToSkyscraper (i default)
      (𝟙 ((schemeModuleStalkModuleFunctor X (i default)).obj
        (closedImmersionIdealTwistSequence i T).X₃))) := by
  exact schemeModuleToSkyscraper_isIso_of_subsingleton_off
    (i default) (closedImmersionIdealTwistSequence i T).X₃
    (fieldPoint_image_isClosed i)
    (fun y hy ↦ fieldPointPushforwardTwist_stalk_subsingleton_off
      i T eT y hy)

/-- The quotient twisted by a locally trivial line bundle is canonically
its skyscraper at the closed field point. -/
theorem fieldPointPushforwardTwist_toSkyscraper_isIso_of_coversTop_iso_unit
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) {I : Type u} (U : I → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    (eU : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (U j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (U j)))) :
    IsIso (schemeModuleToSkyscraper (i default)
      (𝟙 ((schemeModuleStalkModuleFunctor X (i default)).obj
        (closedImmersionIdealTwistSequence i T).X₃))) := by
  exact schemeModuleToSkyscraper_isIso_of_subsingleton_off
    (i default) (closedImmersionIdealTwistSequence i T).X₃
    (fieldPoint_image_isClosed i)
    (fun y hy ↦
      fieldPointPushforwardTwist_stalk_subsingleton_off_of_coversTop_iso_unit
        i T U hU eU y hy)

/-- Explicit skyscraper identification for the point-supported quotient used
in the residue calculation. -/
noncomputable def fieldPointPushforwardTwist_skyscraperIso
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) (eT : T ≅ SheafOfModules.unit X.ringCatSheaf) :
    (closedImmersionIdealTwistSequence i T).X₃ ≅
      schemeModuleSkyscraper (i default)
        ((schemeModuleStalkModuleFunctor X (i default)).obj
          (closedImmersionIdealTwistSequence i T).X₃) := by
  letI := fieldPointPushforwardTwist_toSkyscraper_isIso i T eT
  exact asIso (schemeModuleToSkyscraper (i default) (𝟙 _))

/-- Explicit skyscraper identification for a quotient twisted by a sheaf
which is trivial on the supplied open cover. -/
noncomputable def
    fieldPointPushforwardTwist_skyscraperIso_of_coversTop_iso_unit
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) {I : Type u} (U : I → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    (eU : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (U j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (U j)))) :
    (closedImmersionIdealTwistSequence i T).X₃ ≅
      schemeModuleSkyscraper (i default)
        ((schemeModuleStalkModuleFunctor X (i default)).obj
          (closedImmersionIdealTwistSequence i T).X₃) := by
  letI :=
    fieldPointPushforwardTwist_toSkyscraper_isIso_of_coversTop_iso_unit
      i T U hU eU
  exact asIso (schemeModuleToSkyscraper (i default) (𝟙 _))

/-- The global target map to the skyscraper of a closed-point stalk is
injective on Ext when every class into its off-point kernel becomes zero
after composition with the kernel inclusion.  This is the exact image-zero
condition supplied by the long exact Ext sequence. -/
theorem schemeModuleExt_toSkyscraper_injective_of_kernel_image_zero
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    [HasExt.{u} X.Modules]
    (M N : X.Modules) (n : ℕ)
    (hzero : ∀ k : Ext M
      (kernel (schemeModuleToSkyscraper x
        (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N)))) n,
      k.comp (Ext.mk₀ (kernel.ι (schemeModuleToSkyscraper x
        (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N))))) (add_zero n) = 0) :
    Function.Injective
      (fun z : Ext M N n ↦ z.comp
        (Ext.mk₀ (schemeModuleToSkyscraper x
          (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N))))
        (add_zero n)) := by
  let f := schemeModuleToSkyscraper x
    (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N))
  letI : Epi f := schemeModuleToSkyscraper_epi_of_isClosed x N hx
  exact ext_postcomp_epi_injective_of_kernel_image_zero M f n hzero

/-- Exact kernel-image characterization of injectivity for the canonical
map from a scheme module to the skyscraper of one closed-point stalk. -/
theorem schemeModuleExt_toSkyscraper_injective_iff_kernel_image_zero
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    [HasExt.{u} X.Modules]
    (M N : X.Modules) (n : ℕ) :
    Function.Injective
      (fun z : Ext M N n ↦ z.comp
        (Ext.mk₀ (schemeModuleToSkyscraper x
          (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N))))
        (add_zero n)) ↔
      ∀ k : Ext M
        (kernel (schemeModuleToSkyscraper x
          (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N)))) n,
        k.comp (Ext.mk₀ (kernel.ι (schemeModuleToSkyscraper x
          (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N))))) (add_zero n) = 0 := by
  let f := schemeModuleToSkyscraper x
    (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N))
  letI : Epi f := schemeModuleToSkyscraper_epi_of_isClosed x N hx
  exact ext_postcomp_epi_injective_iff_kernel_image_zero M f n

attribute [local instance] Ext.subsingleton_of_injective in
/-- Vanishing of Ext into the off-point kernel implies the precise
kernel-image condition and hence injectivity of the global target map. -/
theorem schemeModuleExt_toSkyscraper_injective_of_kernel_ext_subsingleton
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    [HasExt.{u} X.Modules]
    (M N : X.Modules) (n : ℕ)
    [Subsingleton (Ext M
      (kernel (schemeModuleToSkyscraper x
        (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N)))) n)] :
    Function.Injective
      (fun z : Ext M N n ↦ z.comp
        (Ext.mk₀ (schemeModuleToSkyscraper x
          (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N))))
        (add_zero n)) := by
  apply schemeModuleExt_toSkyscraper_injective_of_kernel_image_zero x hx M N n
  intro k
  rw [Subsingleton.elim k 0]
  exact Ext.zero_comp _ _ _ _ _

set_option linter.style.haveILetI false in
/-- The Ext map from local modules to their scheme-module skyscrapers.  The
closedness hypothesis supplies the exactness instances used internally by
`mapExtAddHom`. -/
noncomputable def schemeModuleSkyscraperExtMap
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    [HasExt.{u + 1} (ModuleCat.{u} (X.presheaf.stalk x))]
    [HasExt.{u} X.Modules]
    (A B : ModuleCat.{u} (X.presheaf.stalk x)) (n : ℕ) :
    Ext A B n →+ Ext (schemeModuleSkyscraper x A)
      (schemeModuleSkyscraper x B) n := by
  letI : PreservesFiniteLimits (schemeModuleSkyscraperFunctor X x) :=
    schemeModuleSkyscraperFunctorPreservesFiniteLimits x hx
  letI : PreservesFiniteColimits (schemeModuleSkyscraperFunctor X x) :=
    schemeModuleSkyscraperFunctorPreservesFiniteColimits x hx
  exact (schemeModuleSkyscraperFunctor X x).mapExtAddHom A B n

set_option linter.style.haveILetI false in
attribute [local instance] Ext.subsingleton_of_injective in
/-- At a closed point, the exact fully faithful skyscraper functor induces
a bijection on Ext groups in every degree. -/
theorem schemeModuleSkyscraperExtMap_bijective
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    [HasExt.{u + 1} (ModuleCat.{u} (X.presheaf.stalk x))]
    [HasExt.{u} X.Modules]
    (A B : ModuleCat.{u} (X.presheaf.stalk x)) (n : ℕ) :
    Function.Bijective (schemeModuleSkyscraperExtMap x hx A B n) := by
  letI : EnoughInjectives (ModuleCat.{u} (X.presheaf.stalk x)) :=
    @ModuleCat.enoughInjectives.{u, u}
      (X.presheaf.stalk x) inferInstance
  let G := schemeModuleSkyscraperFunctor X x
  let hff := schemeModuleSkyscraperFunctorFullyFaithful X x
  letI : G.Full := hff.full
  letI : G.Faithful := hff.faithful
  letI : PreservesFiniteLimits G :=
    schemeModuleSkyscraperFunctorPreservesFiniteLimits x hx
  letI : PreservesFiniteColimits G :=
    schemeModuleSkyscraperFunctorPreservesFiniteColimits x hx
  change Function.Bijective (G.mapExtAddHom A B n)
  exact Functor.mapExt_bijective_of_preservesInjectiveObjects G A B n

/-- The derived adjunction comparison from Ext into a skyscraper to Ext over
the local ring. -/
noncomputable def schemeModuleStalkSkyscraperExtMap
    {X : Scheme.{u}} (x : X)
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat.{u} (X.presheaf.stalk x))]
    (M : X.Modules) (A : ModuleCat.{u} (X.presheaf.stalk x)) (n : ℕ) :
    Ext M (schemeModuleSkyscraper x A) n →+
      Ext ((schemeModuleStalkModuleFunctor X x).obj M) A n :=
  adjunctionExtAddHom
    (schemeModuleStalkModuleFunctor X x)
    (schemeModuleSkyscraperFunctor X x)
    (schemeModuleStalkSkyscraperAdjunction X x) M A n

set_option linter.style.haveILetI false in
attribute [local instance] Ext.subsingleton_of_injective in
/-- At a closed point, the derived stalk--skyscraper adjunction comparison
is bijective in every Ext degree. -/
theorem schemeModuleStalkSkyscraperExtMap_bijective
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat.{u} (X.presheaf.stalk x))]
    (M : X.Modules) (A : ModuleCat.{u} (X.presheaf.stalk x)) (n : ℕ) :
    Function.Bijective (schemeModuleStalkSkyscraperExtMap x M A n) := by
  letI : EnoughInjectives (ModuleCat.{u} (X.presheaf.stalk x)) :=
    @ModuleCat.enoughInjectives.{u, u}
      (X.presheaf.stalk x) inferInstance
  letI : PreservesFiniteLimits (schemeModuleSkyscraperFunctor X x) :=
    schemeModuleSkyscraperFunctorPreservesFiniteLimits x hx
  letI : PreservesFiniteColimits (schemeModuleSkyscraperFunctor X x) :=
    schemeModuleSkyscraperFunctorPreservesFiniteColimits x hx
  change Function.Bijective (adjunctionExtAddHom
    (schemeModuleStalkModuleFunctor X x)
    (schemeModuleSkyscraperFunctor X x)
    (schemeModuleStalkSkyscraperAdjunction X x) M A n)
  exact adjunctionExtAddHom_bijective
    (schemeModuleStalkModuleFunctor X x)
    (schemeModuleSkyscraperFunctor X x)
    (schemeModuleStalkSkyscraperAdjunction X x) M A n

attribute [local simp] Ext.mapExactFunctor_comp Ext.mapExactFunctor_mk₀ in
set_option backward.isDefEq.respectTransparency false in
/-- The ordinary map on Ext induced by taking the stalk factors through the
canonical map to the skyscraper of the target stalk and the derived
stalk--skyscraper adjunction comparison. -/
theorem schemeModuleStalkModuleExtMap_factorization
    {X : Scheme.{u}} (x : X)
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat.{u} (X.presheaf.stalk x))]
    (M N : X.Modules) (n : ℕ) (z : Ext M N n) :
    schemeModuleStalkModuleExtMap X x M N n z =
      schemeModuleStalkSkyscraperExtMap x M
        ((schemeModuleStalkModuleFunctor X x).obj N) n
        (z.comp (Ext.mk₀ (schemeModuleToSkyscraper x
          (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N)))) (add_zero n)) := by
  let F := schemeModuleStalkModuleFunctor X x
  let adj := schemeModuleStalkSkyscraperAdjunction X x
  dsimp [schemeModuleStalkSkyscraperExtMap,
    adjunctionExtAddHom, schemeModuleStalkModuleExtMap]
  simp only [Ext.bilinearComp_apply_apply]
  change z.mapExactFunctor F =
    ((z.comp (Ext.mk₀ (schemeModuleToSkyscraper x (𝟙 (F.obj N))))
      (add_zero n)).mapExactFunctor F).comp
        (Ext.mk₀ (adj.counit.app (F.obj N))) (add_zero n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  have htri := adj.left_triangle_components N
  rw [schemeModuleStalkSkyscraperAdjunction_unit_app,
    schemeModuleStalkSkyscraperAdjunction_counit_app] at htri
  change F.map (schemeModuleToSkyscraper x (𝟙 (F.obj N))) ≫
      schemeModuleSkyscraperStalkLinearMap x (F.obj N) = 𝟙 (F.obj N) at htri
  rw [schemeModuleStalkSkyscraperAdjunction_counit_app]
  rw [htri, Ext.comp_mk₀_id]

set_option linter.style.haveILetI false in
/-- At a closed point, injectivity of the global-to-local Ext map follows
from the exact kernel-image-zero condition for the target's canonical map to
the skyscraper of its stalk. -/
theorem schemeModuleStalkModuleExtMap_injective_of_kernel_image_zero
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat.{u} (X.presheaf.stalk x))]
    (M N : X.Modules) (n : ℕ)
    (hzero : ∀ k : Ext M
      (kernel (schemeModuleToSkyscraper x
        (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N)))) n,
      k.comp (Ext.mk₀ (kernel.ι (schemeModuleToSkyscraper x
        (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N))))) (add_zero n) = 0) :
    Function.Injective (schemeModuleStalkModuleExtMap X x M N n) := by
  intro z z' hzz'
  apply schemeModuleExt_toSkyscraper_injective_of_kernel_image_zero
    x hx M N n hzero
  apply (schemeModuleStalkSkyscraperExtMap_bijective x hx M
    ((schemeModuleStalkModuleFunctor X x).obj N) n).injective
  rw [← schemeModuleStalkModuleExtMap_factorization x M N n z,
    ← schemeModuleStalkModuleExtMap_factorization x M N n z', hzz']

set_option linter.style.haveILetI false in
/-- For a closed point, the kernel-image-zero condition is exactly
equivalent to injectivity of the global-to-stalk Ext map.  The reverse
direction uses the factorization through the derived stalk--skyscraper
adjunction, whose second map is bijective. -/
theorem schemeModuleStalkModuleExtMap_injective_iff_kernel_image_zero
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat.{u} (X.presheaf.stalk x))]
    (M N : X.Modules) (n : ℕ) :
    Function.Injective (schemeModuleStalkModuleExtMap X x M N n) ↔
      ∀ k : Ext M
        (kernel (schemeModuleToSkyscraper x
          (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N)))) n,
        k.comp (Ext.mk₀ (kernel.ι (schemeModuleToSkyscraper x
          (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N))))) (add_zero n) = 0 := by
  constructor
  · intro hinj
    apply (schemeModuleExt_toSkyscraper_injective_iff_kernel_image_zero
      x hx M N n).mp
    intro z z' hzz'
    apply hinj
    rw [schemeModuleStalkModuleExtMap_factorization x M N n z,
      schemeModuleStalkModuleExtMap_factorization x M N n z']
    exact congrArg
      (schemeModuleStalkSkyscraperExtMap x M
        ((schemeModuleStalkModuleFunctor X x).obj N) n) hzz'
  · exact schemeModuleStalkModuleExtMap_injective_of_kernel_image_zero
      x hx M N n

attribute [local instance] Ext.subsingleton_of_injective in
set_option linter.style.haveILetI false in
/-- Vanishing of Ext into the explicit comparison kernel is a sufficient
condition for the exact kernel-image criterion. -/
theorem schemeModuleStalkModuleExtMap_injective_of_kernel_ext_subsingleton
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat.{u} (X.presheaf.stalk x))]
    (M N : X.Modules) (n : ℕ)
    [Subsingleton (Ext M
      (kernel (schemeModuleToSkyscraper x
        (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N)))) n)] :
    Function.Injective (schemeModuleStalkModuleExtMap X x M N n) := by
  apply schemeModuleStalkModuleExtMap_injective_of_kernel_image_zero
    x hx M N n
  intro k
  rw [Subsingleton.elim k 0]
  exact Ext.zero_comp _ _ _ _ _

set_option linter.style.haveILetI false in
attribute [local instance] Ext.subsingleton_of_injective in
/-- The global-to-stalk comparison is injective in degree zero for every
source supported at a closed point.  This verifies the base degree of the
local-to-global Ext statement independently of any coherence hypothesis. -/
theorem schemeModuleStalkModuleExtMap_zero_injective_of_subsingleton_off
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat.{u} (X.presheaf.stalk x))]
    (M N : X.Modules)
    (hM : ∀ y : X, y ≠ x → Subsingleton (M.presheaf.stalk y)) :
    Function.Injective (schemeModuleStalkModuleExtMap X x M N 0) := by
  letI : Subsingleton (Ext M
      (kernel (schemeModuleToSkyscraper x
        (𝟙 ((schemeModuleStalkModuleFunctor X x).obj N)))) 0) :=
    schemeModuleToSkyscraper_kernel_ext_zero_subsingleton x M N hM
  exact schemeModuleStalkModuleExtMap_injective_of_kernel_ext_subsingleton
    x hx M N 0

/-- A point-supported stalk comparison in degree zero, together with
preservation of injectives by the stalk functor, upgrades to a bijection in
every Ext degree.  This reduces the remaining global-to-local issue to the
concrete support behavior of morphisms and injective sheaves. -/
theorem schemeModuleStalkModuleExtMap_bijective_of_fixedSourceHom
    {X : Scheme.{u}} (x : X)
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    [EnoughInjectives X.Modules]
    [(schemeModuleStalkModuleFunctor X x).PreservesInjectiveObjects]
    (M : X.Modules)
    (hHom : ∀ N : X.Modules, Function.Bijective
      (fun f : M ⟶ N ↦ (schemeModuleStalkModuleFunctor X x).map f))
    (N : X.Modules) (n : ℕ) :
    Function.Bijective (schemeModuleStalkModuleExtMap X x M N n) := by
  exact mapExt_bijective_fixed_source
    (schemeModuleStalkModuleFunctor X x) M hHom N n

/-- Stalk specialization of the acyclic fixed-source comparison.  It is
enough that stalks of injective scheme modules have no positive Ext from the
chosen point-supported source; they need not be known to be injective local
modules. -/
theorem schemeModuleStalkModuleExtMap_bijective_of_fixedSourceHom_of_injective_acyclic
    {X : Scheme.{u}} (x : X)
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    [EnoughInjectives X.Modules]
    (M : X.Modules)
    (hHom : ∀ N : X.Modules, Function.Bijective
      (fun f : M ⟶ N ↦ (schemeModuleStalkModuleFunctor X x).map f))
    (hAcyclic : ∀ (I : X.Modules), Injective I → ∀ n : ℕ, 0 < n →
      Subsingleton (CategoryTheory.Abelian.Ext
        ((schemeModuleStalkModuleFunctor X x).obj M)
        ((schemeModuleStalkModuleFunctor X x).obj I) n))
    (N : X.Modules) (n : ℕ) :
    Function.Bijective (schemeModuleStalkModuleExtMap X x M N n) := by
  exact mapExt_bijective_fixed_source_of_injective_acyclic
    (schemeModuleStalkModuleFunctor X x) M hHom hAcyclic N n

/-- For the injectivity needed in Voisin's residue argument, the preceding
comparison uses only positive-degree acyclicity.  At degree two this means
that `Ext¹` from the supported stalk to the stalk of every global injective
vanishes. -/
theorem schemeModuleStalkModuleExtMap_injective_of_fixedSourceHom_of_injective_acyclic
    {X : Scheme.{u}} (x : X)
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    [EnoughInjectives X.Modules]
    (M : X.Modules)
    (hHom : ∀ N : X.Modules, Function.Bijective
      (fun f : M ⟶ N ↦ (schemeModuleStalkModuleFunctor X x).map f))
    (hAcyclic : ∀ (I : X.Modules), Injective I → ∀ n : ℕ, 0 < n →
      Subsingleton (CategoryTheory.Abelian.Ext
        ((schemeModuleStalkModuleFunctor X x).obj M)
        ((schemeModuleStalkModuleFunctor X x).obj I) n))
    (N : X.Modules) (n : ℕ) :
    Function.Injective (schemeModuleStalkModuleExtMap X x M N n) := by
  exact mapExt_injective_fixed_source_of_injective_acyclic
    (schemeModuleStalkModuleFunctor X x) M hHom hAcyclic N n

/-- Exact degree-two stalk criterion used by Voisin's residue argument.  It
requires only the supported-source Hom comparison and vanishing of `Ext¹`
from that source stalk to the stalk of each global injective. -/
theorem schemeModuleStalkModuleExtMap_two_injective_of_fixedSourceHom_of_injective_ext_one
    {X : Scheme.{u}} (x : X)
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    [EnoughInjectives X.Modules]
    (M : X.Modules)
    (hHomInjective : ∀ N : X.Modules, Function.Injective
      (fun f : M ⟶ N ↦ (schemeModuleStalkModuleFunctor X x).map f))
    (hHomSurjectiveOnInjectives : ∀ (I : X.Modules), Injective I →
      Function.Surjective
        (fun f : M ⟶ I ↦ (schemeModuleStalkModuleFunctor X x).map f))
    (hExtOne : ∀ (I : X.Modules), Injective I →
      Subsingleton (CategoryTheory.Abelian.Ext
        ((schemeModuleStalkModuleFunctor X x).obj M)
        ((schemeModuleStalkModuleFunctor X x).obj I) 1))
    (N : X.Modules) :
    Function.Injective (schemeModuleStalkModuleExtMap X x M N 2) := by
  exact mapExt_two_injective_fixed_source_of_injective_ext_one_subsingleton
    (schemeModuleStalkModuleFunctor X x) M hHomInjective
      hHomSurjectiveOnInjectives hExtOne N

/-- Degree-two comparison for a source supported at one point.  The
off-support stalk condition automatically supplies injectivity of the Hom
comparison, leaving only lifting into globally injective targets and local
`Ext¹`-acyclicity as hypotheses. -/
theorem schemeModuleStalkModuleExtMap_two_injective_of_subsingleton_off
    {X : Scheme.{u}} (x : X)
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    [EnoughInjectives X.Modules]
    (M : X.Modules)
    (hM : ∀ y : X, y ≠ x → Subsingleton (M.presheaf.stalk y))
    (hHomSurjectiveOnInjectives : ∀ (I : X.Modules), Injective I →
      Function.Surjective
        (fun f : M ⟶ I ↦ (schemeModuleStalkModuleFunctor X x).map f))
    (hExtOne : ∀ (I : X.Modules), Injective I →
      Subsingleton (CategoryTheory.Abelian.Ext
        ((schemeModuleStalkModuleFunctor X x).obj M)
        ((schemeModuleStalkModuleFunctor X x).obj I) 1))
    (N : X.Modules) :
    Function.Injective (schemeModuleStalkModuleExtMap X x M N 2) := by
  exact schemeModuleStalkModuleExtMap_two_injective_of_fixedSourceHom_of_injective_ext_one
    x M (fun P ↦
      schemeModuleStalkModuleFunctor_map_injective_of_subsingleton_off
        x M P hM) hHomSurjectiveOnInjectives hExtOne N

/-- Actual closed field-point specialization.  Off-support vanishing and Hom
injectivity have been discharged; only lifting stalk morphisms into globally
injective targets and the corresponding local `Ext¹`-acyclicity remain. -/
theorem fieldPointPushforwardTwist_stalkExtTwo_injective_of_injective_lifting_of_ext_one
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) (eT : T ≅ SheafOfModules.unit X.ringCatSheaf)
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i default)))]
    [EnoughInjectives X.Modules]
    (hHomSurjectiveOnInjectives : ∀ (I : X.Modules), Injective I →
      Function.Surjective
        (fun f : (closedImmersionIdealTwistSequence i T).X₃ ⟶ I ↦
          (schemeModuleStalkModuleFunctor X (i default)).map f))
    (hExtOne : ∀ (I : X.Modules), Injective I →
      Subsingleton (CategoryTheory.Abelian.Ext
        ((schemeModuleStalkModuleFunctor X (i default)).obj
          (closedImmersionIdealTwistSequence i T).X₃)
        ((schemeModuleStalkModuleFunctor X (i default)).obj I) 1))
    (N : X.Modules) :
    Function.Injective
      (schemeModuleStalkModuleExtMap X (i default)
        (closedImmersionIdealTwistSequence i T).X₃ N 2) := by
  exact schemeModuleStalkModuleExtMap_two_injective_of_fixedSourceHom_of_injective_ext_one
    (i default) (closedImmersionIdealTwistSequence i T).X₃
    (fun P ↦ fieldPointPushforwardTwist_stalkHom_injective i T eT P)
    hHomSurjectiveOnInjectives hExtOne N

/-- Degree-two stalk comparison for a locally trivial projective twist.
The cover now discharges the full support/Hom-injectivity part, leaving only
lifting into injective sheaves and the local `Ext¹` acyclicity statement. -/
theorem
    fieldPointPushforwardTwist_stalkExtTwo_injective_of_coversTop_iso_unit_of_injective_lifting_of_ext_one
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) {J : Type u} (U : J → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    (eU : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (U j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (U j))))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i default)))]
    [EnoughInjectives X.Modules]
    (hHomSurjectiveOnInjectives : ∀ (I : X.Modules), Injective I →
      Function.Surjective
        (fun f : (closedImmersionIdealTwistSequence i T).X₃ ⟶ I ↦
          (schemeModuleStalkModuleFunctor X (i default)).map f))
    (hExtOne : ∀ (I : X.Modules), Injective I →
      Subsingleton (CategoryTheory.Abelian.Ext
        ((schemeModuleStalkModuleFunctor X (i default)).obj
          (closedImmersionIdealTwistSequence i T).X₃)
        ((schemeModuleStalkModuleFunctor X (i default)).obj I) 1))
    (N : X.Modules) :
    Function.Injective
      (schemeModuleStalkModuleExtMap X (i default)
        (closedImmersionIdealTwistSequence i T).X₃ N 2) := by
  exact schemeModuleStalkModuleExtMap_two_injective_of_fixedSourceHom_of_injective_ext_one
    (i default) (closedImmersionIdealTwistSequence i T).X₃
    (fun P ↦
      fieldPointPushforwardTwist_stalkHom_injective_of_coversTop_iso_unit
        i T U hU eU P)
    hHomSurjectiveOnInjectives hExtOne N

/-- Stalk specialization of the explicit two-presentation comparison. -/
theorem schemeModuleStalkModuleExtMap_two_injective_of_two_presentations
    {X : Scheme.{u}} (x : X)
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (M N : X.Modules) (I₀ : InjectivePresentation N)
    (I₁ : InjectivePresentation (cokernel I₀.f))
    (hExtOne : Subsingleton (CategoryTheory.Abelian.Ext
      ((schemeModuleStalkModuleFunctor X x).obj M)
      ((schemeModuleStalkModuleFunctor X x).obj I₀.J) 1))
    (hHomSurjective : Function.Surjective
      (fun f : M ⟶ I₁.J ↦
        (schemeModuleStalkModuleFunctor X x).map f))
    (hHomInjective : Function.Injective
      (fun f : M ⟶ cokernel I₁.f ↦
        (schemeModuleStalkModuleFunctor X x).map f)) :
    Function.Injective (schemeModuleStalkModuleExtMap X x M N 2) := by
  exact mapExt_two_injective_fixed_source_of_two_presentations
    (schemeModuleStalkModuleFunctor X x) M N I₀ I₁
      hExtOne hHomSurjective hHomInjective

/-- Actual field-point quotient with two chosen injective presentations.
The support theorem supplies the final Hom-injectivity condition, so only one
local `Ext¹` vanishing and one Hom-lifting assertion remain explicit. -/
theorem fieldPointPushforwardTwist_stalkExtTwo_injective_of_two_presentations
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) (eT : T ≅ SheafOfModules.unit X.ringCatSheaf)
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i default)))]
    (N : X.Modules) (I₀ : InjectivePresentation N)
    (I₁ : InjectivePresentation (cokernel I₀.f))
    (hExtOne : Subsingleton (CategoryTheory.Abelian.Ext
      ((schemeModuleStalkModuleFunctor X (i default)).obj
        (closedImmersionIdealTwistSequence i T).X₃)
      ((schemeModuleStalkModuleFunctor X (i default)).obj I₀.J) 1))
    (hHomSurjective : Function.Surjective
      (fun f : (closedImmersionIdealTwistSequence i T).X₃ ⟶ I₁.J ↦
        (schemeModuleStalkModuleFunctor X (i default)).map f)) :
    Function.Injective
      (schemeModuleStalkModuleExtMap X (i default)
        (closedImmersionIdealTwistSequence i T).X₃ N 2) := by
  exact schemeModuleStalkModuleExtMap_two_injective_of_two_presentations
    (i default) (closedImmersionIdealTwistSequence i T).X₃ N I₀ I₁
      hExtOne hHomSurjective
      (fieldPointPushforwardTwist_stalkHom_injective i T eT
        (cokernel I₁.f))

/-- Two-presentation form of the degree-two comparison for a twist trivial
on an open cover.  The cover supplies the final Hom-injectivity condition. -/
theorem
    fieldPointPushforwardTwist_stalkExtTwo_injective_of_coversTop_iso_unit_of_two_presentations
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) {J : Type u} (U : J → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    (eU : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (U j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (U j))))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i default)))]
    (N : X.Modules) (I₀ : InjectivePresentation N)
    (I₁ : InjectivePresentation (cokernel I₀.f))
    (hExtOne : Subsingleton (CategoryTheory.Abelian.Ext
      ((schemeModuleStalkModuleFunctor X (i default)).obj
        (closedImmersionIdealTwistSequence i T).X₃)
      ((schemeModuleStalkModuleFunctor X (i default)).obj I₀.J) 1))
    (hHomSurjective : Function.Surjective
      (fun f : (closedImmersionIdealTwistSequence i T).X₃ ⟶ I₁.J ↦
        (schemeModuleStalkModuleFunctor X (i default)).map f)) :
    Function.Injective
      (schemeModuleStalkModuleExtMap X (i default)
        (closedImmersionIdealTwistSequence i T).X₃ N 2) := by
  exact schemeModuleStalkModuleExtMap_two_injective_of_two_presentations
    (i default) (closedImmersionIdealTwistSequence i T).X₃ N I₀ I₁
      hExtOne hHomSurjective
      (fieldPointPushforwardTwist_stalkHom_injective_of_coversTop_iso_unit
        i T U hU eU (cokernel I₁.f))

/-- If the two complete-intersection parameters generate the maximal ideal,
the residue coordinate on `Ext²_R(R/(f,g),R)` is injective. -/
theorem localExtTwoResidueCoordinate_injective_of_span_eq_maximalIdeal
    (f g : R) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      (R ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal R)
    (hgm : g ∈ IsLocalRing.maximalIdeal R)
    [HasExt.{w} (ModuleCat R)]
    (hspan : Ideal.span ({f, g} : Set R) =
      IsLocalRing.maximalIdeal R) :
    Function.Injective
      (localExtTwoResidueCoordinate.{u, w} f g hf hg hfm hgm) := by
  intro z z' h
  apply (localExtTwoCoefficientEquiv f g hf hg).symm.injective
  let hle : Ideal.span ({f, g} : Set R) ≤
      IsLocalRing.maximalIdeal R := hspan.le
  change Ideal.Quotient.factor hle
      ((localExtTwoCoefficientEquiv f g hf hg).symm z) =
    Ideal.Quotient.factor hle
      ((localExtTwoCoefficientEquiv f g hf hg).symm z') at h
  apply (Ideal.quotEquivOfEq hspan).injective
  rw [Ideal.quotEquivOfEq_eq_factor, Ideal.quotEquivOfEq_eq_factor]
  exact h

/-- When the two complete-intersection parameters generate the maximal
ideal, the local degree-two Ext group is exactly the residue field: the
canonical residue coordinate is both injective and surjective. -/
theorem localExtTwoResidueCoordinate_bijective_of_span_eq_maximalIdeal
    (f g : R) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      (R ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal R)
    (hgm : g ∈ IsLocalRing.maximalIdeal R)
    [HasExt.{w} (ModuleCat R)]
    (hspan : Ideal.span ({f, g} : Set R) =
      IsLocalRing.maximalIdeal R) :
    Function.Bijective
      (localExtTwoResidueCoordinate.{u, w} f g hf hg hfm hgm) := by
  constructor
  · exact localExtTwoResidueCoordinate_injective_of_span_eq_maximalIdeal
      f g hf hg hfm hgm hspan
  · intro y
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨localSerreExtTwoClass f g c hf hg, by simp⟩

/-- Additive-equivalence form of the complete-intersection residue
calculation.  This is the pointwise equivalence assembled by the
finite-support Serre-duality comparison. -/
noncomputable def localExtTwoResidueCoordinateAddEquiv
    (f g : R) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      (R ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal R)
    (hgm : g ∈ IsLocalRing.maximalIdeal R)
    [HasExt.{w} (ModuleCat R)]
    (hspan : Ideal.span ({f, g} : Set R) =
      IsLocalRing.maximalIdeal R) :
    Ext (ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)))
        (ModuleCat.of R R) 2 ≃+
      R ⧸ IsLocalRing.maximalIdeal R :=
  AddEquiv.ofBijective
    (localExtTwoResidueCoordinate f g hf hg hfm hgm)
    (localExtTwoResidueCoordinate_bijective_of_span_eq_maximalIdeal
      f g hf hg hfm hgm hspan)

@[simp]
theorem localExtTwoResidueCoordinateAddEquiv_apply
    (f g : R) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      (R ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal R)
    (hgm : g ∈ IsLocalRing.maximalIdeal R)
    [HasExt.{w} (ModuleCat R)]
    (hspan : Ideal.span ({f, g} : Set R) =
      IsLocalRing.maximalIdeal R)
    (z : Ext (ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)))
      (ModuleCat.of R R) 2) :
    localExtTwoResidueCoordinateAddEquiv f g hf hg hfm hgm hspan z =
      localExtTwoResidueCoordinate f g hf hg hfm hgm z := rfl

/-- If global-to-stalk Ext is bijective, endpoint transport packages the
local class construction as an additive equivalence. -/
noncomputable def schemeModuleExtLocalClassLargeAddEquiv
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (M N : X.Modules) (f g : X.presheaf.stalk x)
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor X x).obj N ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (hstalk : Function.Bijective
      (schemeModuleStalkModuleExtMap X x M N 2)) :
    Ext.{u} M N 2 ≃+
      Ext.{u + 1}
        (ModuleCat.of (X.presheaf.stalk x)
          ((X.presheaf.stalk x) ⧸ Ideal.span ({f, g} : Set _)))
        (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) 2 :=
  (AddEquiv.ofBijective
      (schemeModuleStalkModuleExtMap X x M N 2) hstalk).trans
    ((extPostcompIsoOfIso qN).trans (extPrecompIsoOfIso qM))

@[simp]
theorem schemeModuleExtLocalClassLargeAddEquiv_apply
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (M N : X.Modules) (f g : X.presheaf.stalk x)
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor X x).obj N ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (hstalk : Function.Bijective
      (schemeModuleStalkModuleExtMap X x M N 2))
    (z : Ext.{u} M N 2) :
    schemeModuleExtLocalClassLargeAddEquiv x M N f g qM qN hstalk z =
      schemeModuleExtLocalClassLarge x M N f g qM qN z := rfl

/-- A bijective global-to-stalk comparison and regular parameters identify
global degree-two Ext with the residue field at the supported point. -/
noncomputable def schemeModuleExtLocalResidueComponentLargeAddEquiv
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (M N : X.Modules) (f g : X.presheaf.stalk x)
    (hf : f ∈ (X.presheaf.stalk x)⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk x) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor X x).obj N ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (hspan : Ideal.span ({f, g} : Set (X.presheaf.stalk x)) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hstalk : Function.Bijective
      (schemeModuleStalkModuleExtMap X x M N 2)) :
    Ext.{u} M N 2 ≃+
      X.presheaf.stalk x ⧸
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
  (schemeModuleExtLocalClassLargeAddEquiv
      x M N f g qM qN hstalk).trans
    (localExtTwoResidueCoordinateAddEquiv
      f g hf hg hfm hgm hspan)

@[simp]
theorem schemeModuleExtLocalResidueComponentLargeAddEquiv_apply
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (M N : X.Modules) (f g : X.presheaf.stalk x)
    (hf : f ∈ (X.presheaf.stalk x)⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk x) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor X x).obj N ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (hspan : Ideal.span ({f, g} : Set (X.presheaf.stalk x)) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hstalk : Function.Bijective
      (schemeModuleStalkModuleExtMap X x M N 2))
    (z : Ext.{u} M N 2) :
    schemeModuleExtLocalResidueComponentLargeAddEquiv
        x M N f g hf hg hfm hgm qM qN hspan hstalk z =
      schemeModuleExtLocalResidueComponentLarge
        x M N f g hf hg hfm hgm qM qN z := rfl

/-- Endpoint transport does not lose information, so injectivity of the
stalk map on Ext implies injectivity of the transported local class map. -/
theorem schemeModuleExtLocalClassLarge_injective_of_stalkMap_injective
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (M N : X.Modules) (f g : X.presheaf.stalk x)
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸
          Ideal.span ({f, g} : Set (X.presheaf.stalk x))))
    (qN : (schemeModuleStalkModuleFunctor X x).obj N ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (hstalk : Function.Injective
      (schemeModuleStalkModuleExtMap X x M N 2)) :
    Function.Injective
      (schemeModuleExtLocalClassLarge x M N f g qM qN) := by
  intro z z' h
  apply hstalk
  apply ext_postcomp_iso_injective qN 2
  apply ext_precomp_iso_injective qM.symm 2
  exact h

/-- The concrete global residue component is injective when its stalk map on
Ext is injective and the two local equations generate the maximal ideal. -/
theorem schemeModuleExtLocalResidueComponentLarge_injective
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (M N : X.Modules) (f g : X.presheaf.stalk x)
    (hf : f ∈ (X.presheaf.stalk x)⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk x) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸
          Ideal.span ({f, g} : Set (X.presheaf.stalk x))))
    (qN : (schemeModuleStalkModuleFunctor X x).obj N ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (hspan : Ideal.span ({f, g} : Set (X.presheaf.stalk x)) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hstalk : Function.Injective
      (schemeModuleStalkModuleExtMap X x M N 2)) :
    Function.Injective
      (schemeModuleExtLocalResidueComponentLarge x M N f g
        hf hg hfm hgm qM qN) := by
  intro z z' h
  apply schemeModuleExtLocalClassLarge_injective_of_stalkMap_injective
    x M N f g qM qN hstalk
  apply localExtTwoResidueCoordinate_injective_of_span_eq_maximalIdeal
    f g hf hg hfm hgm hspan
  exact h

set_option linter.style.haveILetI false in
/-- Injectivity criterion for the canonical residue component used in
Voisin's Serre-extension calculation. -/
theorem serreYonedaResidueComponent_injective
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {T : X.Modules} [PreservesFiniteLimits (schemeModuleTensorRight T)]
    (eT : T ≅ SheafOfModules.unit X.ringCatSheaf)
    (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))] :
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    letI : Module (X.presheaf.stalk x)
        ((show X.Modules from schemeModuleTensor
          ((Scheme.Modules.pushforward i).obj
            (SheafOfModules.unit Z.ringCatSheaf)) T).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    ∀ (f g : X.presheaf.stalk x)
      (hkernel : LinearMap.ker
        (closedImmersionPushforwardStalkFromRingLinearMap i x) =
          Ideal.span ({f, g} : Set (X.presheaf.stalk x)))
      (hf : f ∈ (X.presheaf.stalk x)⁰)
      (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
        ((X.presheaf.stalk x) ⧸ Ideal.span {f})⁰)
      (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (hspan : Ideal.span ({f, g} : Set (X.presheaf.stalk x)) =
        IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (hstalk : Function.Injective
        (schemeModuleStalkModuleExtMap X x
          (closedImmersionIdealTwistSequence i T).X₃
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2)),
      Function.Injective
        (serreYonedaResidueComponent i eT x f g hkernel
          hf hg hfm hgm) := by
  dsimp
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  letI : Module (X.presheaf.stalk x)
      ((show X.Modules from schemeModuleTensor
        ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)) T).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  intro f g hkernel hf hg hfm hgm hspan hstalk
  exact schemeModuleExtLocalResidueComponentLarge_injective x
    (closedImmersionIdealTwistSequence i T).X₃
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
    f g hf hg hfm hgm
    (LinearEquiv.toModuleIso
      (closedImmersionPushforwardTwistStalkQuotientLinearEquivOfIsoUnit
        i eT x f g hkernel))
    (schemeModuleUnitStalkIso X x) hspan hstalk

end PfaffianDescent
