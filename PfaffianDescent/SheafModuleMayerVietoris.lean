import PfaffianDescent.SheafModuleFlasque
import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Topology.Sheaves.MayerVietoris

/-!
# Mayer--Vietoris for section-representing module sheaves

The free module sheaves representing sections on opens carry a Mayer--Vietoris
short exact sequence. Applying contravariant `Ext` gives the two-open
vanishing induction used in the projective-space cohomology calculation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

noncomputable def sectionRepresenterFunctor : C ⥤ SheafOfModules.{u} R :=
  yoneda ⋙ PresheafOfModules.free R.obj ⋙
    PresheafOfModules.sheafification (𝟙 R.obj)

example (X : C) :
    (sectionRepresenterFunctor R).obj X = sectionRepresenter R X := rfl

example (S : J.MayerVietorisSquare) :
    Square (SheafOfModules.{u} R) :=
  S.toSquare.map (sectionRepresenterFunctor R)

end PfaffianDescent

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma freeYonedaEquiv_precomp
    {X Y : C} (f : X ⟶ Y) (P : PresheafOfModules.{u} R.obj)
    (g : (PresheafOfModules.free R.obj).obj (yoneda.obj Y) ⟶ P) :
    PresheafOfModules.freeYonedaEquiv
        ((PresheafOfModules.free R.obj).map (yoneda.map f) ≫ g) =
      P.map f.op (PresheafOfModules.freeYonedaEquiv g) := by
  change yonedaEquiv
      ((PresheafOfModules.freeAdjunction R.obj).homEquiv _ _
        ((PresheafOfModules.free R.obj).map (yoneda.map f) ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_left]
  change yonedaEquiv (yoneda.map f ≫
      ((PresheafOfModules.freeAdjunction R.obj).homEquiv _ P) g) =
    ((P.presheaf ⋙ forget AddCommGrpCat).map f.op)
      (yonedaEquiv (((PresheafOfModules.freeAdjunction R.obj).homEquiv _ P) g))
  exact (yonedaEquiv_naturality _ _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma sectionRepresenterHomEquiv_precomp
    {X Y : C} (f : X ⟶ Y) (M : SheafOfModules.{u} R)
    (g : sectionRepresenter R Y ⟶ M) :
    sectionRepresenterHomEquiv (R := R) X M
        ((sectionRepresenterFunctor R).map f ≫ g) =
      M.val.map f.op (sectionRepresenterHomEquiv (R := R) Y M g) := by
  change PresheafOfModules.freeYonedaEquiv
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _
        ((PresheafOfModules.sheafification (𝟙 R.obj)).map
          ((PresheafOfModules.free R.obj).map (yoneda.map f)) ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_left]
  apply freeYonedaEquiv_precomp

end PfaffianDescent

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The module sheaves freely represented by a Mayer--Vietoris square form a pushout. -/
theorem sectionRepresenter_mayerVietoris_isPushout
    (S : J.MayerVietorisSquare) :
    (S.toSquare.map (sectionRepresenterFunctor R)).IsPushout := by
  rw [Square.isPushout_iff_op_map_yoneda_isPullback]
  intro M
  let sq₁ := (S.toSquare.map (sectionRepresenterFunctor R)).op.map (yoneda.obj M)
  let sq₂ := S.toSquare.op.map (M.val.presheaf ⋙ forget AddCommGrpCat)
  have h₂ : sq₂.IsPullback := by
    have hM := S.sheafCondition_of_sheaf ((SheafOfModules.toSheaf R).obj M)
    exact hM.map (forget AddCommGrpCat)
  let e₁ : sq₁.X₁ ≃ sq₂.X₁ := by
    change (sectionRepresenter R S.X₄ ⟶ M) ≃ M.val.obj (op S.X₄)
    exact sectionRepresenterHomEquiv (R := R) S.X₄ M
  let e₂ : sq₁.X₂ ≃ sq₂.X₂ := by
    change (sectionRepresenter R S.X₂ ⟶ M) ≃ M.val.obj (op S.X₂)
    exact sectionRepresenterHomEquiv (R := R) S.X₂ M
  let e₃ : sq₁.X₃ ≃ sq₂.X₃ := by
    change (sectionRepresenter R S.X₃ ⟶ M) ≃ M.val.obj (op S.X₃)
    exact sectionRepresenterHomEquiv (R := R) S.X₃ M
  let e₄ : sq₁.X₄ ≃ sq₂.X₄ := by
    change (sectionRepresenter R S.X₁ ⟶ M) ≃ M.val.obj (op S.X₁)
    exact sectionRepresenterHomEquiv (R := R) S.X₁ M
  apply (Square.IsPullback.iff_of_equiv sq₁ sq₂ e₁ e₂ e₃ e₄
    (by
      funext x
      change e₂ ((sectionRepresenterFunctor R).map S.f₂₄ ≫ x) =
        M.val.map S.f₂₄.op (e₁ x)
      dsimp [e₁, e₂]
      exact sectionRepresenterHomEquiv_precomp R S.f₂₄ M x)
    (by
      funext x
      change e₃ ((sectionRepresenterFunctor R).map S.f₃₄ ≫ x) =
        M.val.map S.f₃₄.op (e₁ x)
      dsimp [e₁, e₃]
      exact sectionRepresenterHomEquiv_precomp R S.f₃₄ M x)
    (by
      funext x
      change e₄ ((sectionRepresenterFunctor R).map S.f₁₂ ≫ x) =
        M.val.map S.f₁₂.op (e₂ x)
      dsimp [e₂, e₄]
      exact sectionRepresenterHomEquiv_precomp R S.f₁₂ M x)
    (by
      funext x
      change e₄ ((sectionRepresenterFunctor R).map S.f₁₃ ≫ x) =
        M.val.map S.f₁₃.op (e₃ x)
      dsimp [e₃, e₄]
      exact sectionRepresenterHomEquiv_precomp R S.f₁₃ M x)).mpr
  exact h₂

end PfaffianDescent

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits Opposite Abelian

instance moduleCatFree_preservesMonomorphisms (A : Type u) [Ring A] :
    (ModuleCat.free A).PreservesMonomorphisms where
  preserves {X Y} f _ := by
    rw [ModuleCat.mono_iff_injective]
    exact Finsupp.mapDomain_injective ((mono_iff_injective f).mp inferInstance)

variable {C : Type u} [SmallCategory C]

instance presheafModulesFree_preservesMonomorphisms (P : Cᵒᵖ ⥤ RingCat.{u}) :
    (PresheafOfModules.free P).PreservesMonomorphisms where
  preserves {F G} f _ := by
    apply PresheafOfModules.mono_of_injective
      (f := (PresheafOfModules.free P).map f)
    intro X
    change Function.Injective ((ModuleCat.free (P.obj X)).map (f.app X))
    exact (ModuleCat.mono_iff_injective _).mp
      (Functor.map_mono (ModuleCat.free (P.obj X)) (f.app X))

variable {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

noncomputable instance sectionRepresenterFunctor_preservesMonomorphisms :
    (sectionRepresenterFunctor R).PreservesMonomorphisms := by
  change (yoneda ⋙ PresheafOfModules.free R.obj ⋙
    PresheafOfModules.sheafification (𝟙 R.obj)).PreservesMonomorphisms
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The free module sheaves represented by a Mayer--Vietoris square form a short exact
complex. -/
theorem sectionRepresenter_mayerVietoris_shortExact
    (S : J.MayerVietorisSquare) :
    (sectionRepresenter_mayerVietoris_isPushout R S).shortComplex.ShortExact := by
  let h := sectionRepresenter_mayerVietoris_isPushout R S
  haveI : Mono h.shortComplex.f := by
    have : Mono (h.shortComplex.f ≫ biprod.snd) := by
      dsimp [h]
      simp only [biprod.lift_snd]
      infer_instance
    exact mono_of_mono _ biprod.snd
  haveI : Epi h.shortComplex.g := h.epi_shortComplex_g
  exact ⟨h.exact_shortComplex⟩

variable [HasExt.{u} (SheafOfModules.{u} R)]

open ComposableArrows

/-- The contravariant `Ext` Mayer--Vietoris sequence attached to the module
representables. -/
noncomputable abbrev sectionRepresenter_mayerVietoris_extSequence
    (S : J.MayerVietorisSquare) (M : SheafOfModules.{u} R)
    (n₀ n₁ : ℕ) (hn : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  Ext.contravariantSequence
    (sectionRepresenter_mayerVietoris_shortExact R S) M n₀ n₁ (by omega)

/-- Applying `Ext(-, M)` to the module Mayer--Vietoris short exact complex
gives an exact six-term segment. -/
theorem sectionRepresenter_mayerVietoris_extSequence_exact
    (S : J.MayerVietorisSquare) (M : SheafOfModules.{u} R)
    (n₀ n₁ : ℕ) (hn : n₀ + 1 = n₁) :
    (sectionRepresenter_mayerVietoris_extSequence R S M n₀ n₁ hn).Exact := by
  exact Ext.contravariantSequence_exact
    (sectionRepresenter_mayerVietoris_shortExact R S) M n₀ n₁ (by omega)

/-- Two-open vanishing step for module-sheaf cohomology represented by the
free module sheaves on site objects. -/
theorem sectionRepresenter_ext_subsingleton_of_mayerVietoris
    (S : J.MayerVietorisSquare) (M : SheafOfModules.{u} R)
    (n₀ n₁ : ℕ) (hn : n₀ + 1 = n₁)
    [Subsingleton (Ext (sectionRepresenter R S.X₁) M n₀)]
    [Subsingleton (Ext (sectionRepresenter R S.X₂) M n₁)]
    [Subsingleton (Ext (sectionRepresenter R S.X₃) M n₁)] :
    Subsingleton (Ext (sectionRepresenter R S.X₄) M n₁) := by
  let e : Ext (sectionRepresenter R S.X₂ ⊞ sectionRepresenter R S.X₃) M n₁ ≃+
      Ext (sectionRepresenter R S.X₂) M n₁ ×
        Ext (sectionRepresenter R S.X₃) M n₁ :=
    Ext.biprodAddEquiv
  letI : Subsingleton
      (Ext (sectionRepresenter R S.X₂ ⊞ sectionRepresenter R S.X₃) M n₁) :=
    (Equiv.subsingleton_congr e.toEquiv).mpr inferInstance
  let hE := sectionRepresenter_mayerVietoris_extSequence_exact
    R S M n₀ n₁ hn
  have hex := hE.exact 2
  letI : Subsingleton (hE.sc 2).X₁ := by
    change Subsingleton (Ext (sectionRepresenter R S.X₁) M n₀)
    infer_instance
  letI : Subsingleton (hE.sc 2).X₃ := by
    change Subsingleton
      (Ext (sectionRepresenter R S.X₂ ⊞ sectionRepresenter R S.X₃) M n₁)
    infer_instance
  have hfun := (ShortComplex.ab_exact_iff_function_exact _).mp hex
  constructor
  intro x y
  suffices hz : ∀ z : Ext (sectionRepresenter R S.X₄) M n₁, z = 0 by
    exact (hz x).trans (hz y).symm
  intro z
  have hgz : (hE.sc 2).g z = 0 := Subsingleton.elim _ _
  obtain ⟨a, ha⟩ := (hfun z).mp hgz
  rw [show a = 0 by exact Subsingleton.elim _ _, map_zero] at ha
  exact ha.symm

end PfaffianDescent

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian TopologicalSpace

variable {T : Type u} [TopologicalSpace T]
variable (R : Sheaf (Opens.grothendieckTopology T) RingCat.{u})
variable [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasExt.{u} (SheafOfModules.{u} R)]

/-- A checked two-open induction step: vanishing on `U`, `V` in degree `n₁`
and on `U ∩ V` in the previous degree implies vanishing on `U ∪ V`. -/
theorem sectionRepresenter_ext_subsingleton_sup
    (M : SheafOfModules.{u} R) (U V : Opens T)
    (n₀ n₁ : ℕ) (hn : n₀ + 1 = n₁)
    [Subsingleton (Ext (sectionRepresenter R (U ⊓ V)) M n₀)]
    [Subsingleton (Ext (sectionRepresenter R U) M n₁)]
    [Subsingleton (Ext (sectionRepresenter R V) M n₁)] :
    Subsingleton (Ext (sectionRepresenter R (U ⊔ V)) M n₁) := by
  let S := Opens.mayerVietorisSquare U V
  letI : Subsingleton (Ext (sectionRepresenter R S.X₁) M n₀) := by
    change Subsingleton (Ext (sectionRepresenter R (U ⊓ V)) M n₀)
    infer_instance
  letI : Subsingleton (Ext (sectionRepresenter R S.X₂) M n₁) := by
    change Subsingleton (Ext (sectionRepresenter R U) M n₁)
    infer_instance
  letI : Subsingleton (Ext (sectionRepresenter R S.X₃) M n₁) := by
    change Subsingleton (Ext (sectionRepresenter R V) M n₁)
    infer_instance
  have h := sectionRepresenter_ext_subsingleton_of_mayerVietoris
    R S M n₀ n₁ hn
  change Subsingleton (Ext (sectionRepresenter R (U ⊔ V)) M n₁) at h
  exact h

end PfaffianDescent
