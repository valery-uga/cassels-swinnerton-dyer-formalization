import PfaffianDescent.VoisinFieldBaseChangeOpen
import PfaffianDescent.BundleSectionZeroLocusNaturality

/-!
# Naturality of field base change on nested open subschemes

This module proves the categorical coherence needed to compare field base
change before and after restriction to a smaller open subscheme.
-/

open CategoryTheory
open AlgebraicGeometry

universe u

namespace PfaffianDescent

theorem conjugate_restrictFunctorIsoPullback_hom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.restrictAdjunction f)
      (Scheme.Modules.restrictFunctorIsoPullback f).hom =
        𝟙 (Scheme.Modules.pushforward f) := by
  let P := Scheme.Modules.pullbackPushforwardAdjunction f
  let R := Scheme.Modules.restrictAdjunction f
  let e := (conjugateIsoEquiv R P).symm
    (Iso.refl (Scheme.Modules.pushforward f))
  change (conjugateIsoEquiv P R e.symm).hom =
    (Iso.refl (Scheme.Modules.pushforward f)).hom
  have he : conjugateIsoEquiv P R e.symm =
      (conjugateIsoEquiv R P e).symm := by
    rfl
  rw [he, (conjugateIsoEquiv R P).apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem conjugate_restrictFunctorComp_hom
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    conjugateEquiv
      ((Scheme.Modules.restrictAdjunction g).comp
        (Scheme.Modules.restrictAdjunction f))
      (Scheme.Modules.restrictAdjunction (f ≫ g))
      (Scheme.Modules.restrictFunctorComp f g).hom =
        (Scheme.Modules.pushforwardComp f g).hom := by
  ext M U x
  simp only [conjugateEquiv_apply_app]
  change ((M.presheaf.map _ ≫ M.presheaf.map _ ≫
    M.presheaf.map _ ≫ M.presheaf.map _).hom x) = x
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  change (M.presheaf.map _).hom x =
    AddCommGrpCat.Hom.hom
      (𝟙 (((Scheme.Modules.pushforward f ⋙
        Scheme.Modules.pushforward g).obj M).presheaf.obj
          (Opposite.op U))) x
  congr 1
  ext y
  apply ConcreteCategory.congr_hom
  change M.presheaf.map _ =
    𝟙 (M.presheaf.obj
      ((TopologicalSpace.Opens.map f.base).op.obj
        ((TopologicalSpace.Opens.map g.base).op.obj (Opposite.op U))))
  rw [← M.presheaf.map_id]
  exact congrArg (fun k => M.presheaf.map k) (Subsingleton.elim _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem restrictFunctorIsoPullback_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    (Scheme.Modules.restrictFunctorComp f g).hom ≫
        Functor.whiskerRight
          (Scheme.Modules.restrictFunctorIsoPullback g).hom
          (Scheme.Modules.restrictFunctor f) ≫
        Functor.whiskerLeft (Scheme.Modules.pullback g)
          (Scheme.Modules.restrictFunctorIsoPullback f).hom =
      (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).hom ≫
        (Scheme.Modules.pullbackComp f g).inv := by
  let AP := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  let AR := (Scheme.Modules.restrictAdjunction g).comp
    (Scheme.Modules.restrictAdjunction f)
  let AM := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.restrictAdjunction f)
  let AT := Scheme.Modules.restrictAdjunction (f ≫ g)
  let AQ := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  let wf := Functor.whiskerLeft (Scheme.Modules.pullback g)
    (Scheme.Modules.restrictFunctorIsoPullback f).hom
  let wg := Functor.whiskerRight
    (Scheme.Modules.restrictFunctorIsoPullback g).hom
    (Scheme.Modules.restrictFunctor f)
  have hwf : conjugateEquiv AP AM wf = 𝟙 _ := by
    dsimp only [AP, AM, wf]
    rw [conjugateEquiv_whiskerLeft,
      conjugate_restrictFunctorIsoPullback_hom]
    simp
  have hwg : conjugateEquiv AM AR wg = 𝟙 _ := by
    dsimp only [AM, AR, wg]
    rw [conjugateEquiv_whiskerRight,
      conjugate_restrictFunctorIsoPullback_hom]
    simp
  have hw : conjugateEquiv AP AR (wg ≫ wf) = 𝟙 _ := by
    rw [← conjugateEquiv_comp AP AM]
    rw [hwf, hwg, Category.comp_id]
  apply (conjugateEquiv AP AT).injective
  change conjugateEquiv AP AT
      ((Scheme.Modules.restrictFunctorComp f g).hom ≫ wg ≫ wf) =
    conjugateEquiv AP AT
      ((Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).hom ≫
        (Scheme.Modules.pullbackComp f g).inv)
  rw [← conjugateEquiv_comp AP AR, hw,
    conjugate_restrictFunctorComp_hom, Category.id_comp]
  rw [← conjugateEquiv_comp AP AQ,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    conjugate_restrictFunctorIsoPullback_hom,
    Category.comp_id]

noncomputable def restrictFunctorPullbackCompIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    Scheme.Modules.restrictFunctor (f ≫ g) ≅
      Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f :=
  Scheme.Modules.restrictFunctorComp f g ≪≫
    Functor.isoWhiskerRight
      (Scheme.Modules.restrictFunctorIsoPullback g)
      (Scheme.Modules.restrictFunctor f) ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pullback g)
      (Scheme.Modules.restrictFunctorIsoPullback f)

theorem restrictFunctorPullbackCompIso_eq
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    restrictFunctorPullbackCompIso f g =
      Scheme.Modules.restrictFunctorIsoPullback (f ≫ g) ≪≫
        (Scheme.Modules.pullbackComp f g).symm := by
  apply Iso.ext
  exact restrictFunctorIsoPullback_comp f g

theorem restrictFunctorPullbackCompIso_inv_app
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    (Functor.whiskerLeft (Scheme.Modules.pullback g)
          (Scheme.Modules.restrictFunctorIsoPullback f).inv).app M ≫
        (Functor.whiskerRight
          (Scheme.Modules.restrictFunctorIsoPullback g).inv
          (Scheme.Modules.restrictFunctor f)).app M ≫
        (Scheme.Modules.restrictFunctorComp f g).inv.app M =
      (Scheme.Modules.pullbackComp f g).hom.app M ≫
        (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).inv.app M := by
  have h := congrArg Iso.inv (restrictFunctorPullbackCompIso_eq f g)
  exact congr_app h M

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem restrictFunctorIsoPullback_congr
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    (Scheme.Modules.restrictFunctorCongr h).hom ≫
        (Scheme.Modules.restrictFunctorIsoPullback g).hom =
      (Scheme.Modules.restrictFunctorIsoPullback f).hom ≫
        (Scheme.Modules.pullbackCongr h).hom := by
  subst g
  cat_disch

noncomputable def nestedOpenRestrictionPullbackIso
    {X : Scheme.{u}} (M : X.Modules) {U W : X.Opens} (hWU : W ≤ U) :
    (Scheme.Modules.pullback (X.homOfLE hWU)).obj (M.restrict U.ι) ≅
      M.restrict W.ι :=
  ((Scheme.Modules.restrictFunctorIsoPullback
      (X.homOfLE hWU)).app (M.restrict U.ι)).symm ≪≫
    ((Scheme.Modules.restrictFunctorComp (X.homOfLE hWU) U.ι).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr
      (Scheme.homOfLE_ι X hWU)).app M

theorem nestedOpenRestrictionPullbackIso_hom_comp
    {X : Scheme.{u}} (M : X.Modules) {U W : X.Opens} (hWU : W ≤ U) :
    (nestedOpenRestrictionPullbackIso M hWU).hom ≫
        (Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.app M =
      (Scheme.Modules.pullback (X.homOfLE hWU)).map
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app M) ≫
        (Scheme.Modules.pullbackComp (X.homOfLE hWU) U.ι).hom.app M ≫
        (Scheme.Modules.pullbackCongr
          (Scheme.homOfLE_ι X hWU)).hom.app M := by
  let hK := X.homOfLE hWU
  let e := Scheme.homOfLE_ι X hWU
  have hcongr := congr_app
    (restrictFunctorIsoPullback_congr e) M
  have hcomp := congr_app
    (restrictFunctorIsoPullback_comp hK U.ι) M
  simp only [NatTrans.comp_app] at hcongr hcomp
  simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app] at hcomp
  have hrearr :
      (Scheme.Modules.restrictFunctorComp hK U.ι).inv.app M ≫
          (Scheme.Modules.restrictFunctorIsoPullback (hK ≫ U.ι)).hom.app M =
        (Scheme.Modules.restrictFunctor hK).map
            ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app M) ≫
          (Scheme.Modules.restrictFunctorIsoPullback hK).hom.app
              ((Scheme.Modules.pullback U.ι).obj M) ≫
          (Scheme.Modules.pullbackComp hK U.ι).hom.app M := by
    have hh := congrArg (fun k =>
      (Scheme.Modules.restrictFunctorComp hK U.ι).inv.app M ≫ k ≫
        (Scheme.Modules.pullbackComp hK U.ι).hom.app M) hcomp
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc,
      Iso.inv_hom_id_app, Category.comp_id] using hh.symm
  dsimp only [nestedOpenRestrictionPullbackIso, hK, e] at hcongr hcomp hrearr ⊢
  simp only [Iso.trans_hom, Category.assoc]
  change
    (Scheme.Modules.restrictFunctorIsoPullback
          (X.homOfLE hWU)).inv.app (M.restrict U.ι) ≫
        (Scheme.Modules.restrictFunctorComp
          (X.homOfLE hWU) U.ι).inv.app M ≫
        (Scheme.Modules.restrictFunctorCongr
          (Scheme.homOfLE_ι X hWU)).hom.app M ≫
        (Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.app M =
      (Scheme.Modules.pullback (X.homOfLE hWU)).map
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app M) ≫
        (Scheme.Modules.pullbackComp
          (X.homOfLE hWU) U.ι).hom.app M ≫
        (Scheme.Modules.pullbackCongr
          (Scheme.homOfLE_ι X hWU)).hom.app M
  rw [hcongr]
  slice_lhs 2 3 => rw [hrearr]
  slice_lhs 2 3 =>
    rw [(Scheme.Modules.restrictFunctorIsoPullback
      (X.homOfLE hWU)).hom.naturality]
  slice_lhs 1 2 => simp
  simp only [Category.id_comp, Category.assoc]

theorem pullback_isoPullback_inv_comp_nestedOpenRestrictionPullbackIso_hom
    {X : Scheme.{u}} (M : X.Modules) {U W : X.Opens} (hWU : W ≤ U) :
    (Scheme.Modules.pullback (X.homOfLE hWU)).map
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app M) ≫
        (nestedOpenRestrictionPullbackIso M hWU).hom =
      (Scheme.Modules.pullbackComp (X.homOfLE hWU) U.ι).hom.app M ≫
        (Scheme.Modules.pullbackCongr
          (Scheme.homOfLE_ι X hWU)).hom.app M ≫
        (Scheme.Modules.restrictFunctorIsoPullback W.ι).inv.app M := by
  let hK := X.homOfLE hWU
  let e := Scheme.homOfLE_ι X hWU
  have hinv := restrictFunctorPullbackCompIso_inv_app hK U.ι M
  simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app] at hinv
  have hcongr := congr_app
    (restrictFunctorIsoPullback_congr e) M
  simp only [NatTrans.comp_app] at hcongr
  have hcongr_rearr :
      (Scheme.Modules.restrictFunctorIsoPullback (hK ≫ U.ι)).inv.app M ≫
          (Scheme.Modules.restrictFunctorCongr e).hom.app M =
        (Scheme.Modules.pullbackCongr e).hom.app M ≫
          (Scheme.Modules.restrictFunctorIsoPullback W.ι).inv.app M := by
    rw [← cancel_epi
      ((Scheme.Modules.restrictFunctorIsoPullback
        (hK ≫ U.ι)).hom.app M)]
    rw [← cancel_mono
      ((Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.app M)]
    slice_lhs 1 2 => simp
    slice_rhs 3 4 => simp
    exact hcongr
  dsimp only [nestedOpenRestrictionPullbackIso, hK, e] at hinv hcongr ⊢
  dsimp only [hK, e] at hcongr_rearr ⊢
  simp only [Iso.trans_hom]
  change
    (Scheme.Modules.pullback (X.homOfLE hWU)).map
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app M) ≫
        (Scheme.Modules.restrictFunctorIsoPullback
          (X.homOfLE hWU)).inv.app (M.restrict U.ι) ≫
        (Scheme.Modules.restrictFunctorComp
          (X.homOfLE hWU) U.ι).inv.app M ≫
        (Scheme.Modules.restrictFunctorCongr
          (Scheme.homOfLE_ι X hWU)).hom.app M =
      (Scheme.Modules.pullbackComp
          (X.homOfLE hWU) U.ι).hom.app M ≫
        (Scheme.Modules.pullbackCongr
          (Scheme.homOfLE_ι X hWU)).hom.app M ≫
        (Scheme.Modules.restrictFunctorIsoPullback W.ι).inv.app M
  slice_lhs 1 2 =>
    rw [(Scheme.Modules.restrictFunctorIsoPullback
      (X.homOfLE hWU)).inv.naturality]
  slice_lhs 1 3 => rw [hinv]
  slice_lhs 2 3 => rw [hcongr_rearr]

@[reassoc]
theorem pullbackComp_assoc_hom
    {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (M : D.Modules) :
    (Scheme.Modules.pullback f).map
          ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M =
      (Scheme.Modules.pullbackComp f g).hom.app
          ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M ≫
        (Scheme.Modules.pullbackCongr (Category.assoc f g h)).hom.app M := by
  have ha := congr_app
    (Scheme.Modules.pseudofunctor_associativity f g h) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app] at ha
  change _ = (Scheme.Modules.pullbackCongr
    (Category.assoc f g h)).inv.app M at ha
  have hh := congrArg (fun k =>
    (Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫ k ≫
      (Scheme.Modules.pullbackCongr
        (Category.assoc f g h)).hom.app M) ha
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    Category.id_comp] at hh
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app] at hh
  rw [(Scheme.Modules.pullback f).map_id] at hh
  simp only [Category.id_comp] at hh
  simpa only [Category.assoc, Category.id_comp, Category.comp_id,
    Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app] using hh.symm

@[reassoc]
theorem pullbackComp_inv_comp_map_hom
    {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (M : D.Modules) :
    (Scheme.Modules.pullbackComp f g).inv.app
          ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullback f).map
          ((Scheme.Modules.pullbackComp g h).hom.app M) =
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M ≫
        (Scheme.Modules.pullbackCongr (Category.assoc f g h)).hom.app M ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M := by
  have ha := pullbackComp_assoc_hom f g h M
  rw [← cancel_mono
    ((Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M)]
  slice_lhs 2 3 => rw [ha]
  slice_lhs 1 2 => simp
  simp

@[reassoc]
theorem pullbackComp_congr_left
    {A B C : Scheme.{u}} {f f' : A ⟶ B} (e : f = f')
    (h : B ⟶ C) (M : C.Modules) :
    (Scheme.Modules.pullbackCongr e).hom.app
          ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullbackComp f' h).hom.app M =
      (Scheme.Modules.pullbackComp f h).hom.app M ≫
        (Scheme.Modules.pullbackCongr
          (congrArg (fun k => k ≫ h) e)).hom.app M := by
  subst f'
  cat_disch

@[reassoc]
theorem pullbackComp_congr_right
    {A B C : Scheme.{u}} (f : A ⟶ B) {g g' : B ⟶ C}
    (e : g = g') (M : C.Modules) :
    (Scheme.Modules.pullback f).map
          ((Scheme.Modules.pullbackCongr e).hom.app M) ≫
        (Scheme.Modules.pullbackComp f g').hom.app M =
      (Scheme.Modules.pullbackComp f g).hom.app M ≫
        (Scheme.Modules.pullbackCongr
          (congrArg (fun k => f ≫ k) e)).hom.app M := by
  subst g'
  simp [Scheme.Modules.pullbackCongr]

@[reassoc]
theorem map_pullbackComp_inv_comp_pullbackComp_hom
    {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (M : D.Modules) :
    (Scheme.Modules.pullback f).map
          ((Scheme.Modules.pullbackComp g h).inv.app M) ≫
        (Scheme.Modules.pullbackComp f g).hom.app
          ((Scheme.Modules.pullback h).obj M) =
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫
        (Scheme.Modules.pullbackCongr (Category.assoc f g h)).inv.app M ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).inv.app M := by
  have ha := pullbackComp_assoc_hom f g h M
  rw [← cancel_epi
    ((Scheme.Modules.pullback f).map
      ((Scheme.Modules.pullbackComp g h).hom.app M))]
  slice_lhs 1 2 => simp
  slice_rhs 1 2 => rw [ha]
  simp

@[reassoc]
theorem pullback_baseChange_rectangle
    {X U W XL VU VW : Scheme.{u}}
    (g : XL ⟶ X) (u : U ⟶ X) (w : W ⟶ X)
    (vu : VU ⟶ XL) (vw : VW ⟶ XL)
    (pU : VU ⟶ U) (pW : VW ⟶ W)
    (hK : W ⟶ U) (hL : VW ⟶ VU)
    (eK : hK ≫ u = w) (eU : pU ≫ u = vu ≫ g)
    (eW : pW ≫ w = vw ≫ g) (esq : pW ≫ hK = hL ≫ pU)
    (eL : hL ≫ vu = vw)
    (M : X.Modules) (E : U.Modules)
    (m : E ⟶ (Scheme.Modules.pullback u).obj M) :
    (Scheme.Modules.pullback pW).map
          ((Scheme.Modules.pullback hK).map m) ≫
        (Scheme.Modules.pullback pW).map
          ((Scheme.Modules.pullbackComp hK u).hom.app M) ≫
        (Scheme.Modules.pullback pW).map
          ((Scheme.Modules.pullbackCongr eK).hom.app M) ≫
        (Scheme.Modules.pullbackComp pW w).hom.app M ≫
        (Scheme.Modules.pullbackCongr eW).hom.app M ≫
        (Scheme.Modules.pullbackComp vw g).inv.app M =
      (Scheme.Modules.pullbackComp pW hK).hom.app E ≫
        (Scheme.Modules.pullbackCongr esq).hom.app E ≫
        (Scheme.Modules.pullbackComp hL pU).inv.app E ≫
        (Scheme.Modules.pullback hL).map
          ((Scheme.Modules.pullback pU).map m) ≫
        (Scheme.Modules.pullback hL).map
          ((Scheme.Modules.pullbackComp pU u).hom.app M) ≫
        (Scheme.Modules.pullback hL).map
          ((Scheme.Modules.pullbackCongr eU).hom.app M) ≫
        (Scheme.Modules.pullback hL).map
          ((Scheme.Modules.pullbackComp vu g).inv.app M) ≫
        (Scheme.Modules.pullbackComp hL vu).hom.app
          ((Scheme.Modules.pullback g).obj M) ≫
    (Scheme.Modules.pullbackCongr eL).hom.app
          ((Scheme.Modules.pullback g).obj M) := by
  subst w
  subst vw
  let squareIso :=
    (Scheme.Modules.pullbackComp pW hK) ≪≫
      Scheme.Modules.pullbackCongr esq ≪≫
      (Scheme.Modules.pullbackComp hL pU).symm
  have hnat := squareIso.hom.naturality m
  dsimp only [squareIso] at hnat
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.comp_map] at hnat
  simp at hnat ⊢
  slice_rhs 1 4 => rw [← hnat]
  slice_lhs 3 3 => simp [Scheme.Modules.pullbackCongr]
  slice_rhs 9 9 => simp [Scheme.Modules.pullbackCongr]
  simp only [Category.id_comp, Category.comp_id, NatTrans.id_app]
  slice_lhs 2 3 => rw [pullbackComp_assoc_hom pW hK u M]
  slice_rhs 4 5 =>
    rw [pullbackComp_inv_comp_map_hom hL pU u M]
  slice_rhs 3 4 => rw [pullbackComp_congr_left esq u M]
  slice_rhs 8 9 =>
    rw [map_pullbackComp_inv_comp_pullbackComp_hom hL vu g M]
  slice_rhs 7 8 => rw [pullbackComp_congr_right hL eU M]
  slice_rhs 6 7 => simp
  simp [Scheme.Modules.pullbackCongr]

theorem schemeFieldBaseChangeOpenModuleIso_naturality_restrict
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {U W : X.Opens} (hWU : W ≤ U) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let ML := (Scheme.Modules.pullback g).obj M
    let hK := X.homOfLE hWU
    let hL := (schemeFieldBaseChange base).homOfLE (g.preimage_mono hWU)
    let pW := g ∣_ W
    let pU := g ∣_ U
    let E := M.restrict U.ι
    let rK := nestedOpenRestrictionPullbackIso M hWU
    let rL := nestedOpenRestrictionPullbackIso ML (g.preimage_mono hWU)
    let AU := schemeFieldBaseChangeOpenModuleIso (K := K) (L := L) base M U
    let AW := schemeFieldBaseChangeOpenModuleIso (K := K) (L := L) base M W
    let square := ((Scheme.Modules.pullbackComp pW hK).app E ≪≫
        (Scheme.Modules.pullbackCongr
          (morphismRestrict_homOfLE g W U hWU)).app E) ≪≫
      ((Scheme.Modules.pullbackComp hL pU).app E).symm
    ((Scheme.Modules.pullback pW).mapIso rK ≪≫ AW) =
      square ≪≫ ((Scheme.Modules.pullback hL).mapIso AU ≪≫ rL) := by
  dsimp only
  have hKmap := congrArg (fun k =>
      (Scheme.Modules.pullback
        (schemeFieldBaseChangeToOriginal (L := L) base ∣_ W)).map k)
    (nestedOpenRestrictionPullbackIso_hom_comp M hWU)
  simp only [Functor.map_comp] at hKmap
  have hLtail :=
    pullback_isoPullback_inv_comp_nestedOpenRestrictionPullbackIso_hom
      ((Scheme.Modules.pullback
        (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)
      ((schemeFieldBaseChangeToOriginal (L := L) base).preimage_mono hWU)
  change
    (Scheme.Modules.pullback
        (schemeFieldBaseChangeToOriginal (L := L) base ∣_ W)).map
          (nestedOpenRestrictionPullbackIso M hWU).hom ≫
      (Scheme.Modules.pullback
        (schemeFieldBaseChangeToOriginal (L := L) base ∣_ W)).map
          ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app M).hom = _
    at hKmap
  change
    (Scheme.Modules.pullback
        ((schemeFieldBaseChange (L := L) base).homOfLE
          ((schemeFieldBaseChangeToOriginal (L := L) base).preimage_mono hWU))).map
          (((Scheme.Modules.restrictFunctorIsoPullback
            (schemeFieldBaseChangeToOriginal (L := L) base ⁻¹ᵁ U).ι).app
              ((Scheme.Modules.pullback
                (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)).symm.hom) ≫
      (nestedOpenRestrictionPullbackIso
        ((Scheme.Modules.pullback
          (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)
        ((schemeFieldBaseChangeToOriginal (L := L) base).preimage_mono hWU)).hom = _
    at hLtail
  have hrect := pullback_baseChange_rectangle_assoc
    (schemeFieldBaseChangeToOriginal (L := L) base)
    U.ι W.ι
    (schemeFieldBaseChangeToOriginal (L := L) base ⁻¹ᵁ U).ι
    (schemeFieldBaseChangeToOriginal (L := L) base ⁻¹ᵁ W).ι
    (schemeFieldBaseChangeToOriginal (L := L) base ∣_ U)
    (schemeFieldBaseChangeToOriginal (L := L) base ∣_ W)
    (X.homOfLE hWU)
    ((schemeFieldBaseChange (L := L) base).homOfLE
      ((schemeFieldBaseChangeToOriginal (L := L) base).preimage_mono hWU))
    (Scheme.homOfLE_ι X hWU)
    (morphismRestrict_ι
      (schemeFieldBaseChangeToOriginal (L := L) base) U)
    (morphismRestrict_ι
      (schemeFieldBaseChangeToOriginal (L := L) base) W)
    (morphismRestrict_homOfLE
      (schemeFieldBaseChangeToOriginal (L := L) base) W U hWU)
    (Scheme.homOfLE_ι (schemeFieldBaseChange (L := L) base)
      ((schemeFieldBaseChangeToOriginal (L := L) base).preimage_mono hWU))
    M (M.restrict U.ι)
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app M)
    ((Scheme.Modules.restrictFunctorIsoPullback
      (schemeFieldBaseChangeToOriginal (L := L) base ⁻¹ᵁ W).ι).inv.app
      ((Scheme.Modules.pullback
        (schemeFieldBaseChangeToOriginal (L := L) base)).obj M))
  apply Iso.ext
  unfold schemeFieldBaseChangeOpenModuleIso
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  slice_lhs 1 2 => rw [hKmap]
  simp only [Functor.map_comp]
  slice_rhs 8 9 => rw [hLtail]
  simpa only [Category.assoc, Iso.app_hom, Iso.app_inv, Iso.symm_hom] using hrect


namespace BundleSectionZeroLocus

theorem pullbackFreeIso_trans_restrictFunctorIsoPullback_symm
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {E : Y.Modules} (I : Type u)
    (e : SheafOfModules.free (R := Y.ringCatSheaf) I ≅ E) :
    pullbackFreeIso f I e ≪≫
        ((Scheme.Modules.restrictFunctorIsoPullback f).app E).symm =
      restrictionFreeIsoOf f I e := by
  letI := isIso_pullbackUnitComparison f
  apply Iso.ext
  apply ((Scheme.Modules.restrictFunctor f).obj E).freeHomEquiv.injective
  funext i
  apply ((Scheme.Modules.restrictFunctor f).obj E).unitHomEquiv.symm.injective
  erw [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply,
    SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  erw [Iso.trans_hom]
  let α := Scheme.Modules.restrictFunctorIsoPullback f
  let ρ := Scheme.Modules.restrictUnitIso f
  let z := SheafOfModules.ιFree i ≫ e.hom
  have hpb : SheafOfModules.ιFree i ≫ (pullbackFreeIso f I e).hom =
      inv (pullbackUnitComparison f) ≫
        (Scheme.Modules.pullback f).map z :=
    pullbackFreeIso_ιFree_hom f I e i
  have hres : SheafOfModules.ιFree i ≫
      (restrictionFreeIsoOf f I e).hom =
      ρ.inv ≫ (Scheme.Modules.restrictFunctor f).map z :=
    restrictionFreeIsoOf_ιFree_hom f I e i
  have hpc : pullbackUnitComparison f = α.inv.app _ ≫ ρ.hom :=
    pullbackUnitComparison_eq_restrict f
  have hinv : inv (pullbackUnitComparison f) =
      ρ.inv ≫ α.hom.app (SheafOfModules.unit Y.ringCatSheaf) := by
    apply (IsIso.eq_inv_of_hom_inv_id (by
      rw [hpc]
      calc
        (α.inv.app _ ≫ ρ.hom) ≫
            (ρ.inv ≫ α.hom.app _) =
          α.inv.app _ ≫ (ρ.hom ≫ ρ.inv) ≫
            α.hom.app _ := by rfl
        _ = α.inv.app _ ≫ (𝟙 _ ≫ α.hom.app _) := by
          exact congrArg (fun q =>
            α.inv.app _ ≫ (q ≫ α.hom.app _)) ρ.hom_inv_id
        _ = α.inv.app _ ≫ α.hom.app _ := by
          rw [Category.id_comp]
        _ = 𝟙 _ := α.inv_hom_id_app _)).symm
  erw [← Category.assoc, hpb, hinv]
  erw [Category.assoc, Category.assoc]
  erw [α.inv.naturality]
  have hcancel :
      α.hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
          (α.inv.app (SheafOfModules.unit Y.ringCatSheaf) ≫
            (Scheme.Modules.restrictFunctor f).map z) =
        (Scheme.Modules.restrictFunctor f).map z := by
    rw [← Category.assoc]
    exact (congrArg (fun q => q ≫
      (Scheme.Modules.restrictFunctor f).map z)
      (α.hom_inv_id_app _)).trans (Category.id_comp _)
  exact (congrArg (fun q => ρ.inv ≫ q) hcancel).trans hres.symm

end BundleSectionZeroLocus

end PfaffianDescent
