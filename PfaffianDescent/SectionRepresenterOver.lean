import PfaffianDescent.SheafModuleMayerVietoris
import PfaffianDescent.SheafModulePushforwardExact
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Section representers on an over-site

Restriction to the site over `X` carries the free module sheaf represented by
`Y` to the free module sheaf represented by `X × Y → X`.  This file packages
that comparison, including its naturality in `Y`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace PfaffianDescent

universe u

variable {C : Type u} [SmallCategory C] [HasBinaryProducts C]
variable {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Yoneda base change along `Over.forget X`, whose right adjoint sends `Y`
to `X × Y → X`. -/
noncomputable def overYonedaIso (X Y : C) :
    yoneda.obj ((Over.star X).obj Y) ≅
      (Over.forget X).op ⋙ yoneda.obj Y :=
  (Adjunction.compYonedaIso (Over.forgetAdjStar X)).app Y

/-- Objectwise-free module presheaves commute with passage to an over-site. -/
noncomputable def overFreeYonedaIso (X Y : C) :
    (PresheafOfModules.pushforward (𝟙 (R.over X).obj)).obj
        ((PresheafOfModules.free R.obj).obj (yoneda.obj Y)) ≅
      (PresheafOfModules.free (R.over X).obj).obj
        (yoneda.obj ((Over.star X).obj Y)) := by
  change (PresheafOfModules.free (R.over X).obj).obj
      ((Over.forget X).op ⋙ yoneda.obj Y) ≅ _
  exact (PresheafOfModules.free (R.over X).obj).mapIso
    (overYonedaIso X Y).symm

/-- Restriction of a section-representing module sheaf to the over-site of
`X` is represented there by `X × Y → X`. -/
noncomputable def overSectionRepresenterIso (X Y : C) :
    sectionRepresenter (R.over X) ((Over.star X).obj Y) ≅
      (SheafOfModules.overFunctor R X).obj (sectionRepresenter R Y) :=
  (PresheafOfModules.sheafification (𝟙 (R.over X).obj)).mapIso
      (overFreeYonedaIso R X Y).symm ≪≫
    SheafOfModules.overFunctor_sheafificationComparisonIso X
      ((PresheafOfModules.free R.obj).obj (yoneda.obj Y))

omit [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
set_option backward.isDefEq.respectTransparency false in
lemma overFreeYonedaIso_inv_naturality {X Y Z : C} (f : Y ⟶ Z) :
    (PresheafOfModules.free (R.over X).obj).map
        (yoneda.map ((Over.star X).map f)) ≫
      (overFreeYonedaIso R X Z).inv =
    (overFreeYonedaIso R X Y).inv ≫
      (PresheafOfModules.pushforward (𝟙 (R.over X).obj)).map
        ((PresheafOfModules.free R.obj).map (yoneda.map f)) := by
  change (PresheafOfModules.free (R.over X).obj).map
      (yoneda.map ((Over.star X).map f)) ≫
      (PresheafOfModules.free (R.over X).obj).map
        ((Adjunction.compYonedaIso (Over.forgetAdjStar X)).hom.app Z) =
    (PresheafOfModules.free (R.over X).obj).map
        ((Adjunction.compYonedaIso (Over.forgetAdjStar X)).hom.app Y) ≫
      (PresheafOfModules.free (R.over X).obj).map
        ((Functor.whiskeringLeft _ _ _).obj (Over.forget X).op |>.map (yoneda.map f))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact (Adjunction.compYonedaIso (Over.forgetAdjStar X)).hom.naturality f

set_option backward.isDefEq.respectTransparency false in
lemma overSectionRepresenterIso_hom_naturality {X Y Z : C} (f : Y ⟶ Z) :
    (sectionRepresenterFunctor (R.over X)).map ((Over.star X).map f) ≫
        (overSectionRepresenterIso R X Z).hom =
      (overSectionRepresenterIso R X Y).hom ≫
        (SheafOfModules.overFunctor R X).map
          ((sectionRepresenterFunctor R).map f) := by
  let PY := (PresheafOfModules.free R.obj).obj (yoneda.obj Y)
  let PZ := (PresheafOfModules.free R.obj).obj (yoneda.obj Z)
  let fp : PY ⟶ PZ := (PresheafOfModules.free R.obj).map (yoneda.map f)
  let cY := SheafOfModules.overFunctor_sheafificationComparisonIso X PY
  let cZ := SheafOfModules.overFunctor_sheafificationComparisonIso X PZ
  have hc : cY.hom ≫ (SheafOfModules.overFunctor R X).map
        ((PresheafOfModules.sheafification (𝟙 R.obj)).map fp) =
      (PresheafOfModules.sheafification (𝟙 (R.over X).obj)).map
        ((PresheafOfModules.pushforward (𝟙 (R.over X).obj)).map fp) ≫ cZ.hom := by
    exact (SheafOfModules.overFunctor_sheafificationComparison_naturality
      (R := R) X fp).symm
  dsimp only [overSectionRepresenterIso, Iso.trans_hom]
  change
    (PresheafOfModules.sheafification (𝟙 (R.over X).obj)).map
        ((PresheafOfModules.free (R.over X).obj).map
          (yoneda.map ((Over.star X).map f))) ≫
      (PresheafOfModules.sheafification (𝟙 (R.over X).obj)).map
        (overFreeYonedaIso R X Z).inv ≫ cZ.hom =
    (PresheafOfModules.sheafification (𝟙 (R.over X).obj)).map
        (overFreeYonedaIso R X Y).inv ≫ cY.hom ≫
      (SheafOfModules.overFunctor R X).map
        ((PresheafOfModules.sheafification (𝟙 R.obj)).map fp)
  rw [hc]
  rw [← Category.assoc, ← Category.assoc]
  apply (cancel_mono cZ.hom).2
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact overFreeYonedaIso_inv_naturality R f

/-- The over-site comparison for section representers, natural in the
represented object. -/
noncomputable def overSectionRepresenterNatIso (X : C) :
    Over.star X ⋙ sectionRepresenterFunctor (R.over X) ≅
      sectionRepresenterFunctor R ⋙ SheafOfModules.overFunctor R X :=
  NatIso.ofComponents (fun Y ↦ overSectionRepresenterIso R X Y)
    (fun f ↦ overSectionRepresenterIso_hom_naturality R f)

end PfaffianDescent
