import PfaffianDescent.ActualSmoothFamilyAmbientStalk169
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! SOURCE ONLY / UNVERIFIED171. Actual open-immersion transport of the
canonical coefficient action and of the entire closed-fiber ideal. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma familyBaseToStalk169_comp171
    {B : Type u} [CommRing B] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (a : Y ⟶ X) (y : Y) :
    familyBaseToStalk169 (a ≫ f) y =
      (a.stalkMap y).hom.comp (familyBaseToStalk169 f (a y)) := by
  rw [familyBaseToStalk169_eq_base_germ_stalkMap,
    familyBaseToStalk169_eq_base_germ_stalkMap, Scheme.Hom.stalkMap_comp]
  apply RingHom.ext
  intro c
  rfl

lemma familyBaseIdeal_map171
    {B : Type u} [CommRing B] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (a : Y ⟶ X) (I : Ideal B) (y : Y) :
    (I.map (familyBaseToStalk169 f (a y))).map (a.stalkMap y).hom =
      I.map (familyBaseToStalk169 (a ≫ f) y) := by
  rw [Ideal.map_map, familyBaseToStalk169_comp171]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma openChart_germ_stalkMap171
    {X Y : Scheme.{u}} (a : Y ⟶ X) [IsOpenImmersion a] (y : Y) :
    (a.appIso ⊤).hom ≫ Y.presheaf.germ ⊤ y (by trivial) =
      X.presheaf.germ (a ''ᵁ ⊤) (a y) ⟨y, trivial, rfl⟩ ≫ a.stalkMap y := by
  rw [a.appIso_hom, Category.assoc, Y.presheaf.germ_res]
  exact (a.germ_stalkMap (a ''ᵁ ⊤) y ⟨y, trivial, rfl⟩).symm

private lemma commRingCatIdeal_comap_inv171
    {R S : CommRingCat.{u}} (e : R ≅ S) (I : Ideal R) :
    I.comap e.inv.hom = I.map e.hom.hom := by
  let eR := e.commRingCatIsoToRingEquiv
  change I.comap eR.symm.toRingHom = I.map eR.toRingHom
  exact Ideal.comap_symm eR

private lemma commRingCatIdeal_transport171
    {R S U V : CommRingCat.{u}} (e : R ≅ S)
    (g : S ⟶ V) (h : R ⟶ U) (l : U ⟶ V)
    (H : e.hom ≫ g = h ≫ l) (I : Ideal R) :
    (I.comap e.inv.hom).map g.hom = (I.map h.hom).map l.hom := by
  have Hhom : g.hom.comp e.hom.hom = l.hom.comp h.hom := by
    have hh := congrArg (fun r : R ⟶ V => r.hom) H
    simpa only [CommRingCat.hom_comp] using hh
  rw [commRingCatIdeal_comap_inv171, Ideal.map_map, Ideal.map_map]
  exact congrArg (fun r : R →+* V => I.map r) Hhom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A genuine Cartesian open chart transports the WHOLE closed-immersion
ideal, by the SAME native stalk map used to transport the coefficient map. -/
lemma openClosedFiberIdeal_map171
    {X Z Y T : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : T ⟶ Y) (b : T ⟶ Z) (a : Y ⟶ X) [IsOpenImmersion a]
    [IsAffine Y] (H : IsPullback j b a i) (y : Y) :
    let W : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
    let V : X.affineOpens := ⟨a ''ᵁ ⊤,
      (isAffineOpen_top Y).image_of_isOpenImmersion a⟩
    (j.ker.ideal W).map (Y.presheaf.germ ⊤ y (by trivial)).hom =
      ((i.ker.ideal V).map
        (X.presheaf.germ V.1 (a y) ⟨y, trivial, rfl⟩).hom).map
          (a.stalkMap y).hom := by
  let W : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  let V : X.affineOpens := ⟨a ''ᵁ ⊤,
    (isAffineOpen_top Y).image_of_isOpenImmersion a⟩
  have hk : j.ker.ideal W = (i.ker.ideal V).comap (a.appIso ⊤).inv.hom :=
    Scheme.ker_ideal_of_isPullback_of_isOpenImmersion i j b a H W
  change (j.ker.ideal W).map (Y.presheaf.germ ⊤ y (by trivial)).hom = _
  rw [hk]
  exact commRingCatIdeal_transport171 (a.appIso ⊤)
    (Y.presheaf.germ ⊤ y (by trivial))
    (X.presheaf.germ V.1 (a y) ⟨y, trivial, rfl⟩)
    (a.stalkMap y) (openChart_germ_stalkMap171 a y) (i.ker.ideal V)

end PfaffianDescent
