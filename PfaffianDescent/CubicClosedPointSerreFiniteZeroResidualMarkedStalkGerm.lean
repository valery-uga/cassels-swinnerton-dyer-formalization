import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualMarkedStalkRetraction

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_markedStalkBaseMap_germ
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (j : Y ⟶ Z)
    (hj : j ≫ g = 𝟙 Y) (y : Y) :
    (cubicClosedPointSerreFiniteZeroResidual_markedStalkBaseMap g j hj y).comp
      (Y.presheaf.germ ⊤ y trivial).hom =
        (Z.presheaf.germ ⊤ (j y) trivial).hom.comp g.appTop.hom := by
  unfold cubicClosedPointSerreFiniteZeroResidual_markedStalkBaseMap
  change (Y.presheaf.germ ⊤ y trivial ≫
      ((Y.presheaf.stalkCongr (.of_eq (show g (j y) = y from
        congrArg (fun f : Y ⟶ Y => f y) hj))).inv ≫ g.stalkMap (j y))).hom =
      (g.appTop ≫ Z.presheaf.germ ⊤ (j y) trivial).hom
  change (Y.presheaf.germ ⊤ y trivial ≫
      (Y.presheaf.stalkSpecializes
        (Inseparable.of_eq (show g (j y) = y from
          congrArg (fun f : Y ⟶ Y => f y) hj)).le ≫ g.stalkMap (j y))).hom = _
  rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes,
    Scheme.Hom.germ_stalkMap]
  rfl

theorem cubicClosedPointSerreFiniteZeroResidual_markedStalk_fibre_ideal
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (j : Y ⟶ Z)
    (hj : j ≫ g = 𝟙 Y) (y : Y) (I : Ideal Γ(Y, ⊤))
    (hI : I.map (Y.presheaf.germ ⊤ y trivial).hom =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) :
    (I.map g.appTop.hom).map (Z.presheaf.germ ⊤ (j y) trivial).hom =
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).map
        (cubicClosedPointSerreFiniteZeroResidual_markedStalkBaseMap g j hj y) := by
  rw [Ideal.map_map, ← cubicClosedPointSerreFiniteZeroResidual_markedStalkBaseMap_germ,
    ← Ideal.map_map, hI]

end PfaffianDescent
