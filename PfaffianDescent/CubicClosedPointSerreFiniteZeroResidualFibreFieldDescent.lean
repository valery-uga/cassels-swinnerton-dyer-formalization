import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualFlatFieldStalk
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualEtaleFibreStalkField
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_fibre_stalks_isField_descend
    {X Y B T : Scheme.{u}} (g : X ⟶ Y) (i : B ⟶ Y)
    (k : T ⟶ B) [Flat k] [Surjective k]
    (hf : ∀ z : (pullback g (k ≫ i) : Scheme),
      IsField ((pullback g (k ≫ i)).presheaf.stalk z))
    (z : (pullback g i : Scheme)) :
    IsField ((pullback g i).presheaf.stalk z) := by
  apply cubicClosedPointSerreFiniteZeroResidual_flat_surjective_stalks_isField
    (pullback.fst (pullback.snd g i) k) _ z
  intro w
  let e := pullbackLeftPullbackSndIso g i k
  letI : Field ((pullback g (k ≫ i)).presheaf.stalk (e.hom w)) := (hf (e.hom w)).toField
  exact cubicClosedPointSerreFiniteZeroResidual_field_of_bijective
    (e.hom.stalkMap w).hom (ConcreteCategory.bijective_of_isIso (e.hom.stalkMap w))

end PfaffianDescent
