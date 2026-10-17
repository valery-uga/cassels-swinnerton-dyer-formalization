import Mathlib.AlgebraicGeometry.Morphisms.Flat

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_stalk_flat_of_open_chart
    {X Y T : Scheme.{u}} (f : X ⟶ Y) (j : T ⟶ X) [IsOpenImmersion j]
    [Flat (j ≫ f)] (x : T) : (f.stalkMap (j x)).hom.Flat := by
  have h := Flat.stalkMap (j ≫ f) x
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at h
  exact (RingHom.Flat.comp_iff_of_bijective_left
    (ConcreteCategory.bijective_of_isIso (j.stalkMap x))).mp h

end PfaffianDescent
