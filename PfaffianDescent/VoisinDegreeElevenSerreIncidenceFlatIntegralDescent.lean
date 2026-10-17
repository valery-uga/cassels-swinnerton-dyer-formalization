import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Actual integral source descends along a flat surjective morphism -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceFlatSurjective_integral
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [IsIntegral X] :
    IsIntegral Y := by
  letI : IrreducibleSpace Y := f.surjective.irreducibleSpace f.continuous
  letI : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := fun y => by
    obtain ⟨x,rfl⟩ := f.surjective y
    algebraize [(f.stalkMap x).hom]
    have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap f x) (f.toLRSHom.prop x)
    exact isReduced_of_injective (f.stalkMap x).hom
      (‹RingHom.FaithfullyFlat _›.injective)
  letI : IsReduced Y := isReduced_of_isReduced_stalk Y
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

end PfaffianDescent
