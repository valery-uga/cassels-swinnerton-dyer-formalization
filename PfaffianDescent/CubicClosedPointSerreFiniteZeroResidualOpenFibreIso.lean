import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualEtaleFibreStalkField
import Mathlib.AlgebraicGeometry.Restrict

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def cubicClosedPointSerreFiniteZeroResidual_openFibreIso
    {Z Y T : Scheme.{u}} (g : Z ⟶ Y) (U : Y.Opens) (i : T ⟶ (U : Scheme)) :
    pullback (g.resLE U (g ⁻¹ᵁ U) le_rfl) i ≅ pullback g (i ≫ U.ι) := by
  have H : IsPullback (g.resLE U (g ⁻¹ᵁ U) le_rfl) (g ⁻¹ᵁ U).ι U.ι g := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact isPullback_morphismRestrict g U
  exact ((IsPullback.of_hasPullback (g.resLE U (g ⁻¹ᵁ U) le_rfl) i).paste_horiz H.flip).isoPullback

theorem cubicClosedPointSerreFiniteZeroResidual_openFibre_stalks_isField
    {Z Y T : Scheme.{u}} (g : Z ⟶ Y) (U : Y.Opens) (i : T ⟶ (U : Scheme))
    (hf : ∀ z : (pullback g (i ≫ U.ι) : Scheme), IsField ((pullback g (i ≫ U.ι)).presheaf.stalk z))
    (z : (pullback (g.resLE U (g ⁻¹ᵁ U) le_rfl) i : Scheme)) :
    IsField ((pullback (g.resLE U (g ⁻¹ᵁ U) le_rfl) i).presheaf.stalk z) := by
  let e := cubicClosedPointSerreFiniteZeroResidual_openFibreIso g U i
  letI : Field ((pullback g (i ≫ U.ι)).presheaf.stalk (e.hom z)) := (hf (e.hom z)).toField
  exact cubicClosedPointSerreFiniteZeroResidual_field_of_bijective
    (e.hom.stalkMap z).hom (ConcreteCategory.bijective_of_isIso (e.hom.stalkMap z))

end PfaffianDescent
