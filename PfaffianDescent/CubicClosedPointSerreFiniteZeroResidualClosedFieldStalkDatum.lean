import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualClosedFieldStalkOpen
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOpenClosedDatumDisjoint
import Mathlib.AlgebraicGeometry.Noetherian

noncomputable section
open AlgebraicGeometry CategoryTheory AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_closed_field_stalk_datum_eight
    {K : Type u} [Field K] {X Y Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (c : X ⟶ Y) [IsClosedImmersion c]
    (f : Y ⟶ Spec (.of K)) [IsFinite (c ≫ f)]
    (hf : ∀ z : Z, IsField (X.presheaf.stalk (i z)))
    (hX : finiteSchemeRank (c ≫ f) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ f) = 3) :
    ∃ D : FiniteSubschemeDatum f 8,
      Disjoint (Set.range D.val.subschemeι) (Set.range (i ≫ c)) := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (c ≫ f)
  letI : IsOpenImmersion i :=
    cubicClosedPointSerreFiniteZeroResidual_closed_field_stalk_open i hf
  exact ⟨cubicClosedPointSerreFiniteZeroResidual_openClosed_datum_eight i c f hX hZ,
    cubicClosedPointSerreFiniteZeroResidual_openClosed_datum_eight_disjoint i c f hX hZ⟩

end PfaffianDescent
