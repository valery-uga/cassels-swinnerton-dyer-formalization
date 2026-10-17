import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualMarkedOpenImmersion
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOpenClosedDatumDisjoint

noncomputable section
open AlgebraicGeometry CategoryTheory AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_marked_datum_eight
    {K : Type u} [Field K] {X Y Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (c : X ⟶ Y) [IsClosedImmersion c]
    (f : Y ⟶ Spec (.of K)) [IsFinite (c ≫ f)]
    [Etale (i ≫ (c ≫ f))]
    (hr : Set.range i ⊆ (cubicClosedPointSerreFiniteZeroResidual_etaleOpen (c ≫ f) : Set X))
    (hX : finiteSchemeRank (c ≫ f) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ f) = 3) :
    ∃ D : FiniteSubschemeDatum f 8,
      Disjoint (Set.range D.val.subschemeι) (Set.range (i ≫ c)) := by
  letI : IsOpenImmersion i :=
    cubicClosedPointSerreFiniteZeroResidual_marked_isOpenImmersion (c ≫ f) i hr
  exact ⟨cubicClosedPointSerreFiniteZeroResidual_openClosed_datum_eight i c f hX hZ,
    cubicClosedPointSerreFiniteZeroResidual_openClosed_datum_eight_disjoint i c f hX hZ⟩

end PfaffianDescent
