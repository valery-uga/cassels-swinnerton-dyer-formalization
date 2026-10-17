import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOpenClosedRank
import PfaffianDescent.FiniteSubschemeResidualDatum

noncomputable section
open AlgebraicGeometry CategoryTheory AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- An actual open and closed degree-three part of a finite degree-eleven
zero scheme has a degree-eight residual datum on the original surface. -/
noncomputable def cubicClosedPointSerreFiniteZeroResidual_openClosed_datum_eight
    {K : Type u} [Field K] {X Y Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsOpenImmersion i]
    (c : X ⟶ Y) [IsClosedImmersion c]
    (f : Y ⟶ Spec (.of K)) [IsFinite (c ≫ f)]
    (hX : finiteSchemeRank (c ≫ f) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ f) = 3) :
    FiniteSubschemeDatum f 8 := by
  let r := finiteClosedResidualι i (c ≫ f)
  letI : IsClosedImmersion r := by dsimp [r]; infer_instance
  letI : IsFinite ((r ≫ c) ≫ f) := by
    rw [Category.assoc]
    dsimp [r]
    infer_instance
  letI : Flat ((r ≫ c) ≫ f) := by infer_instance
  letI : LocallyOfFinitePresentation ((r ≫ c) ≫ f) := by infer_instance
  have hr : finiteSchemeRank ((r ≫ c) ≫ f) = 8 := by
    simpa only [r, Category.assoc] using
      cubicClosedPointSerreFiniteZeroResidual_openClosed_rank_complement
        i (c ≫ f) 11 3 hX (by simpa only [Category.assoc] using hZ)
  exact finiteSubschemeDatumOfClosedImmersion (r ≫ c) f 8 (fun s => by
    have hs : s = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst s
    exact (finiteSchemeRank_eq_finrank ((r ≫ c) ≫ f)).symm.trans hr)

end PfaffianDescent
