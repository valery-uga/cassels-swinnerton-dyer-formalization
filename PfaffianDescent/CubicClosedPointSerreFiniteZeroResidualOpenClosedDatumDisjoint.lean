import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOpenClosedDatum
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOpenClosedDisjoint

noncomputable section
open AlgebraicGeometry CategoryTheory AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_openClosed_datum_eight_disjoint
    {K : Type u} [Field K] {X Y Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsOpenImmersion i]
    (c : X ⟶ Y) [IsClosedImmersion c]
    (f : Y ⟶ Spec (.of K)) [IsFinite (c ≫ f)]
    (hX : finiteSchemeRank (c ≫ f) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ f) = 3) :
    Disjoint (Set.range
      (cubicClosedPointSerreFiniteZeroResidual_openClosed_datum_eight
        i c f hX hZ).val.subschemeι) (Set.range (i ≫ c)) := by
  let r := finiteClosedResidualι i (c ≫ f)
  letI : IsFinite ((r ≫ c) ≫ f) := by
    rw [Category.assoc]
    dsimp [r]
    infer_instance
  letI : Flat ((r ≫ c) ≫ f) := by infer_instance
  letI : LocallyOfFinitePresentation ((r ≫ c) ≫ f) := by infer_instance
  have hri : Disjoint (Set.range i) (Set.range r) :=
    cubicClosedPointSerreFiniteZeroResidual_openClosed_disjoint i (c ≫ f)
  have hcomp : Disjoint (Set.range (r ≫ c)) (Set.range (i ≫ c)) := by
    rw [Set.disjoint_left] at hri ⊢
    rintro x ⟨a, ha⟩ ⟨b, hb⟩
    apply hri ⟨b, rfl⟩
    exact ⟨a, c.isClosedEmbedding.injective (ha.trans hb.symm)⟩
  have hres : Set.range
      (cubicClosedPointSerreFiniteZeroResidual_openClosed_datum_eight
        i c f hX hZ).val.subschemeι ⊆ Set.range (r ≫ c) := by
    rw [← range_finiteSubschemeDatumSpecMap_eq_range_subschemeι]
    unfold cubicClosedPointSerreFiniteZeroResidual_openClosed_datum_eight
    apply finiteSubschemeDatumSpecMap_ofClosedImmersion_range_subset
  exact hcomp.mono_left hres

end PfaffianDescent
