import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualClosedFieldStalkDatum
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualFlatFieldStalk

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_fieldBaseChange_datum_eight
    {K E L : Type u} [Field K] [Field E] [Field L] [Algebra K E]
    {X Y : Scheme.{u}} (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (c : X ⟶ Y) [IsClosedImmersion c]
    (f : Y ⟶ Spec (.of K)) [IsFinite (c ≫ f)]
    (z : (pullback (c ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap K E))) : Scheme))
    (hz : pullback.fst (c ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap K E))) z =
      i (IsLocalRing.closedPoint L))
    (hfield : IsField ((pullback (c ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap K E)))).presheaf.stalk z))
    (hX : finiteSchemeRank (c ≫ f) = 11)
    (hL : finiteSchemeRank (i ≫ c ≫ f) = 3) :
    ∃ D : FiniteSubschemeDatum f 8,
      Disjoint (Set.range D.val.subschemeι) (Set.range (i ≫ c)) := by
  let r := Spec.map (CommRingCat.ofHom (algebraMap K E))
  letI : Flat r := (HasRingHomProperty.Spec_iff (P := @Flat)).mpr
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have ht := cubicClosedPointSerreFiniteZeroResidual_flat_stalk_isField
    (pullback.fst (c ≫ f) r) z hfield
  rw [hz] at ht
  apply cubicClosedPointSerreFiniteZeroResidual_closed_field_stalk_datum_eight i c f _ hX hL
  intro w
  have hw : w = IsLocalRing.closedPoint L := Subsingleton.elim _ _
  rw [hw]
  exact ht

end PfaffianDescent
