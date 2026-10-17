import AllCharacteristics.FiniteSubschemeClosedImmersionPushforward
import PfaffianDescent.FiniteSubschemeResidualDatum
import PfaffianDescent.FiniteEtaleResidualDisjoint

/-!
# Disjoint finite-subscheme data from an étale residual

For Voisin's rank-two construction, a degree-three closed component inside a
finite étale degree-eleven scheme has an annihilator residual of degree eight.
This file proves that the two induced finite-subscheme data on the ambient
surface have disjoint support.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open AllCharacteristics

universe u

/-- The degree-three finite-subscheme datum carried by a closed component of
a finite scheme on an ambient surface. -/
noncomputable def finiteSubschemeDatumRankThreeOfClosedComponent
    {K : Type u} [Field K] {X Y Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (c : X ⟶ Y) [IsClosedImmersion c]
    (f : Y ⟶ Spec (.of K)) [IsFinite (c ≫ f)]
    (hZ : finiteSchemeRank (i ≫ c ≫ f) = 3) :
    FiniteSubschemeDatum f 3 := by
  let _ : IsFinite ((i ≫ c) ≫ f) := by
    rw [Category.assoc]
    infer_instance
  let _ : Flat ((i ≫ c) ≫ f) := by infer_instance
  let _ : LocallyOfFinitePresentation ((i ≫ c) ≫ f) := by infer_instance
  apply finiteSubschemeDatumOfClosedImmersion (i ≫ c) f 3
  intro s
  have hs : s = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  subst s
  rw [← finiteSchemeRank_eq_finrank]
  exact hZ

/-- The rank-eight annihilator residual and the rank-three closed component of
a finite étale rank-eleven scheme induce disjoint finite-subscheme data on the
ambient scheme. -/
theorem disjoint_rankEightResidual_rankThreeComponent_of_etale
    {K : Type u} [Field K] [CharZero K] {X Y Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (c : X ⟶ Y) [IsClosedImmersion c]
    (f : Y ⟶ Spec (.of K)) [IsFinite (c ≫ f)] [Etale (c ≫ f)]
    (hX : finiteSchemeRank (c ≫ f) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ f) = 3) :
    Disjoint
      (Set.range (finiteSubschemeDatumSpecMap f
        (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual i c f hX hZ)))
      (Set.range (finiteSubschemeDatumSpecMap f
        (finiteSubschemeDatumRankThreeOfClosedComponent i c f hZ)) ) := by
  let r := finiteClosedResidualι i (c ≫ f)
  have hri : Disjoint (Set.range i) (Set.range r) :=
    disjoint_range_closedImmersion_finiteClosedResidualι_of_finiteEtale i (c ≫ f)
  have hcomp : Disjoint (Set.range (r ≫ c)) (Set.range (i ≫ c)) := by
    rw [Set.disjoint_left] at hri ⊢
    rintro x ⟨a, ha⟩ ⟨b, hb⟩
    apply hri (show i b ∈ Set.range i from ⟨b, rfl⟩)
    exact ⟨a, c.isClosedEmbedding.injective (ha.trans hb.symm)⟩
  let _ : IsFinite ((r ≫ c) ≫ f) := by
    rw [Category.assoc]
    dsimp [r]
    infer_instance
  let _ : Flat ((r ≫ c) ≫ f) := by infer_instance
  let _ : LocallyOfFinitePresentation ((r ≫ c) ≫ f) := by infer_instance
  have h8 : Set.range (finiteSubschemeDatumSpecMap f
      (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual i c f hX hZ)) ⊆
      Set.range (r ≫ c) := by
    unfold finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
    unfold finiteSubschemeDatumRankEightOfRankElevenResidual
    unfold finiteSubschemeDatumOfFiniteResidualOnAmbient
    apply finiteSubschemeDatumSpecMap_ofClosedImmersion_range_subset
  let _ : IsFinite ((i ≫ c) ≫ f) := by
    rw [Category.assoc]
    infer_instance
  let _ : Flat ((i ≫ c) ≫ f) := by infer_instance
  let _ : LocallyOfFinitePresentation ((i ≫ c) ≫ f) := by infer_instance
  have h3 : Set.range (finiteSubschemeDatumSpecMap f
      (finiteSubschemeDatumRankThreeOfClosedComponent i c f hZ)) ⊆
      Set.range (i ≫ c) := by
    unfold finiteSubschemeDatumRankThreeOfClosedComponent
    apply finiteSubschemeDatumSpecMap_ofClosedImmersion_range_subset
  rw [Set.disjoint_left] at hcomp ⊢
  intro x hx8 hx3
  exact hcomp (h8 hx8) (h3 hx3)

end PfaffianDescent
