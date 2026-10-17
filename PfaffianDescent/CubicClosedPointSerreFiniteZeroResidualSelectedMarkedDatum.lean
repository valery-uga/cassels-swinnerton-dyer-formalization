import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualFieldBaseChangeDatum
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualMarkedFibreStalk
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualIncidenceMarkedOpen

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_selectedMarked_datum_eight
    {K E L : Type u} [Field K] [Field E] [Field L] [Algebra K E]
    {B X P Z X₀ : Scheme.{u}}
    (b : B ⟶ Spec (.of K)) (x : X ⟶ Spec (.of K)) (p : P ⟶ Spec (.of K))
    (marked : Fin 3 → (B ⟶ X)) (hm : ∀ n, marked n ≫ x = b)
    (zero : Z ⟶ pullback x p) [IsClosedImmersion zero]
    (s : Spec (.of E) ⟶ serreThreePointSectionIncidence b x p marked hm zero)
    (hs : s (IsLocalRing.closedPoint E) ∈
      cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen b x p marked hm zero)
    (n : Fin 3) (i : Spec (.of L) ⟶ X₀) [IsClosedImmersion i]
    (c : X₀ ⟶ X) [IsClosedImmersion c] [IsFinite (c ≫ x)]
    (e : pullback (serreThreePointSectionIncidenceZeroFamily b x p marked hm zero) s ≅
      pullback (c ≫ x) (Spec.map (CommRingCat.ofHom (algebraMap K E))))
    (hp :
      let g := serreThreePointSectionIncidenceZeroFamily b x p marked hm zero
      let j := serreIncidenceMarkedZeroSection b x p marked hm zero n
      let m := cubicClosedPointSerreFiniteZeroResidual_markedFibreSection g j
        (serreIncidenceMarkedZeroSection_toIncidence b x p marked hm zero n) s
      c (pullback.fst (c ≫ x) (Spec.map (CommRingCat.ofHom (algebraMap K E)))
        (e.hom (m (IsLocalRing.closedPoint E)))) = c (i (IsLocalRing.closedPoint L)))
    (hX : finiteSchemeRank (c ≫ x) = 11)
    (hL : finiteSchemeRank (i ≫ c ≫ x) = 3) :
    ∃ D : FiniteSubschemeDatum x 8,
      Disjoint (Set.range D.val.subschemeι) (Set.range (i ≫ c)) := by
  let g := serreThreePointSectionIncidenceZeroFamily b x p marked hm zero
  let j := serreIncidenceMarkedZeroSection b x p marked hm zero n
  let m := cubicClosedPointSerreFiniteZeroResidual_markedFibreSection g j
    (serreIncidenceMarkedZeroSection_toIncidence b x p marked hm zero n) s
  have hs' : s (IsLocalRing.closedPoint E) ∈
      cubicClosedPointSerreFiniteZeroResidual_markedSectionOpen g j := by
    apply (show cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen b x p marked hm zero ≤
      cubicClosedPointSerreFiniteZeroResidual_markedSectionOpen g j from iInf_le _ n)
    exact hs
  have hf := cubicClosedPointSerreFiniteZeroResidual_markedFibreSection_stalk_isField
    g j (serreIncidenceMarkedZeroSection_toIncidence b x p marked hm zero n) s
    (IsLocalRing.closedPoint E) hs'
  have ht := cubicClosedPointSerreFiniteZeroResidual_flat_stalk_isField
    e.hom (m (IsLocalRing.closedPoint E)) hf
  exact cubicClosedPointSerreFiniteZeroResidual_fieldBaseChange_datum_eight i c x
    (e.hom (m (IsLocalRing.closedPoint E))) (c.isClosedEmbedding.injective hp) ht hX hL

end PfaffianDescent
