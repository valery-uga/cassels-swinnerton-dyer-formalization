import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualSelectedMarkedDatum
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualSeedFibreSurface
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualMarkedFibreSurface

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_selected_incidence_datum_eight
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
    (t : Spec (.of K) ⟶ P)
    (v : X₀ ≅ pullback (zero ≫ pullback.snd x p) t)
    (hv : v.hom ≫ pullback.snd (zero ≫ pullback.snd x p) t = c ≫ x)
    (hvc : v.hom ≫ pullback.fst (zero ≫ pullback.snd x p) t ≫
      zero ≫ pullback.fst x p = c)
    (hsp : s ≫ serreThreePointSectionIncidenceToParameters b x p marked hm zero =
      Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ t)
    (hp : (s ≫ serreThreePointSectionIncidenceToConfiguration b x p marked hm zero ≫
      marked n) (IsLocalRing.closedPoint E) = c (i (IsLocalRing.closedPoint L)))
    (hX : finiteSchemeRank (c ≫ x) = 11)
    (hL : finiteSchemeRank (i ≫ c ≫ x) = 3) :
    ∃ D : FiniteSubschemeDatum x 8,
      Disjoint (Set.range D.val.subschemeι) (Set.range (i ≫ c)) := by
  let r := Spec.map (CommRingCat.ofHom (algebraMap K E))
  let g := serreThreePointSectionIncidenceZeroFamily b x p marked hm zero
  let j := serreIncidenceMarkedZeroSection b x p marked hm zero n
  let m := cubicClosedPointSerreFiniteZeroResidual_markedFibreSection g j
    (serreIncidenceMarkedZeroSection_toIncidence b x p marked hm zero n) s
  let e := serreIncidenceSeedCanonicalFibreIso b x p marked hm zero s t (c ≫ x) v hv r hsp
  let q := pullback.fst g s ≫ pullback.fst (zero ≫ pullback.snd x p)
    (serreThreePointSectionIncidenceToParameters b x p marked hm zero) ≫
    zero ≫ pullback.fst x p
  have he : e.hom ≫ q = pullback.fst (c ≫ x) r ≫ c :=
    cubicClosedPointSerreFiniteZeroResidual_seedFibreIso_hom_surface
      b x p marked hm zero s t (c ≫ x) c v hv hvc r hsp
  have hei : e.inv ≫ pullback.fst (c ≫ x) r ≫ c = q := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hmproj : m ≫ q = s ≫ serreThreePointSectionIncidenceToConfiguration
      b x p marked hm zero ≫ marked n :=
    cubicClosedPointSerreFiniteZeroResidual_markedFibreSection_surface
      b x p marked hm zero s n
  apply cubicClosedPointSerreFiniteZeroResidual_selectedMarked_datum_eight
    b x p marked hm zero s hs n i c e.symm _ hX hL
  change c (pullback.fst (c ≫ x) r (e.inv (m (IsLocalRing.closedPoint E)))) = _
  calc
    _ = (e.inv ≫ pullback.fst (c ≫ x) r ≫ c) (m (IsLocalRing.closedPoint E)) := by
      simp only [Scheme.Hom.comp_apply]
    _ = q (m (IsLocalRing.closedPoint E)) := congrArg (fun f : pullback g s ⟶ X => f (m (IsLocalRing.closedPoint E))) hei
    _ = (m ≫ q) (IsLocalRing.closedPoint E) := by simp only [Scheme.Hom.comp_apply]
    _ = _ := (congrArg (fun f => f (IsLocalRing.closedPoint E)) hmproj).trans hp

end PfaffianDescent
