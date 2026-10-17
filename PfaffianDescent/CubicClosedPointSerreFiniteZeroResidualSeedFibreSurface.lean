import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSeedFibre

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

@[reassoc]
theorem cubicClosedPointSerreFiniteZeroResidual_seedFibreIso_hom_surface
    {S B X P Z T D : Scheme.{u}}
    (b : B ⟶ S) (x : X ⟶ S) (p : P ⟶ S)
    (marked : Fin 3 → (B ⟶ X)) (hm : ∀ n, marked n ≫ x = b)
    (zero : Z ⟶ pullback x p) [IsClosedImmersion zero]
    (s : T ⟶ serreThreePointSectionIncidence b x p marked hm zero)
    (t : S ⟶ P) (d : D ⟶ S) (i : D ⟶ X)
    (v : D ≅ pullback (zero ≫ pullback.snd x p) t)
    (hv : v.hom ≫ pullback.snd (zero ≫ pullback.snd x p) t = d)
    (hvi : v.hom ≫ pullback.fst (zero ≫ pullback.snd x p) t ≫
      zero ≫ pullback.fst x p = i)
    (r : T ⟶ S)
    (hs : s ≫ serreThreePointSectionIncidenceToParameters b x p marked hm zero = r ≫ t) :
    (serreIncidenceSeedCanonicalFibreIso b x p marked hm zero s t d v hv r hs).hom ≫
      pullback.fst (serreThreePointSectionIncidenceZeroFamily b x p marked hm zero) s ≫
      pullback.fst (zero ≫ pullback.snd x p)
        (serreThreePointSectionIncidenceToParameters b x p marked hm zero) ≫
      zero ≫ pullback.fst x p = pullback.fst d r ≫ i := by
  simp only [serreIncidenceSeedCanonicalFibreIso, Iso.trans_hom, Iso.symm_hom,
    serreIncidenceSeedFamilyFibreIso, Category.assoc,
    pullbackLeftPullbackSndIso_inv_fst_assoc]
  simp [serreIncidenceCanonicalFibreBaseChangeIso, Category.assoc, pullback.map, hvi]

end PfaffianDescent
