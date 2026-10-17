import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSeedFibre

/-! # Exact structural projection of the actual canonical incidence seed fibre -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

@[reassoc]
theorem serreIncidenceSeedCanonicalFibreIso_hom_snd
    {S B X P Z T D : Scheme.{u}}
    (b : B ⟶ S) (x : X ⟶ S) (p : P ⟶ S)
    (marked : Fin 3 → (B ⟶ X)) (hm : ∀ i, marked i ≫ x = b)
    (zero : Z ⟶ pullback x p) [IsClosedImmersion zero]
    (s : T ⟶ serreThreePointSectionIncidence b x p marked hm zero)
    (t : S ⟶ P) (d : D ⟶ S)
    (v : D ≅ pullback (zero ≫ pullback.snd x p) t)
    (hv : v.hom ≫ pullback.snd (zero ≫ pullback.snd x p) t = d)
    (r : T ⟶ S)
    (hs : s ≫ serreThreePointSectionIncidenceToParameters b x p marked hm zero = r ≫ t) :
    (serreIncidenceSeedCanonicalFibreIso b x p marked hm zero s t d v hv r hs).hom ≫
      pullback.snd (serreThreePointSectionIncidenceZeroFamily b x p marked hm zero) s =
    pullback.snd d r := by
  have hi : (serreIncidenceSeedFamilyFibreIso b x p marked hm zero s).inv ≫
      pullback.snd (serreThreePointSectionIncidenceZeroFamily b x p marked hm zero) s =
      pullback.snd (zero ≫ pullback.snd x p)
        (s ≫ serreThreePointSectionIncidenceToParameters b x p marked hm zero) := by
    rw [Iso.inv_comp_eq]
    exact (serreIncidenceSeedFamilyFibreIso_hom_snd b x p marked hm zero s).symm
  simp only [serreIncidenceSeedCanonicalFibreIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, hi]
  simp [pullback.congrHom, pullback.map, Category.assoc,
    serreIncidenceCanonicalFibreBaseChangeIso_hom_snd]

end PfaffianDescent
