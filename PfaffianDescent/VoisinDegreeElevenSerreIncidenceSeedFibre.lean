import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalFibreBaseChange
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSeedFactor

/-! # The actual incidence seed fibre is the literal canonical parameter fibre -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

section
variable {S B X P Z T D : Scheme.{u}}
variable (b : B ⟶ S) (x : X ⟶ S) (p : P ⟶ S)
variable (marked : Fin 3 → (B ⟶ X)) (hm : ∀ i, marked i ≫ x = b)
variable (zero : Z ⟶ pullback x p) [IsClosedImmersion zero]
variable (s : T ⟶ serreThreePointSectionIncidence b x p marked hm zero)

def serreIncidenceSeedFamilyFibreIso :
    pullback (serreThreePointSectionIncidenceZeroFamily b x p marked hm zero) s ≅
      pullback (zero ≫ pullback.snd x p)
        (s ≫ serreThreePointSectionIncidenceToParameters b x p marked hm zero) :=
  pullbackLeftPullbackSndIso (zero ≫ pullback.snd x p)
    (serreThreePointSectionIncidenceToParameters b x p marked hm zero) s

@[reassoc]
theorem serreIncidenceSeedFamilyFibreIso_hom_snd :
    (serreIncidenceSeedFamilyFibreIso b x p marked hm zero s).hom ≫
      pullback.snd (zero ≫ pullback.snd x p)
        (s ≫ serreThreePointSectionIncidenceToParameters b x p marked hm zero) =
    pullback.snd (serreThreePointSectionIncidenceZeroFamily b x p marked hm zero) s :=
  pullbackLeftPullbackSndIso_hom_snd _ _ _

def serreIncidenceSeedCanonicalFibreIso
    (t : S ⟶ P) (d : D ⟶ S)
    (v : D ≅ pullback (zero ≫ pullback.snd x p) t)
    (hv : v.hom ≫ pullback.snd (zero ≫ pullback.snd x p) t = d)
    (r : T ⟶ S)
    (hs : s ≫ serreThreePointSectionIncidenceToParameters b x p marked hm zero = r ≫ t) :
    pullback d r ≅
      pullback (serreThreePointSectionIncidenceZeroFamily b x p marked hm zero) s :=
  serreIncidenceCanonicalFibreBaseChangeIso (zero ≫ pullback.snd x p) t d v hv r ≪≫
    pullback.congrHom rfl hs.symm ≪≫
    (serreIncidenceSeedFamilyFibreIso b x p marked hm zero s).symm

end
end PfaffianDescent
