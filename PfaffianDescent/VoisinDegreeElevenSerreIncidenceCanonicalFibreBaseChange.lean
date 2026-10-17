import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSectionGraphFibre

/-! # Base-changing a literal canonical fibre identification -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def serreIncidenceCanonicalFibreBaseChangeIso
    {S P Z D T : Scheme.{u}} (z : Z ⟶ P) (t : S ⟶ P)
    (d : D ⟶ S) (v : D ≅ pullback z t)
    (hv : v.hom ≫ pullback.snd z t = d) (r : T ⟶ S) :
    pullback d r ≅ pullback z (r ≫ t) :=
  asIso (pullback.map d r (pullback.snd z t) r v.hom (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using hv.symm) (by simp)) ≪≫
      pullbackLeftPullbackSndIso z t r

@[reassoc]
theorem serreIncidenceCanonicalFibreBaseChangeIso_hom_snd
    {S P Z D T : Scheme.{u}} (z : Z ⟶ P) (t : S ⟶ P)
    (d : D ⟶ S) (v : D ≅ pullback z t)
    (hv : v.hom ≫ pullback.snd z t = d) (r : T ⟶ S) :
    (serreIncidenceCanonicalFibreBaseChangeIso z t d v hv r).hom ≫
      pullback.snd z (r ≫ t) = pullback.snd d r := by
  simp [serreIncidenceCanonicalFibreBaseChangeIso, Category.assoc, pullback.map]

end PfaffianDescent
