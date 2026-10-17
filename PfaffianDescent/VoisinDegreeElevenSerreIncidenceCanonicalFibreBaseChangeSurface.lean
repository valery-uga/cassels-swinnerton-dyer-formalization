import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalFibreBaseChange

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u

@[reassoc]
theorem serreIncidenceCanonicalFibreBaseChangeIso_hom_fst
    {S P Z D T : Scheme.{u}} (z : Z ⟶ P) (t : S ⟶ P)
    (d : D ⟶ S) (v : D ≅ pullback z t)
    (hv : v.hom ≫ pullback.snd z t = d) (r : T ⟶ S) :
    (serreIncidenceCanonicalFibreBaseChangeIso z t d v hv r).hom ≫
        pullback.fst z (r ≫ t) =
      pullback.fst d r ≫ v.hom ≫ pullback.fst z t := by
  simp [serreIncidenceCanonicalFibreBaseChangeIso, Category.assoc, pullback.map,
    pullback.lift_fst_assoc]

@[reassoc]
theorem serreIncidenceCanonicalFibreBaseChangeIso_inv_fst
    {S P Z D T : Scheme.{u}} (z : Z ⟶ P) (t : S ⟶ P)
    (d : D ⟶ S) (v : D ≅ pullback z t)
    (hv : v.hom ≫ pullback.snd z t = d) (r : T ⟶ S) :
    (serreIncidenceCanonicalFibreBaseChangeIso z t d v hv r).inv ≫
        pullback.fst d r ≫ v.hom ≫ pullback.fst z t =
      pullback.fst z (r ≫ t) := by
  rw [← serreIncidenceCanonicalFibreBaseChangeIso_hom_fst z t d v hv r,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The actual selected-chart surface map is preserved by base change of its
literal canonical fibre identification. -/
@[reassoc]
theorem serreIncidenceCanonicalFibreBaseChangeIso_inv_surface
    {S P Z D T X : Scheme.{u}} (z : Z ⟶ P) (t : S ⟶ P)
    (d : D ⟶ S) (v : D ≅ pullback z t)
    (hv : v.hom ≫ pullback.snd z t = d) (r : T ⟶ S)
    (f : Z ⟶ X) (c : D ⟶ X)
    (hc : v.hom ≫ pullback.fst z t ≫ f = c) :
    (serreIncidenceCanonicalFibreBaseChangeIso z t d v hv r).inv ≫
        pullback.fst d r ≫ c = pullback.fst z (r ≫ t) ≫ f := by
  rw [← hc]
  simp only [Category.assoc,
    serreIncidenceCanonicalFibreBaseChangeIso_inv_fst_assoc]

end PfaffianDescent
