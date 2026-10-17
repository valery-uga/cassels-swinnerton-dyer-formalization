import PfaffianDescent.VoisinDegreeElevenSerreIncidenceProductRankTransport

/-! # Actual closed subschemes transport along the ambient isomorphism -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def serreIncidenceIdealIsoTransport
    {X Y : Scheme.{u}} (e : X ≅ Y) (I : X.IdealSheafData) :
    (I.comap e.inv).subscheme ≅ I.subscheme :=
  I.comapIso e.inv ≪≫ asIso (pullback.snd e.inv I.subschemeι)

@[reassoc]
theorem serreIncidenceIdealIsoTransport_subschemeι
    {X Y : Scheme.{u}} (e : X ≅ Y) (I : X.IdealSheafData) :
    (serreIncidenceIdealIsoTransport e I).hom ≫ I.subschemeι =
      (I.comap e.inv).subschemeι ≫ e.inv := by
  simp only [serreIncidenceIdealIsoTransport, Iso.trans_hom, asIso_hom,
    Category.assoc, ← pullback.condition]
  rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]

end PfaffianDescent
