import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSectionGraphFibre
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualIdealCover

/-! # Native closed-immersion identification of an actual graph zero fibre -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def serreIncidenceClosedGraphZeroIso
    {S X P Z D : Scheme.{u}} (x : X ⟶ S) (p : P ⟶ S)
    (t : S ⟶ P) (ht : t ≫ p = 𝟙 S)
    (g : X ⟶ properFiniteIncidenceParameterSpace x p)
    (hgfst : g ≫ pullback.fst x p = 𝟙 X)
    (hgsnd : g ≫ pullback.snd x p = x ≫ t)
    (zero : Z ⟶ properFiniteIncidenceParameterSpace x p) [IsClosedImmersion zero]
    (i : D ⟶ X) [IsClosedImmersion i] (h : zero.ker.comap g = i.ker) :
    D ≅ pullback (zero ≫ pullback.snd x p) t := by
  let c := pullback.snd zero g
  have hc : c.ker = i.ker :=
    (cubicClosedPointSerreFiniteZeroResidual_pullback_snd_kernel zero g).trans h
  let w := IsClosedImmersion.lift c i hc.le
  letI : IsIso w := IsClosedImmersion.isIso_lift c i hc
  exact asIso w ≪≫ serreIncidenceSectionGraphZeroFibreIso x p t ht g hgfst hgsnd zero

@[reassoc]
theorem serreIncidenceClosedGraphZeroIso_hom_snd
    {S X P Z D : Scheme.{u}} (x : X ⟶ S) (p : P ⟶ S)
    (t : S ⟶ P) (ht : t ≫ p = 𝟙 S)
    (g : X ⟶ properFiniteIncidenceParameterSpace x p)
    (hgfst : g ≫ pullback.fst x p = 𝟙 X)
    (hgsnd : g ≫ pullback.snd x p = x ≫ t)
    (zero : Z ⟶ properFiniteIncidenceParameterSpace x p) [IsClosedImmersion zero]
    (i : D ⟶ X) [IsClosedImmersion i] (h : zero.ker.comap g = i.ker) :
    (serreIncidenceClosedGraphZeroIso x p t ht g hgfst hgsnd zero i h).hom ≫
      pullback.snd (zero ≫ pullback.snd x p) t = i ≫ x := by
  simp only [serreIncidenceClosedGraphZeroIso, Iso.trans_hom, asIso_hom,
    Category.assoc, serreIncidenceSectionGraphZeroFibreIso_hom_snd]
  rw [← Category.assoc, IsClosedImmersion.lift_fac]

end PfaffianDescent
