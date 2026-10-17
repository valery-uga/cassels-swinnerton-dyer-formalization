import PfaffianDescent.VoisinDegreeElevenSerreIncidenceClosedFamily
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Actual graph pullbacks identify the actual universal zero fibre -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The graph of an actual section of the parameter base map is the actual
Cartesian square over that parameter section. -/
theorem serreIncidenceSectionGraph_isPullback
    {S X P : Scheme.{u}} (x : X ⟶ S) (p : P ⟶ S)
    (t : S ⟶ P) (ht : t ≫ p = 𝟙 S)
    (g : X ⟶ properFiniteIncidenceParameterSpace x p)
    (hgfst : g ≫ pullback.fst x p = 𝟙 X)
    (hgsnd : g ≫ pullback.snd x p = x ≫ t) :
    IsPullback g x (pullback.snd x p) t := by
  let e : pullback (pullback.snd x p) t ≅ X :=
    pullbackLeftPullbackSndIso x p t ≪≫ pullback.congrHom rfl ht ≪≫
      asIso (pullback.fst x (𝟙 S))
  let i := pullback.lift g x hgsnd
  have hi : i ≫ e.hom = 𝟙 X := by
    simp [e, pullback.congrHom, pullback.map, Category.assoc, i, hgfst]
  have hie : i = e.inv := by
    rw [← cancel_mono e.hom]
    exact hi.trans e.inv_hom_id.symm
  haveI : IsIso i := hie ▸ inferInstance
  exact IsPullback.of_iso_pullback ⟨hgsnd⟩ (asIso i)
    (by simp [i]) (by simp [i])

/-- The actual zero ideal pulled to a section graph has the same source as
the actual zero-family fibre over that parameter, by Cartesian pasting. -/
def serreIncidenceSectionGraphZeroFibreIso
    {S X P Z : Scheme.{u}} (x : X ⟶ S) (p : P ⟶ S)
    (t : S ⟶ P) (ht : t ≫ p = 𝟙 S)
    (g : X ⟶ properFiniteIncidenceParameterSpace x p)
    (hgfst : g ≫ pullback.fst x p = 𝟙 X)
    (hgsnd : g ≫ pullback.snd x p = x ≫ t)
    (zero : Z ⟶ properFiniteIncidenceParameterSpace x p) :
    pullback zero g ≅ pullback (zero ≫ pullback.snd x p) t :=
  ((IsPullback.of_hasPullback zero g).paste_vert
    (serreIncidenceSectionGraph_isPullback x p t ht g hgfst hgsnd)).isoPullback

@[reassoc]
theorem serreIncidenceSectionGraphZeroFibreIso_hom_snd
    {S X P Z : Scheme.{u}} (x : X ⟶ S) (p : P ⟶ S)
    (t : S ⟶ P) (ht : t ≫ p = 𝟙 S)
    (g : X ⟶ properFiniteIncidenceParameterSpace x p)
    (hgfst : g ≫ pullback.fst x p = 𝟙 X)
    (hgsnd : g ≫ pullback.snd x p = x ≫ t)
    (zero : Z ⟶ properFiniteIncidenceParameterSpace x p) :
    (serreIncidenceSectionGraphZeroFibreIso x p t ht g hgfst hgsnd zero).hom ≫
      pullback.snd (zero ≫ pullback.snd x p) t = pullback.snd zero g ≫ x :=
  ((IsPullback.of_hasPullback zero g).paste_vert
    (serreIncidenceSectionGraph_isPullback x p t ht g hgfst hgsnd)).isoPullback_hom_snd

end PfaffianDescent
