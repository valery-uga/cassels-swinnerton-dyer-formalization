import PfaffianDescent.VoisinDegreeElevenSerreIncidenceClosedGraphFibre

/-! # Literal surface projection of the actual canonical fibre isomorphism -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

@[reassoc]
theorem serreIncidenceSectionGraphZeroFibreIso_hom_fst
    {S X P Z : Scheme.{u}} (x : X ⟶ S) (p : P ⟶ S)
    (t : S ⟶ P) (ht : t ≫ p = 𝟙 S)
    (g : X ⟶ properFiniteIncidenceParameterSpace x p)
    (hgfst : g ≫ pullback.fst x p = 𝟙 X)
    (hgsnd : g ≫ pullback.snd x p = x ≫ t)
    (zero : Z ⟶ properFiniteIncidenceParameterSpace x p) :
    (serreIncidenceSectionGraphZeroFibreIso x p t ht g hgfst hgsnd zero).hom ≫
      pullback.fst (zero ≫ pullback.snd x p) t = pullback.fst zero g :=
  ((IsPullback.of_hasPullback zero g).paste_vert
    (serreIncidenceSectionGraph_isPullback x p t ht g hgfst hgsnd)).isoPullback_hom_fst

@[reassoc]
theorem serreIncidenceClosedGraphZeroIso_hom_surface
    {S X P Z D : Scheme.{u}} (x : X ⟶ S) (p : P ⟶ S)
    (t : S ⟶ P) (ht : t ≫ p = 𝟙 S)
    (g : X ⟶ properFiniteIncidenceParameterSpace x p)
    (hgfst : g ≫ pullback.fst x p = 𝟙 X)
    (hgsnd : g ≫ pullback.snd x p = x ≫ t)
    (zero : Z ⟶ properFiniteIncidenceParameterSpace x p) [IsClosedImmersion zero]
    (i : D ⟶ X) [IsClosedImmersion i] (h : zero.ker.comap g = i.ker) :
    (serreIncidenceClosedGraphZeroIso x p t ht g hgfst hgsnd zero i h).hom ≫
      pullback.fst (zero ≫ pullback.snd x p) t ≫ zero ≫ pullback.fst x p = i := by
  simp only [serreIncidenceClosedGraphZeroIso, Iso.trans_hom, asIso_hom,
    Category.assoc, serreIncidenceSectionGraphZeroFibreIso_hom_fst_assoc]
  rw [pullback.condition_assoc, hgfst, Category.comp_id, IsClosedImmersion.lift_fac]

end PfaffianDescent
