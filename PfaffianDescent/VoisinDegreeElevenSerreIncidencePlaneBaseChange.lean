import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativePlane
import AllCharacteristics.ProjectiveBaseChange

/-! # The actual plane incidence frame base changes over a literal field-valued configuration -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def serreIncidencePlaneBaseChangeIso
    {R F : Type u} [CommRing R] [CommRing F]
    {B I : Scheme.{u}} (a : Spec (.of R) ≅ B) (π : I ⟶ B)
    (e : scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R)) ≅ I)
    (he : e.hom ≫ π = toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 3) R)) ≫ a.hom)
    (β : R →+* F) (c : Spec (.of F) ⟶ B)
    (hc : Spec.map (CommRingCat.ofHom β) ≫ a.hom = c) :
    scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)) ≅ pullback π c :=
  projectiveBaseChangeIso β
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R))
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)) (by simp) ≪≫
  asIso (pullback.map _ _ π c e.hom (𝟙 _) a.hom he.symm (by simpa using hc))

@[reassoc]
theorem serreIncidencePlaneBaseChangeIso_toBase
    {R F : Type u} [CommRing R] [CommRing F]
    {B I : Scheme.{u}} (a : Spec (.of R) ≅ B) (π : I ⟶ B)
    (e : scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R)) ≅ I)
    (he : e.hom ≫ π = toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 3) R)) ≫ a.hom)
    (β : R →+* F) (c : Spec (.of F) ⟶ B)
    (hc : Spec.map (CommRingCat.ofHom β) ≫ a.hom = c) :
    (serreIncidencePlaneBaseChangeIso a π e he β c hc).hom ≫ pullback.snd π c =
      toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)) := by
  simp only [serreIncidencePlaneBaseChangeIso, Iso.trans_hom, asIso_hom,
    Category.assoc, pullback.map, pullback.lift_snd, Category.comp_id]
  exact projectiveBaseChangeIso_hom_snd β _ _ _

@[reassoc]
theorem serreIncidencePlaneBaseChangeIso_frame
    {R F : Type u} [CommRing R] [CommRing F]
    {B I : Scheme.{u}} (a : Spec (.of R) ≅ B) (π : I ⟶ B)
    (e : scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R)) ≅ I)
    (he : e.hom ≫ π = toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 3) R)) ≫ a.hom)
    (β : R →+* F) (c : Spec (.of F) ⟶ B)
    (hc : Spec.map (CommRingCat.ofHom β) ≫ a.hom = c) :
    (serreIncidencePlaneBaseChangeIso a π e he β c hc).hom ≫ pullback.fst π c ≫ π =
      toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)) ≫ c := by
  rw [pullback.condition, ← Category.assoc, serreIncidencePlaneBaseChangeIso_toBase]

end PfaffianDescent
