import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelCoefficientIdeal
import PfaffianDescent.VoisinDegreeElevenSerreIncidencePlaneBaseChange

/-! # Literal native evaluation-kernel Proj over an actual field-valued configuration -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def serreIncidenceKernelBaseChangeIso
    {R E : Type u} [CommRing R] [CommRing E]
    {B I : Scheme.{u}} (a : Spec (.of R) ≅ B) (π : I ⟶ B)
    (A : Matrix (Fin 6) (Fin 9) R)
    (e : scheme (serreEvaluationHomogeneousIdeal A) ≅ I)
    (he : e.hom ≫ π = toBase (serreEvaluationHomogeneousIdeal A) ≫ a.hom)
    (β : R →+* E) (c : Spec (.of E) ⟶ B)
    (hc : Spec.map (CommRingCat.ofHom β) ≫ a.hom = c) :
    scheme (serreEvaluationHomogeneousIdeal (A.map β)) ≅ pullback π c :=
  projectiveBaseChangeIso β (serreEvaluationHomogeneousIdeal A)
    (serreEvaluationHomogeneousIdeal (A.map β)) (serreIncidenceKernelIdeal_coefficient β A) ≪≫
  asIso (pullback.map _ _ π c e.hom (𝟙 _) a.hom he.symm (by simpa using hc))

@[reassoc]
theorem serreIncidenceKernelBaseChangeIso_toBase
    {R E : Type u} [CommRing R] [CommRing E]
    {B I : Scheme.{u}} (a : Spec (.of R) ≅ B) (π : I ⟶ B)
    (A : Matrix (Fin 6) (Fin 9) R)
    (e : scheme (serreEvaluationHomogeneousIdeal A) ≅ I)
    (he : e.hom ≫ π = toBase (serreEvaluationHomogeneousIdeal A) ≫ a.hom)
    (β : R →+* E) (c : Spec (.of E) ⟶ B)
    (hc : Spec.map (CommRingCat.ofHom β) ≫ a.hom = c) :
    (serreIncidenceKernelBaseChangeIso a π A e he β c hc).hom ≫ pullback.snd π c =
      toBase (serreEvaluationHomogeneousIdeal (A.map β)) := by
  simp only [serreIncidenceKernelBaseChangeIso, Iso.trans_hom, asIso_hom,
    Category.assoc, pullback.map, pullback.lift_snd, Category.comp_id]
  exact projectiveBaseChangeIso_hom_snd β _ _ _

@[reassoc]
theorem serreIncidenceKernelBaseChangeIso_toOriginal
    {R E : Type u} [CommRing R] [CommRing E]
    {B I : Scheme.{u}} (a : Spec (.of R) ≅ B) (π : I ⟶ B)
    (A : Matrix (Fin 6) (Fin 9) R)
    (e : scheme (serreEvaluationHomogeneousIdeal A) ≅ I)
    (he : e.hom ≫ π = toBase (serreEvaluationHomogeneousIdeal A) ≫ a.hom)
    (β : R →+* E) (c : Spec (.of E) ⟶ B)
    (hc : Spec.map (CommRingCat.ofHom β) ≫ a.hom = c) :
    (serreIncidenceKernelBaseChangeIso a π A e he β c hc).hom ≫ pullback.fst π c =
      projectiveCoefficientMap β (serreEvaluationHomogeneousIdeal A)
        (serreEvaluationHomogeneousIdeal (A.map β))
        (serreIncidenceKernelIdeal_coefficient β A) ≫ e.hom := by
  simp only [serreIncidenceKernelBaseChangeIso, Iso.trans_hom, asIso_hom,
    Category.assoc, pullback.map, pullback.lift_fst]
  rw [← Category.assoc, projectiveBaseChangeIso_hom_fst]

end PfaffianDescent
