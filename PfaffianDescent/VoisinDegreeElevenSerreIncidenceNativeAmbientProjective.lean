import PfaffianDescent.SchemeAffineFunctions
import AllCharacteristics.ProjectiveBaseChange

/-! # Actual affine configuration times section parameters is relative projective space -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceAffineBase_isoSpec_inv
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K)) :
    B.isoSpec.inv ≫ b = Spec.map (CommRingCat.ofHom (affineFunctionHom b)) := by
  have h := from_affineFunctionHom b
  change B.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (affineFunctionHom b)) = b at h
  exact (congrArg (fun q => B.isoSpec.inv ≫ q) h.symm).trans
    (by rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp])

def serreIncidenceNativeAmbientProjectiveIso
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K)) :
    scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) ≅
      pullback b (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))) :=
  projectiveBaseChangeIso (affineFunctionHom b)
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) (by simp) ≪≫
  pullbackSymmetry _ _ ≪≫
  asIso (pullback.map _ _ b _ B.isoSpec.inv (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using (serreIncidenceAffineBase_isoSpec_inv b).symm)
    (by simp))

end PfaffianDescent
