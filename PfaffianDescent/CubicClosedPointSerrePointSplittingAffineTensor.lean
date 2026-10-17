import PfaffianDescent.FiniteSchemeAlgebra
import Mathlib.AlgebraicGeometry.Pullbacks

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The scalar extension of the actual finite scheme has the canonical
coordinate algebra E tensor Gamma(D), with the genuine finite-scheme action. -/
def pointSplittingFinitePullbackTensorIso
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {D : Scheme.{u}} (q : D ⟶ Spec (.of F)) [IsFinite q] :
    letI := finiteSchemeCoefficientAlgebra q
    pullback q (Spec.map (CommRingCat.ofHom (algebraMap F E))) ≅
      Spec (.of (E ⊗[F] Γ(D, ⊤))) := by
  letI := finiteSchemeCoefficientAlgebra q
  letI : IsAffine D := isAffine_of_isAffineHom q
  let b := Spec.map (CommRingCat.ofHom (algebraMap F E))
  let a := Spec.map (CommRingCat.ofHom (algebraMap F Γ(D, ⊤)))
  have h : IsPullback (pullback.fst q b ≫ D.isoSpec.hom)
      (pullback.snd q b) a b := by
    apply (IsPullback.of_hasPullback q b).of_iso
      (Iso.refl _) D.isoSpec (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · simp only [Iso.refl_hom, Category.comp_id]
      dsimp only [a]
      rw [finiteSchemeCoefficient_spec q, Iso.hom_inv_id_assoc]
    · simp
  exact h.isoPullback ≪≫ pullbackSymmetry a b ≪≫
    pullbackSpecIso F E Γ(D, ⊤)

end PfaffianDescent
