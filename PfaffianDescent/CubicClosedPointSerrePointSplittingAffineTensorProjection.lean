import PfaffianDescent.CubicClosedPointSerrePointSplittingAffineTensor

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

@[reassoc] theorem pointSplittingFinitePullbackTensorIso_inv_snd
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {D : Scheme.{u}} (q : D ⟶ Spec (.of F)) [IsFinite q] :
    letI := finiteSchemeCoefficientAlgebra q
    (pointSplittingFinitePullbackTensorIso q).inv ≫
      pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap F E))) =
    Spec.map (CommRingCat.ofHom (algebraMap E (E ⊗[F] Γ(D, ⊤)))) := by
  letI := finiteSchemeCoefficientAlgebra q
  dsimp only [pointSplittingFinitePullbackTensorIso]
  simp only [Iso.trans_inv, Category.assoc, IsPullback.isoPullback_inv_snd,
    pullbackSymmetry_inv_comp_snd]
  exact pullbackSpecIso_inv_fst' F E Γ(D, ⊤)

@[reassoc] theorem pointSplittingFinitePullbackTensorIso_hom_base
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {D : Scheme.{u}} (q : D ⟶ Spec (.of F)) [IsFinite q] :
    letI := finiteSchemeCoefficientAlgebra q
    (pointSplittingFinitePullbackTensorIso q).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap E (E ⊗[F] Γ(D, ⊤)))) =
    pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap F E))) := by
  letI := finiteSchemeCoefficientAlgebra q
  apply (cancel_epi (pointSplittingFinitePullbackTensorIso q).inv).1
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact (pointSplittingFinitePullbackTensorIso_inv_snd q).symm

end PfaffianDescent
