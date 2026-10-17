import PfaffianDescent.CubicClosedPointSerrePointSplittingAffineTensorProjection

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem pointSplittingFinitePullbackTensorIso_hom_coordinate
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {D : Scheme.{u}} (q : D ⟶ Spec (.of F)) [IsFinite q] [IsAffine D] :
    letI := finiteSchemeCoefficientAlgebra q
    (pointSplittingFinitePullbackTensorIso q).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        Γ(D, ⊤) →+* E ⊗[F] Γ(D, ⊤))) =
    pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap F E))) ≫ D.isoSpec.hom := by
  letI := finiteSchemeCoefficientAlgebra q
  dsimp only [pointSplittingFinitePullbackTensorIso]
  simp only [Iso.trans_hom, Category.assoc]
  erw [pullbackSpecIso_hom_snd]
  rw [pullbackSymmetry_hom_comp_snd, IsPullback.isoPullback_hom_fst]

end PfaffianDescent
