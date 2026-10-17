import PfaffianDescent.ActualQuarticDualTensorCoordinates
import PfaffianDescent.SingleSupportGeometricSchemeSplitting

/-! The embedding-indexed product-dual presentation retains the actual
projection to the originally supplied scheme, rather than replacing it by
an unrelated abstract coproduct presentation. -/

noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open scoped TensorProduct
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K]
  [IsAlgClosed K] [FiniteDimensional k L] [Algebra.IsSeparable k L]

/-- Exact product-dual presentation of the actual field base change of Z,
indexed by the same full embeddings as its tangent matrix. -/
def actualQuarticTensorSchemeIso
    {Z : Scheme.{u}} (t : Z ⟶ Spec (.of k)) [IsFinite t]
    (eA : letI := finiteSchemeCoefficientAlgebra t
      Γ(Z, ⊤) ≃ₐ[k] DualNumber L)
    (b : Basis (Fin 4) k L) (full : Fin 4 ≃ (L →ₐ[k] K)) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) t ≅
      Spec (.of (FourTangentDualAlgebra K)) := by
  letI := finiteSchemeCoefficientAlgebra t
  let theta := actualQuarticDualTensorEquiv eA b full
  exact finiteSchemeActualFieldBaseChangeIso (K := K) t ≪≫
    Scheme.Spec.mapIso theta.toRingEquiv.toCommRingCatIso.symm.op

/-- Pulling back through the literal tensor evaluator reconstructs the
projection to the SAME original Z, including its nilpotent structure. -/
theorem actualQuarticTensorSchemeIso_hom_toOriginal
    {Z : Scheme.{u}} (t : Z ⟶ Spec (.of k)) [IsFinite t]
    (eA : letI := finiteSchemeCoefficientAlgebra t
      Γ(Z, ⊤) ≃ₐ[k] DualNumber L)
    (b : Basis (Fin 4) k L) (full : Fin 4 ≃ (L →ₐ[k] K)) :
    letI := finiteSchemeCoefficientAlgebra t
    letI : IsAffine Z := isAffine_of_isAffineHom t
    (actualQuarticTensorSchemeIso t eA b full).hom ≫
      Spec.map (CommRingCat.ofHom
        ((actualQuarticDualTensorEquiv eA b full).toRingHom.comp
          (Algebra.TensorProduct.includeRight : Γ(Z, ⊤) →ₐ[k]
            K ⊗[k] Γ(Z, ⊤)).toRingHom)) ≫ Z.isoSpec.inv =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) t := by
  letI := finiteSchemeCoefficientAlgebra t
  letI : IsAffine Z := isAffine_of_isAffineHom t
  let theta := actualQuarticDualTensorEquiv eA b full
  have hcompose : CommRingCat.ofHom
      (theta.toRingHom.comp (Algebra.TensorProduct.includeRight :
        Γ(Z, ⊤) →ₐ[k] K ⊗[k] Γ(Z, ⊤)).toRingHom) =
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        Γ(Z, ⊤) →ₐ[k] K ⊗[k] Γ(Z, ⊤)).toRingHom ≫
        CommRingCat.ofHom theta.toRingHom := rfl
  change ((finiteSchemeActualFieldBaseChangeIso (K := K) t) ≪≫
    Scheme.Spec.mapIso theta.toRingEquiv.toCommRingCatIso.symm.op).hom ≫ _ ≫ _ = _
  rw [hcompose, Spec.map_comp]
  simp only [Iso.trans_hom, Scheme.Spec.mapIso_hom, Category.assoc]
  have hcancel : Spec.map theta.toRingEquiv.toCommRingCatIso.inv ≫
      Spec.map (CommRingCat.ofHom theta.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp]
    change Spec.map (theta.toRingEquiv.toCommRingCatIso.hom ≫
      theta.toRingEquiv.toCommRingCatIso.inv) = _
    rw [Iso.hom_inv_id, Spec.map_id]
  erw [← Category.assoc (Spec.map theta.toRingEquiv.toCommRingCatIso.inv),
    hcancel, Category.id_comp]
  exact finiteSchemeActualFieldBaseChangeIso_hom_toOriginal (K := K) t

end PfaffianDescent.QuarticNet
