import PfaffianDescent.CubicClosedPointSerrePointSplittingSectionTensorApply

noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

variable {F A E : Type u} [Field F] [Field A] [Field E] [Algebra F A] [Algebra F E]
variable (α : Fin 3 → (A →ₐ[F] E)) (I : Type u) [Fintype I] [DecidableEq I]
variable (M : (Spec (.of A)).Modules)
variable (e : SheafOfModules.free (R := (Spec (.of A)).ringCatSheaf) I ≅ M)
variable (ρ : (E ⊗[F] A) ≃ₗ[E] (Fin 3 → E))

/-- The constructed split-section isomorphism is the literal actual tensor
point evaluator, once the genuine coefficient-algebra formula is substituted. -/
theorem pointSplittingSectionTensorEquiv_eq_evaluator
    (hρ : ∀ a : A, ρ (1 ⊗ₜ[F] a) = fun k => α k a) :
    (pointSplittingSectionTensorEquiv α I M e ρ).toLinearMap =
    cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
      (Spec.map (CommRingCat.ofHom (algebraMap F A)))
      (fun k => Spec.map (CommRingCat.ofHom (α k).toRingHom))
      (fun k => pointSplitting_specPoint_over (α k)) M := by
  let g := cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
    (Spec.map (CommRingCat.ofHom (algebraMap F A)))
    (fun k => Spec.map (CommRingCat.ofHom (α k).toRingHom))
    (fun k => pointSplitting_specPoint_over (α k)) M
  let f := (pointSplittingSectionTensorEquiv α I M e ρ).toLinearMap
  change f = g
  apply LinearMap.ext
  intro w
  induction w using TensorProduct.induction_on with
  | zero => exact f.map_zero.trans g.map_zero.symm
  | add x y hx hy => rw [f.map_add, g.map_add, hx, hy]
  | tmul c s =>
    have hw : c ⊗ₜ[F] s = c • (1 ⊗ₜ[F] s) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hw]
    rw [f.map_smul, g.map_smul]
    exact congrArg (fun v => c • v)
      (pointSplittingSectionTensorEquiv_one_tmul α I M e ρ hρ s)

include I e in
/-- Bijectivity is proved for the actual evaluator rather than merely for
the coordinate model used in its construction. -/
theorem pointSplitting_actual_tensor_evaluator_bijective
    (hρ : ∀ a : A, ρ (1 ⊗ₜ[F] a) = fun k => α k a) :
    Function.Bijective
      (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
        (Spec.map (CommRingCat.ofHom (algebraMap F A)))
        (fun k => Spec.map (CommRingCat.ofHom (α k).toRingHom))
        (fun k => pointSplitting_specPoint_over (α k)) M) := by
  rw [← pointSplittingSectionTensorEquiv_eq_evaluator α I M e ρ hρ]
  exact (pointSplittingSectionTensorEquiv α I M e ρ).bijective

end PfaffianDescent
