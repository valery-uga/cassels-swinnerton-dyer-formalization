import PfaffianDescent.CubicClosedPointSerrePointSplittingRestriction
import PfaffianDescent.CubicClosedPointSerrePointSplittingDescent

noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable {X D : Scheme.{u}} (base : X ⟶ Spec (.of F)) (d : D ⟶ X)
variable (δ : Fin 3 → (Spec (.of E) ⟶ D))
variable (hδ : ∀ k, δ k ≫ (d ≫ base) = Spec.map (CommRingCat.ofHom (algebraMap F E)))
variable (M : X.Modules)

/-- Actual pullback composition identifies the actual three point targets. -/
def pointSplittingRestrictionTripleFiberEquiv :
    (∀ k : Fin 3, (moduleSpecΓFunctor (R := CommRingCat.of E)).obj
      ((Scheme.Modules.pullback (δ k ≫ d)).obj M)) ≃ₗ[E]
    (∀ k : Fin 3, (moduleSpecΓFunctor (R := CommRingCat.of E)).obj
      ((Scheme.Modules.pullback (δ k)).obj ((Scheme.Modules.pullback d).obj M))) :=
  LinearEquiv.piCongrRight (fun k =>
    ((moduleSpecΓFunctor (R := CommRingCat.of E)).mapIso
      ((Scheme.Modules.pullbackComp (δ k) d).app M).symm).toLinearEquiv)

/-- The literal finite-support restriction commutes with scalar extension
and actual component evaluation, through native pullback composition. -/
theorem pointSplitting_restriction_tensor_square :
    (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
      (d ≫ base) δ hδ ((Scheme.Modules.pullback d).obj M)).comp
      ((cubicClosedPointSerreDegreeThreeEvaluationMap base d M).baseChange E) =
    (pointSplittingRestrictionTripleFiberEquiv d δ M).toLinearMap.comp
      (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
        base (fun k => δ k ≫ d) (fun k => by simpa only [Category.assoc] using hδ k) M) := by
  let f := (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
    (d ≫ base) δ hδ ((Scheme.Modules.pullback d).obj M)).comp
    ((cubicClosedPointSerreDegreeThreeEvaluationMap base d M).baseChange E)
  let g := (pointSplittingRestrictionTripleFiberEquiv d δ M).toLinearMap.comp
    (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
      base (fun k => δ k ≫ d) (fun k => by simpa only [Category.assoc] using hδ k) M)
  change f = g
  apply LinearMap.ext
  intro w
  induction w using TensorProduct.induction_on with
  | zero => exact f.map_zero.trans g.map_zero.symm
  | add x y hx hy => rw [f.map_add, g.map_add, hx, hy]
  | tmul c σ =>
    have hw : c ⊗ₜ[F] σ = c • (1 ⊗ₜ[F] σ) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hw, f.map_smul, g.map_smul]
    apply congrArg (fun v => c • v)
    dsimp only [f, g, LinearMap.comp_apply]
    rw [LinearMap.baseChange_tmul]
    rw [cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor_one_tmul,
      cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor_one_tmul]
    funext k
    have h := pointSplitting_restriction_component_evaluation base d (δ k) (hδ k) M σ
    rw [cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation_apply,
      cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation_apply] at h
    exact h.symm

/-- Actual split evaluation surjectivity descends to the original finite
support, provided its actual component evaluator is bijective. -/
theorem pointSplitting_actual_restriction_surjective_of_split
    (hfinite : Function.Bijective
      (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
        (d ≫ base) δ hδ ((Scheme.Modules.pullback d).obj M)))
    (hglobal : Function.Surjective
      (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
        base (fun k => δ k ≫ d) (fun k => by simpa only [Category.assoc] using hδ k) M)) :
    Function.Surjective (cubicClosedPointSerreDegreeThreeEvaluationMap base d M) := by
  apply pointSplitting_surjective_of_baseChange (E := E)
  intro y
  obtain ⟨x, hx⟩ := ((pointSplittingRestrictionTripleFiberEquiv d δ M).surjective.comp hglobal)
    (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
      (d ≫ base) δ hδ ((Scheme.Modules.pullback d).obj M) y)
  refine ⟨x, hfinite.1 ?_⟩
  exact (DFunLike.congr_fun (pointSplitting_restriction_tensor_square base d δ hδ M) x).trans hx

end PfaffianDescent
