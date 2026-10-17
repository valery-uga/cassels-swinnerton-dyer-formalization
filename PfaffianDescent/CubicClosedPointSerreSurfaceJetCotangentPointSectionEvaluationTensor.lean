import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointSectionEvaluationMap
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointSectionEvaluationTensorBase

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

/-- E-linear scalar extension of the literal actual section evaluator. -/
def cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluationTensor
    {F E : Type u} [Field F] [Field E] [Algebra F E] {X : Scheme.{u}}
    (base : X ⟶ Spec (CommRingCat.of F)) (r : Spec (CommRingCat.of E) ⟶ X)
    (hr : r ≫ base = Spec.map (CommRingCat.ofHom (algebraMap F E))) (M : X.Modules) :
    E ⊗[F] SchemeModuleGlobalSectionsOver base M →ₗ[E]
      (moduleSpecΓFunctor (R := CommRingCat.of E)).obj ((Scheme.Modules.pullback r).obj M) :=
  cubicClosedPointSerreSurfaceJetCotangent_pointTensorLift _
    (cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation base r hr M)

/-- Pure tensors retain the literal actual pullback-section value. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluationTensor_tmul
    {F E : Type u} [Field F] [Field E] [Algebra F E] {X : Scheme.{u}}
    (base : X ⟶ Spec (CommRingCat.of F)) (r : Spec (CommRingCat.of E) ⟶ X)
    (hr : r ≫ base = Spec.map (CommRingCat.ofHom (algebraMap F E))) (M : X.Modules)
    (c : E) (s : SchemeModuleGlobalSectionsOver base M) :
    cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluationTensor base r hr M (c ⊗ₜ[F] s) =
      c • (show (moduleSpecΓFunctor (R := CommRingCat.of E)).obj
        ((Scheme.Modules.pullback r).obj M) from
        (pullbackSection r M (isIso_pullbackUnitComparison _) (M.unitHomEquiv s)).val (op ⊤)) := by
  change cubicClosedPointSerreSurfaceJetCotangent_pointTensorLift _
    (cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation base r hr M)
    (c ⊗ₜ[F] s) = _
  rw [
    cubicClosedPointSerreSurfaceJetCotangent_pointTensorLift_tmul,
    cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation_apply]

/-- In particular 1 tensor s is the actual native point restriction of s. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluationTensor_one_tmul
    {F E : Type u} [Field F] [Field E] [Algebra F E] {X : Scheme.{u}}
    (base : X ⟶ Spec (CommRingCat.of F)) (r : Spec (CommRingCat.of E) ⟶ X)
    (hr : r ≫ base = Spec.map (CommRingCat.ofHom (algebraMap F E))) (M : X.Modules)
    (s : SchemeModuleGlobalSectionsOver base M) :
    cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluationTensor base r hr M (1 ⊗ₜ[F] s) =
      (pullbackSection r M (isIso_pullbackUnitComparison _) (M.unitHomEquiv s)).val (op ⊤) := by
  rw [cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluationTensor_tmul, one_smul]

/-- The E-linear actual evaluator retains native projection naturality. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluationTensor_naturality
    {F E : Type u} [Field F] [Field E] [Algebra F E] {X : Scheme.{u}}
    (base : X ⟶ Spec (CommRingCat.of F)) (r : Spec (CommRingCat.of E) ⟶ X)
    (hr : r ≫ base = Spec.map (CommRingCat.ofHom (algebraMap F E)))
    {M N : X.Modules} (π : M ⟶ N) (w : E ⊗[F] SchemeModuleGlobalSectionsOver base M) :
    ((moduleSpecΓFunctor (R := CommRingCat.of E)).map ((Scheme.Modules.pullback r).map π)).hom
      (cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluationTensor base r hr M w) =
    cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluationTensor base r hr N
      ((schemeModuleGlobalSectionsMap base π).baseChange E w) :=
  cubicClosedPointSerreSurfaceJetCotangent_pointTensorLift_naturality _ _
    (cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation base r hr M)
    (cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation base r hr N)
    (schemeModuleGlobalSectionsMap base π)
    ((moduleSpecΓFunctor (R := CommRingCat.of E)).map ((Scheme.Modules.pullback r).map π)).hom
    (cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation_naturality base r hr π) w

end PfaffianDescent
