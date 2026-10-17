import PfaffianDescent.CubicClosedPointSerrePointSplittingSectionApply
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointSectionEvaluationThree

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u v w
set_option backward.isDefEq.respectTransparency false

def pointSplittingPiTranspose {E : Type u} {I : Type v} {J : Type w} [Field E] :
    (I → J → E) ≃ₗ[E] (J → I → E) where
  toFun v j i := v i j
  invFun v i j := v j i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The finite free affine section comparison constructed from an actual
split coefficient-algebra equivalence. Its compatibility is proved separately
against the literal evaluator; native applications derive the algebra split. -/
def pointSplittingSectionTensorEquiv
    {F A E : Type u} [Field F] [Field A] [Field E] [Algebra F A] [Algebra F E]
    (α : Fin 3 → (A →ₐ[F] E))
    (I : Type u) [Fintype I] [DecidableEq I]
    (M : (Spec (.of A)).Modules)
    (e : SheafOfModules.free (R := (Spec (.of A)).ringCatSheaf) I ≅ M)
    (ρ : (E ⊗[F] A) ≃ₗ[E] (Fin 3 → E)) :
    (E ⊗[F] SchemeModuleGlobalSectionsOver
      (Spec.map (CommRingCat.ofHom (algebraMap F A))) M) ≃ₗ[E]
    (∀ k : Fin 3, (moduleSpecΓFunctor (R := CommRingCat.of E)).obj
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (α k).toRingHom))).obj M)) :=
  (pointSplittingSpecSectionCoordinates (F := F) I M e).baseChange F E _ _ ≪≫ₗ
    tensorFinitePiLinearEquivOfFamily (fun _ : I => A) (fun _ : I => Fin 3 → E)
      (fun _ => ρ) ≪≫ₗ
    pointSplittingPiTranspose ≪≫ₗ
    (LinearEquiv.piCongrRight (fun k : Fin 3 => pointSplittingNativeSpecSectionCoordinates I
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (α k).toRingHom))).obj M)
      (pullbackFreeIso (Spec.map (CommRingCat.ofHom (α k).toRingHom)) I e))).symm

end PfaffianDescent
