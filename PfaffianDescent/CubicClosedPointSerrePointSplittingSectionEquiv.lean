import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointSectionEvaluationAction
import PfaffianDescent.CubicClosedPointSerrePointSplittingCoordinates

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def pointSplittingSpecSectionCoordinates
    {F A : Type u} [Field F] [Field A] [Algebra F A]
    (I : Type u) [Fintype I] [DecidableEq I]
    (M : (Spec (.of A)).Modules)
    (e : SheafOfModules.free (R := (Spec (.of A)).ringCatSheaf) I ≅ M) :
    SchemeModuleGlobalSectionsOver (Spec.map (CommRingCat.ofHom (algebraMap F A))) M ≃ₗ[F]
      (I → A) := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap F A))
  letI := Module.compHom Γ(Spec (.of A), ⊤) (schemeOpenBaseRingHom p ⊤)
  exact schemeModuleGlobalSectionsLinearEquivOpenTop p M ≪≫ₗ
    moduleOpenTopLinearEquivOfFreeIsoOver p I M e ≪≫ₗ
    LinearEquiv.piCongrRight (fun _ => specGlobalFunctionsLinearEquiv F A)

/-- Actual native affine Gamma coordinates over its literal coefficient field. -/
def pointSplittingNativeSpecSectionCoordinates
    {E : Type u} [Field E]
    (I : Type u) [Fintype I] [DecidableEq I]
    (M : (Spec (.of E)).Modules)
    (e : SheafOfModules.free (R := (Spec (.of E)).ringCatSheaf) I ≅ M) :
    (moduleSpecΓFunctor (R := CommRingCat.of E)).obj M ≃ₗ[E] (I → E) :=
  (cubicClosedPointSerreSurfaceJetCotangent_pointNativeGammaOverLinearEquiv
    (Spec.map (CommRingCat.ofHom (algebraMap E E))) rfl M).symm ≪≫ₗ
      pointSplittingSpecSectionCoordinates (F := E) I M e

end PfaffianDescent
