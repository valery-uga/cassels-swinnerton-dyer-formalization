import PfaffianDescent.ActualQuotientScalarExtensionUnitSurjective
import PfaffianDescent.AffineTildeActualPointClass

/- SOURCE ONLY / UNVERIFIED. Actual adjunction point classes generate the
WHOLE actual pullback Gamma module for a surjective affine ring map. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u

theorem actualAffineQuotientPointClass_surjective
    {R S : CommRingCat.{u}} (rho : R ⟶ S)
    (hquot : Function.Surjective rho.hom) (M : ModuleCat R) :
    Function.Surjective (affineTildeActualPointClass rho M) := by
  letI : Algebra R S := rho.hom.toAlgebra
  let E := affineTildeActualPointFiberEquiv rho M
  have hOne := actualQuotientScalarExtension_oneTensor_surjective (M := M) hquot
  intro w
  obtain ⟨m, hm⟩ := hOne (E w)
  refine ⟨m, E.injective ?_⟩
  rw [affineTildeActualPointFiberEquiv_pointClass]
  exact hm

end PfaffianDescent
