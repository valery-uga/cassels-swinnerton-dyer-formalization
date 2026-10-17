import PfaffianDescent.ActualP3IdealHomogeneousRestrictionKernel

/-! SOURCE ONLY / UNVERIFIED. Exact canonical ambient embedding formula
for the genuine H0 ideal-to-polynomial kernel equivalence. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The genuine H0 kernel dictionary has the actual original ideal
inclusion as its ambient global-section map. No map comparison premise. -/
theorem p3ClosedImmersionIdealHomogeneousKernelEquiv_embedding
    {Z : Scheme.{u}} (i : Z ⟶ Proj PS) [IsClosedImmersion i]
    (m : ℕ) (hm : 0 < m)
    (s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i (positiveSheafOfModules PS m))) :
    p3HomogeneousGlobalSectionLinearMap K m
      ((p3ClosedImmersionIdealHomogeneousKernelEquiv i m hm s).val) =
      s ≫ (closedImmersionIdealTwistSequence i (positiveSheafOfModules PS m)).f ≫
        (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS m)).hom := by
  let e := p3HomogeneousGlobalSectionsLinearEquiv K m hm
  change e (e.symm ((p3ClosedImmersionPositiveIdealGlobalKernelEquiv i m hm s).val)) = _
  rw [e.apply_symm_apply]
  rfl

end PfaffianDescent
