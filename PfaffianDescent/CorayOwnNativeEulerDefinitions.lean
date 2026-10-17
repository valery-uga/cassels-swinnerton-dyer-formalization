import PfaffianDescent.CorayProjectiveIntersectionIntrinsicH1Finite
import PfaffianDescent.SchemeModuleOpenTopConnectingLinearExact
import PfaffianDescent.CorayOwnPositivePullbackCohomologyVanishing

/-! Actual original-field native Euler definitions and positive-zero Iso. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Native positive Euler characteristic with the SAME toBase-C actions. -/
def ownPositiveNativeEuler (C : HomogeneousIdeal PS)
    [HasExt.{u} (scheme C).Modules] (m : ℕ) : ℤ := by
  letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
  exact (Module.finrank K (SchemeModuleOpenSectionsOver (toBase C)
    (positiveSheafOfModules (grading C) m) ⊤) : ℤ) -
    Module.finrank K (schemeModuleCohomology (scheme C)
      (positiveSheafOfModules (grading C) m) 1)

/-- Native structure-sheaf Euler characteristic; its H0 rank is not set to 1. -/
def ownUnitNativeEuler (C : HomogeneousIdeal PS)
    [HasExt.{u} (scheme C).Modules] : ℤ := by
  letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
  let O : (scheme C).Modules := SheafOfModules.unit (scheme C).ringCatSheaf
  exact (Module.finrank K (SchemeModuleOpenSectionsOver (toBase C) O ⊤) : ℤ) -
    Module.finrank K (schemeModuleCohomology (scheme C) O 1)

/-- Actual positive-zero coefficient Iso preserves BOTH independently
existing toBase-C field actions on H0 and H1. -/
theorem ownPositiveNativeEuler_zero_eq_unit (C : HomogeneousIdeal PS)
    [HasExt.{u} (scheme C).Modules] :
    ownPositiveNativeEuler C 0 = ownUnitNativeEuler C := by
  letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
  let O : (scheme C).Modules := SheafOfModules.unit (scheme C).ringCatSheaf
  let e : positiveSheafOfModules (grading C) 0 ≅ O :=
    positiveZeroTwistIso (grading C) ≪≫ (unitIsoZeroTwist (grading C)).symm
  have h0 := (schemeModuleOpenTopIsoLinearEquivOver (toBase C) e).finrank_eq
  have h1 := (schemeModuleCohomologyIsoLinearEquivOver (toBase C) e 1).finrank_eq
  change ((Module.finrank K (SchemeModuleOpenSectionsOver (toBase C)
      (positiveSheafOfModules (grading C) 0) ⊤) : ℤ) -
      Module.finrank K (schemeModuleCohomology (scheme C)
        (positiveSheafOfModules (grading C) 0) 1)) =
    ((Module.finrank K (SchemeModuleOpenSectionsOver (toBase C) O ⊤) : ℤ) -
      Module.finrank K (schemeModuleCohomology (scheme C) O 1))
  rw [h0, h1]

end PfaffianDescent.Coray
