import PfaffianDescent.ActualAmbientPositiveTwistQuotientIso
import PfaffianDescent.CorayOwnPositivePullbackCohomologyVanishing
import PfaffianDescent.SchemeModuleOpenTopConnectingLinearExact

/-! Literal intrinsic OWN positive coefficient H1 from actual pullback vanishing. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K
set_option autoImplicit false

/-- Eventual H1 vanishing of the SAME quotient grading's actual positive
coefficient. Ambient HasExt and actual pullback/quotient Iso are constructed. -/
theorem homogeneousIdeal_eventually_actualOwnPositive_cohomology_one_subsingleton001
    (C : HomogeneousIdeal PS) [HasExt.{u} (scheme C).Modules] :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
      Subsingleton (schemeModuleCohomology (scheme C)
        (positiveSheafOfModules (grading C) m) 1) := by
  letI : EnoughInjectives (Proj PS).Modules :=
    sheafOfModules_enoughInjectives (Proj PS).ringCatSheaf
  letI : HasExt.{u} (Proj PS).Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} (Proj PS).Modules
  obtain ⟨B, hB⟩ := homogeneousIdeal_eventually_ownPositivePullback_cohomology_one_subsingleton C
  refine ⟨B, fun m hm => ?_⟩
  letI := hB m hm
  exact schemeModuleCohomology_subsingleton_of_iso (scheme C)
    (actualAmbientPositiveTwistQuotientIso C m) 1

end PfaffianDescent.Coray
