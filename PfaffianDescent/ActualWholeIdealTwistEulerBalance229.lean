import PfaffianDescent.SchemeModuleFinitePointSequenceBalance

/-! Bounded original-action arithmetic assembly of native finite H0/H1.
The middle Euler and quotient rank are explicit intermediate inputs; the
original geometric caller constructs both from actual native producers. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [HasExt.{u} X.Modules]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Exact native finite balance gives the actual kernel Euler number3d−m.
The original structure morphism pi supplies every scalar action. -/
theorem actualWholeIdealTwist_finite_euler_of_middle_three_degree229
    (pi : X ⟶ Spec (.of K)) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (d m : ℕ) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) →
    Module.Finite K (schemeModuleCohomology X S.X₂ 1) →
    (Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) : ℤ) -
      Module.finrank K (schemeModuleCohomology X S.X₂ 1) = 3 * (d : ℤ) →
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) →
    Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) = m →
    Subsingleton (schemeModuleCohomology X S.X₃ 1) →
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) ∧
      Module.Finite K (schemeModuleCohomology X S.X₁ 1) ∧
      ((Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology X S.X₁ 1) =
          3 * (d : ℤ) - (m : ℤ)) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  intro hMiddle0 hMiddle1 hMiddleEuler hQuotient0 hQuotientRank hQuotient1
  have h := schemeModuleShortExact_finite_first_and_h0_h1_balance
    pi S hS hMiddle0 hMiddle1 hQuotient0 hQuotient1
  refine ⟨h.1, h.2.1, ?_⟩
  have hBalance := h.2.2
  rw [hQuotientRank] at hBalance
  omega

end PfaffianDescent.Coray
