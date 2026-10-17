import PfaffianDescent.SchemeModuleFinitePointSequenceBalance

/-! SOURCE ONLY / UNVERIFIED. Independent native exact/rank cut. Geometry
callers construct the actual short exact sequence, finite terms, actual
quotient H1 zero and genuine Euler change; no actual-component premise is
postulated here. This imports only accepted native primitives, not113. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u

/-- SAME actual native short exact sequence and real five-term linear
balance identify quotient H0 with the independently proved Euler change.
All actual base H0/H1 ranks cancel, without a constants=K assertion. -/
theorem schemeModuleShortExact_zeroQuotientHOne_topSections_finrank_eq_eulerChange
    {K : Type u} [Field K] {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (weight : ℤ) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) →
    Module.Finite K (schemeModuleCohomology.{u} X S.X₁ 1) →
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) →
    Subsingleton (schemeModuleCohomology.{u} X S.X₃ 1) →
    ((Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology.{u} X S.X₂ 1) =
      (Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology.{u} X S.X₁ 1) + weight) →
    (Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) : ℤ) = weight := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  intro h0 h1 hQ hv hchange
  have hbalance := (schemeModuleShortExact_finite_second_and_h0_h1_balance
    pi S hS h0 h1 hQ hv).2.2
  omega

end PfaffianDescent.Coray
