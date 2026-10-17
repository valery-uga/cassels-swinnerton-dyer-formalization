import PfaffianDescent.CorayNativeTwoKernelFiniteCohomology

/-! SOURCE ONLY / UNVERIFIED: abstract native two-short-exact-sequence cut. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u

theorem nativeShortExactPair_right_cohomology_two_finite
    {K : Type u} [Field K] {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K))
    (S₀ S₁ : ShortComplex X.Modules) (h₀ : S₀.ShortExact) (h₁ : S₁.ShortExact)
    (hlink : S₁.X₃ = S₀.X₁) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Subsingleton (schemeModuleCohomology X S₁.X₁ 4) →
      Module.Finite K (schemeModuleCohomology X S₁.X₂ 3) →
      Subsingleton (schemeModuleCohomology X S₀.X₂ 2) →
      Module.Finite K (schemeModuleCohomology X S₀.X₃ 2) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  intro hH₄ hF₁ hF₀
  letI : Subsingleton (schemeModuleCohomology X S₁.X₁ (3 + 1)) := hH₄
  have hmiddle : Module.Finite K (schemeModuleCohomology X S₁.X₃ 3) :=
    schemeModuleRestriction_rightCohomology_finite_of_middle_finite_and_next_left_zero
      pi S₁ h₁ 3 hF₁
  have hleft : Module.Finite K (schemeModuleCohomology X S₀.X₁ (2 + 1)) := by
    rw [← hlink]
    exact hmiddle
  letI : Subsingleton (schemeModuleCohomology X S₀.X₂ 2) := hF₀
  exact schemeModuleRestriction_rightCohomology_finite_of_middle_zero_and_next_left_finite
    pi S₀ h₀ 2 hleft

end PfaffianDescent.Coray
