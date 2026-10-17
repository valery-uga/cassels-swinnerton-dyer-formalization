import PfaffianDescent.CorayNativeFiniteCoproductExt

/-! SOURCE ONLY / UNVERIFIED. Bounded native exact-sequence assembly for the
actual two kernels, with the already installed original base scalar action. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u

/-- Native two-kernel dimension shifting: finite middle H3 and zero middle
H2, with zero second-kernel H4, imply finite right H2. No finite H2 premise. -/
theorem nativeTwoKernelPresentation_cohomology_two_finite
    {K : Type u} [Field K] {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K))
    {F₀ F₁ J : X.Modules} (a : F₀ ⟶ J) (r : F₁ ⟶ F₀) (hz : r ≫ a = 0)
    (h₀ : (ShortComplex.mk (kernel.ι a) a (kernel.condition a)).ShortExact)
    (h₁ : (ShortComplex.mk (kernel.ι (kernel.lift a r hz))
      (kernel.lift a r hz) (kernel.condition (kernel.lift a r hz))).ShortExact) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Subsingleton (schemeModuleCohomology X (kernel (kernel.lift a r hz)) 4) →
      Module.Finite K (schemeModuleCohomology X F₁ 3) →
      Subsingleton (schemeModuleCohomology X F₀ 2) →
      Module.Finite K (schemeModuleCohomology X J 2) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  intro hH₄ hF₁ hF₀
  let b : F₁ ⟶ kernel a := kernel.lift a r hz
  let S₁ : ShortComplex X.Modules := ShortComplex.mk (kernel.ι b) b (kernel.condition b)
  let S₀ : ShortComplex X.Modules := ShortComplex.mk (kernel.ι a) a (kernel.condition a)
  letI : Subsingleton (schemeModuleCohomology X S₁.X₁ (3 + 1)) := hH₄
  have hS₁ : S₁.ShortExact := h₁
  have hkernel : Module.Finite K (schemeModuleCohomology X S₁.X₃ 3) :=
    schemeModuleRestriction_rightCohomology_finite_of_middle_finite_and_next_left_zero
      pi S₁ hS₁ 3 hF₁
  letI : Subsingleton (schemeModuleCohomology X S₀.X₂ 2) := hF₀
  have hS₀ : S₀.ShortExact := h₀
  exact schemeModuleRestriction_rightCohomology_finite_of_middle_zero_and_next_left_finite
    pi S₀ hS₀ 2 hkernel

end PfaffianDescent.Coray
