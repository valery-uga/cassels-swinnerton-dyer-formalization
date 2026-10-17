import PfaffianDescent.FiniteFiveTermLinearRank

/-! Native gluing upper-bound primitive. This is a genuine low-degree LES
inequality, retaining the full first-term constants rank. It assumes neither
quotient H1-zero nor a desired gluing rank or genus bound. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K : Type u} [Field K]
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An exact four-term sequence derives finiteness of the third space and
its upper dimension balance, without assuming surjectivity onto the fourth. -/
theorem finiteFourTermLinearRankUpper
    {A B C D : Type u}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [Module K A] [Module K B] [Module K C] [Module K D]
    [Module.Finite K B] [Module.Finite K D]
    (f : A →ₗ[K] B) (g : B →ₗ[K] C) (h : C →ₗ[K] D)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hgh : Function.Exact g h) :
    Module.Finite K C ∧
      Module.finrank K C + Module.finrank K A ≤
        Module.finrank K B + Module.finrank K D := by
  letI : Module.Finite K A := FiniteDimensional.of_injective f hf
  letI : Module.Finite K C := moduleFinite_middle_of_exact g h hgh
  have hdimG := g.finrank_range_add_finrank_ker
  rw [hfg.linearMap_ker_eq, LinearMap.finrank_range_of_inj hf] at hdimG
  have hdimH := h.finrank_range_add_finrank_ker
  rw [hgh.linearMap_ker_eq] at hdimH
  have hRange : Module.finrank K (LinearMap.range h) ≤ Module.finrank K D :=
    Submodule.finrank_le _
  exact ⟨inferInstance, by omega⟩

/-- Actual native H0 maps and actual native connecting map give finite H0
of the SAME quotient and the upper inequality with full first-term H0.
The scalar action is the literal structural pi action throughout. -/
theorem schemeModuleShortExact_finite_third_and_hZero_hOne_upperBound
    {X : Scheme.{u}} [hExt : HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) →
    Module.Finite K (schemeModuleCohomology.{u} X S.X₁ 1) →
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) +
          Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) ≤
        Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) +
          Module.finrank K (schemeModuleCohomology.{u} X S.X₁ 1) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  intro hB hD
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) := hB
  letI : Module.Finite K (schemeModuleCohomology.{u} X S.X₁ 1) := hD
  letI : Mono S.f := hS.mono_f
  have hex := schemeModuleOpenTopConnectingLinearMaps_exact pi S hS
  exact finiteFourTermLinearRankUpper
    (schemeModuleOpenTopCoefficientLinearMapOver pi S.f)
    (schemeModuleOpenTopCoefficientLinearMapOver pi S.g)
    (schemeModuleOpenTopConnectingLinearMapOver pi S hS)
    (schemeModuleOpenTopCoefficientLinearMapOver_injective_of_mono pi S.f)
    (schemeModuleOpenTopCoefficientLinearMaps_exact pi S hS) hex.1

end PfaffianDescent.Coray
