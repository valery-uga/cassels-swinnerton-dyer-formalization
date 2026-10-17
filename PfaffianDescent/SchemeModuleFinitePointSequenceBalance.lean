import PfaffianDescent.FiniteFiveTermLinearRank

/-! Two orientations of the actual low-degree Ext sequence. These are
formal helpers: ShortExact, finite quotient H0 and vanishing quotient H1
are explicit here and are all derived by the geometric point callers.
Only H0-H1 is asserted; no higher-degree Euler or RR claim.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [HasExt.{u} X.Modules]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- With finite H0/H1 of the first coefficient and a quotient with finite H0
and zero H1, the second coefficient is finite and has the actual rank balance. -/
theorem schemeModuleShortExact_finite_second_and_h0_h1_balance
    (pi : X ⟶ Spec (CommRingCat.of K)) (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) →
    Module.Finite K (schemeModuleCohomology X S.X₁ 1) →
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) →
    Subsingleton (schemeModuleCohomology X S.X₃ 1) →
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) ∧
      Module.Finite K (schemeModuleCohomology X S.X₂ 1) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) +
          Module.finrank K (schemeModuleCohomology X S.X₁ 1) =
        Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) +
          Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) +
          Module.finrank K (schemeModuleCohomology X S.X₂ 1) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  intro h0 h1 hF hv
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) := h0
  letI : Module.Finite K (schemeModuleCohomology X S.X₁ 1) := h1
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) := hF
  letI : Subsingleton (schemeModuleCohomology X S.X₃ 1) := hv
  letI : Mono S.f := hS.mono_f
  have hex := schemeModuleOpenTopConnectingLinearMaps_exact pi S hS
  exact finiteFiveTermLinearRank
    (schemeModuleOpenTopCoefficientLinearMapOver pi S.f)
    (schemeModuleOpenTopCoefficientLinearMapOver pi S.g)
    (schemeModuleOpenTopConnectingLinearMapOver pi S hS)
    (schemeModuleCohomologyLinearMapOver pi S.f 1)
    (schemeModuleOpenTopCoefficientLinearMapOver_injective_of_mono pi S.f)
    (schemeModuleOpenTopCoefficientLinearMaps_exact pi S hS) hex.1 hex.2
    (schemeModuleCohomologyOneMap_surjective_of_quotient_subsingleton pi S hS)

/-- The reverse induction orientation: finite H0/H1 of the middle
coefficient proves finite H0/H1 of its actual kernel. In particular H1 of
the kernel is derived as an exact middle, rather than assumed finite. -/
theorem schemeModuleShortExact_finite_first_and_h0_h1_balance
    (pi : X ⟶ Spec (CommRingCat.of K)) (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) →
    Module.Finite K (schemeModuleCohomology X S.X₂ 1) →
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) →
    Subsingleton (schemeModuleCohomology X S.X₃ 1) →
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) ∧
      Module.Finite K (schemeModuleCohomology X S.X₁ 1) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) +
          Module.finrank K (schemeModuleCohomology X S.X₁ 1) =
        Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) +
          Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) +
          Module.finrank K (schemeModuleCohomology X S.X₂ 1) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  intro h0 h1 hF hv
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) := h0
  letI : Module.Finite K (schemeModuleCohomology X S.X₂ 1) := h1
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) := hF
  letI : Subsingleton (schemeModuleCohomology X S.X₃ 1) := hv
  letI : Mono S.f := hS.mono_f
  let f := schemeModuleOpenTopCoefficientLinearMapOver pi S.f
  let g := schemeModuleOpenTopCoefficientLinearMapOver pi S.g
  let b := schemeModuleOpenTopConnectingLinearMapOver pi S hS
  let j := schemeModuleCohomologyLinearMapOver pi S.f 1
  have hf : Function.Injective f := schemeModuleOpenTopCoefficientLinearMapOver_injective_of_mono pi S.f
  have hex := schemeModuleOpenTopConnectingLinearMaps_exact pi S hS
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) :=
    FiniteDimensional.of_injective f hf
  letI : Module.Finite K (schemeModuleCohomology X S.X₁ 1) :=
    moduleFinite_middle_of_exact b j hex.2
  have h := finiteFiveTermLinearRank f g b j hf
    (schemeModuleOpenTopCoefficientLinearMaps_exact pi S hS) hex.1 hex.2
    (schemeModuleCohomologyOneMap_surjective_of_quotient_subsingleton pi S hS)
  exact ⟨inferInstance, inferInstance, h.2.2⟩

end PfaffianDescent.Coray
