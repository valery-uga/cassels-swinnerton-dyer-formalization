import PfaffianDescent.FiniteSchemeUnitCohomologyOne
import PfaffianDescent.FiniteProjectiveTwistQuotientRank
import PfaffianDescent.SchemeModuleFinitePointSequenceBalance

/-! SOURCE ONLY / UNVERIFIED162. The entire finite closed-immersion ideal
has finite H0/H1 and Euler change minus its actual finite-scheme rank.
Geometric callers construct unit finiteness and rank internally. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory AllCharacteristics
universe u
variable {K : Type u} [Field K]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine entire-ideal Euler balance. Actual short exactness, finite
quotient rank and quotient H1 zero are all constructed inside the proof.
Only finite cohomology of the unit is a generic induction input. -/
theorem finiteClosedImmersionIdeal_finite_and_h0_h1_change
    {X Z : Scheme.{u}} (pi : X ⟶ Spec (.of K)) (i : Z ⟶ X)
    [IsClosedImmersion i] [IsFinite (i ≫ pi)] [HasExt.{u} X.Modules] :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.Finite K (SchemeModuleOpenSectionsOver pi
      (SheafOfModules.unit X.ringCatSheaf) ⊤) →
    Module.Finite K (schemeModuleCohomology X
      (SheafOfModules.unit X.ringCatSheaf) 1) →
    Module.Finite K (SchemeModuleOpenSectionsOver pi
      (IdealSheafDataModule.closedImmersionModule i) ⊤) ∧
      Module.Finite K (schemeModuleCohomology X
        (IdealSheafDataModule.closedImmersionModule i) 1) ∧
      ((Module.finrank K (SchemeModuleOpenSectionsOver pi
          (IdealSheafDataModule.closedImmersionModule i) ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology X
          (IdealSheafDataModule.closedImmersionModule i) 1) =
        (Module.finrank K (SchemeModuleOpenSectionsOver pi
          (SheafOfModules.unit X.ringCatSheaf) ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology X
          (SheafOfModules.unit X.ringCatSheaf) 1) - (finiteSchemeRank (i ≫ pi) : ℤ)) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  intro h0 h1
  let S := IdealSheafDataModule.closedImmersionModulePushforwardSequence i
  have hS := IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i
  have hQ := finitePushforwardUnit_topSections_finite_and_nativeRank pi i
  have hv : Subsingleton (schemeModuleCohomology X S.X₃ 1) :=
    finiteClosedImmersionUnitPushforward_cohomology_one_subsingleton pi i
  have h := schemeModuleShortExact_finite_first_and_h0_h1_balance pi S hS h0 h1 hQ.1 hv
  have hBalance :
      (Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) : ℤ) +
          Module.finrank K (schemeModuleCohomology X S.X₁ 1) =
        (Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) : ℤ) +
          Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) +
          Module.finrank K (schemeModuleCohomology X S.X₂ 1) := by
    exact_mod_cast h.2.2
  have hRank : (Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) : ℤ) =
      (finiteSchemeRank (i ≫ pi) : ℤ) := by exact_mod_cast hQ.2
  exact ⟨h.1, h.2.1, by
    change (Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology X S.X₁ 1) =
      (Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology X S.X₂ 1) - (finiteSchemeRank (i ≫ pi) : ℤ)
    omega⟩

end PfaffianDescent.Coray
