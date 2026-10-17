import PfaffianDescent.CorayPerfectOwnNormalizationConstantsTower
import PfaffianDescent.CorayGenericNormalizationLowDegreeLinearExact
import PfaffianDescent.SchemeModuleUnitHomGroundSections
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Original perfect-K normalization H0 rank retains BOTH full constants
fields and SAME canonical projection image. No H0=K, H1, genus, geometric
integrality, or vanishing hypothesis. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace
universe u

private theorem fullConstants_hom_first_two_maps_exact
    {K : Type u} [Field K] {C : Type*} [Category C] [Abelian C] [Linear K C]
    (O : C) (S : ShortComplex C) (hS : S.ShortExact) :
    Function.Exact (CategoryTheory.Linear.rightComp K O S.f)
      (CategoryTheory.Linear.rightComp K O S.g) := by
  intro z
  change z ≫ S.g = 0 ↔ ∃ s, s ≫ S.f = z
  constructor
  · intro hz
    let t := KernelFork.IsLimit.lift' hS.fIsKernel z hz
    exact ⟨t.1, t.2⟩
  · rintro ⟨s, rfl⟩
    rw [Category.assoc, S.zero, comp_zero]

private theorem fullConstants_injective_exact_middle_finrank
    {K : Type u} [Field K] {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C]
    [Module.Finite K A] [Module.Finite K B]
    (f : A →ₗ[K] B) (g : B →ₗ[K] C)
    (hf : Function.Injective f) (hex : Function.Exact f g) :
    Module.finrank K B = Module.finrank K A + Module.finrank K (LinearMap.range g) := by
  have hdim := g.finrank_range_add_finrank_ker
  rw [hex.linearMap_ker_eq, LinearMap.finrank_range_of_inj hf] at hdim
  exact hdim.symm.trans (Nat.add_comm _ _)

/-- The SAME original-K normalization H0 rank is original curve H0 rank
plus the full image of its actual canonical quotient projection. Both H0
finiteness inputs are internally derived from properness and genuine finite
normalization over perfect K; no constants-rank equality is a premise. -/
theorem perfectField_integralProper_genericNormalization_unit_topSections_finrank_eq_curveRank_add_globalProjectionImage
    {K : Type u} [Field K] [PerfectField K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [IsProper pi] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    let σ := genericNormalizationHomQuotientLinearMap X pi
    Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
      (show N.Modules from SheafOfModules.unit N.ringCatSheaf) ⊤) =
      Module.finrank K (SchemeModuleOpenSectionsOver pi
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⊤) +
        Module.finrank K (LinearMap.range σ) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  let σ := genericNormalizationHomQuotientLinearMap X pi
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let ON : N.Modules := SheafOfModules.unit N.ringCatSheaf
  let P : X.Modules := (Scheme.Modules.pushforward ν).obj ON
  let S : ShortComplex X.Modules :=
    ShortComplex.cokernelSequence (genericNormalizationUnitToPushforwardUnit X)
  have hS : S.ShortExact := genericNormalization_cokernelSequence_shortExact X
  let E := (schemeModuleUnitHomGroundLinearEquivOpenTop pi P).trans
    (schemeModulePushforward_topSectionsLinearEquiv pi ν ON)
  let F := schemeModuleUnitHomGroundLinearEquivOpenTop pi OX
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi OX ⊤) :=
    (integralProper_originalGlobalFunctions_field_and_unitSectionsFinite pi).2
  letI : Module.Finite K (SchemeModuleOpenSectionsOver (ν ≫ pi) ON ⊤) :=
    (perfectField_integralProper_genericNormalization_originalConstants_finite_and_finrank_dvd X pi).2.2.1
  letI hPFinite : Module.Finite K (OX ⟶ P) := Module.Finite.equiv E.symm
  letI hOXFinite : Module.Finite K (OX ⟶ OX) := Module.Finite.equiv F.symm
  letI : Module.Finite K (OX ⟶ S.X₁) := hOXFinite
  letI : Module.Finite K (OX ⟶ S.X₂) := hPFinite
  let ρ := CategoryTheory.Linear.rightComp K OX S.f
  letI : Mono S.f := hS.mono_f
  have hρ : Function.Injective ρ := by
    intro a b hab
    exact (cancel_mono S.f).mp hab
  have hdim := fullConstants_injective_exact_middle_finrank ρ σ hρ (by
    change Function.Exact (CategoryTheory.Linear.rightComp K OX S.f)
      (CategoryTheory.Linear.rightComp K OX S.g)
    exact fullConstants_hom_first_two_maps_exact OX S hS)
  calc
    Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi) ON ⊤) =
        Module.finrank K (OX ⟶ P) := E.finrank_eq.symm
    _ = Module.finrank K (OX ⟶ OX) + Module.finrank K (LinearMap.range σ) := hdim
    _ = Module.finrank K (SchemeModuleOpenSectionsOver pi OX ⊤) +
        Module.finrank K (LinearMap.range σ) :=
      congrArg (fun a : ℕ => a + Module.finrank K (LinearMap.range σ)) F.finrank_eq

end PfaffianDescent.Coray
