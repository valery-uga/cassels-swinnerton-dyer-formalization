import PfaffianDescent.CorayProjectiveIntersectionGlobalConstants
import PfaffianDescent.CorayNormalizationGlobalUnitSectionsFinite
import PfaffianDescent.CorayProjectiveNormalizationIntrinsicH1Finite
import PfaffianDescent.SchemeModuleUnitHomGroundSections
import PfaffianDescent.SchemeModuleSupportedFiberGroundDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Actual normalization base H0 rank and H0-minus-H1 over the ORIGINAL K.
The full canonical global projection image is retained and cancels only in
the Euler arithmetic. No H0(normalization)=K or genus/section certificate.
SOURCE ONLY / UNVERIFIED; root owns all compiler and acceptance checks. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual Hom is left exact on a genuine short exact complex. The first
coefficient is not assumed projective, and Hom is not asserted surjective
onto the third coefficient. -/
private theorem hom_first_two_maps_exact
    {C : Type*} [Category C] [Abelian C] [Linear K C]
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

/-- Finite middle-term rank-nullity retains the actual last-map range. -/
private theorem injective_exact_middle_finrank
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C]
    [Module.Finite K A] [Module.Finite K B]
    (f : A →ₗ[K] B) (g : B →ₗ[K] C)
    (hf : Function.Injective f) (hex : Function.Exact f g) :
    Module.finrank K B = Module.finrank K A + Module.finrank K (LinearMap.range g) := by
  have hdim := g.finrank_range_add_finrank_ker
  rw [hex.linearMap_ker_eq, LinearMap.finrank_range_of_inj hf] at hdim
  exact hdim.symm.trans (Nat.add_comm _ _)

/-- The actual normalization constants have dimension one PLUS the full
image of the actual canonical global projection. Original-curve constants,
normalization H0 finiteness, monicity and exactness are derived internally. -/
theorem projectiveIntersection_genericNormalization_unit_topSections_finrank_eq_one_add_globalProjectionImage
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    let pi := toBase I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    let σ := genericNormalizationHomQuotientLinearMap X pi
    Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
      (SheafOfModules.unit N.ringCatSheaf) ⊤) =
        1 + Module.finrank K (LinearMap.range σ) := by
  intro I X pi N ν σ
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let ON : N.Modules := SheafOfModules.unit N.ringCatSheaf
  let P : X.Modules := (Scheme.Modules.pushforward ν).obj ON
  let S := ShortComplex.cokernelSequence (genericNormalizationUnitToPushforwardUnit X)
  have hS : S.ShortExact := genericNormalization_cokernelSequence_shortExact X
  let E := (schemeModuleUnitHomGroundLinearEquivOpenTop pi P).trans
    (schemeModulePushforward_topSectionsLinearEquiv pi ν ON)
  let F := (projectiveIntersection_globalFunctionsLinearEquiv_native p q hp hp0 n hn hq hnot).trans
    (schemeModuleUnitHomGroundLinearEquivOpenTop pi OX).symm
  letI : Module.Finite K (SchemeModuleOpenSectionsOver (ν ≫ pi) ON ⊤) :=
    projectiveIntersection_genericNormalization_unit_topSections_finite_native
      p q hp hp0 n hn hq hnot
  letI hPFinite : Module.Finite K (OX ⟶ P) := Module.Finite.equiv E.symm
  letI hOXFinite : Module.Finite K (OX ⟶ OX) := Module.Finite.equiv F
  letI : Module.Finite K (OX ⟶ S.X₁) := hOXFinite
  letI : Module.Finite K (OX ⟶ S.X₂) := hPFinite
  let ρ := CategoryTheory.Linear.rightComp K OX S.f
  letI : Mono S.f := hS.mono_f
  have hρ : Function.Injective ρ := by
    intro a b hab
    exact (cancel_mono S.f).mp hab
  have hdim := injective_exact_middle_finrank ρ σ hρ (by
    change Function.Exact (CategoryTheory.Linear.rightComp K OX S.f)
      (CategoryTheory.Linear.rightComp K OX S.g)
    exact hom_first_two_maps_exact OX S hS)
  have hOX : Module.finrank K (OX ⟶ OX) = 1 :=
    F.finrank_eq.symm.trans (CommSemiring.finrank_self K)
  calc
    Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi) ON ⊤) =
        Module.finrank K (OX ⟶ P) := E.finrank_eq.symm
    _ = Module.finrank K (OX ⟶ OX) + Module.finrank K (LinearMap.range σ) := hdim
    _ = 1 + Module.finrank K (LinearMap.range σ) :=
      congrArg (fun a : ℕ => a + Module.finrank K (LinearMap.range σ)) hOX

/-- The normalization base Euler number follows from the two actual full
image identities. The normalization constants are retained, never replaced
by K; the common global projection-image dimension cancels algebraically. -/
theorem projectiveIntersection_genericNormalization_unit_baseEuler_eq_curveH1_and_quotient
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    let pi := toBase I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
    (Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
        (SheafOfModules.unit N.ringCatSheaf) ⊤) : ℤ) -
        (Module.finrank K (schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1) : ℤ) =
      1 - (Module.finrank K (schemeModuleCohomology X (SheafOfModules.unit X.ringCatSheaf) 1) : ℤ) +
        (Module.finrank K (SchemeModuleGlobalSectionsOver pi (genericNormalizationQuotientSheaf X)) : ℤ) := by
  intro I X pi N ν
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
  have h0 := projectiveIntersection_genericNormalization_unit_topSections_finrank_eq_one_add_globalProjectionImage
    p q hp hp0 n hn hq hnot
  have h1 := projectiveIntersection_genericNormalization_cohomology_one_finrank_with_globalProjectionImage
    p q hp hp0 n hq hnot
  have hQ := (schemeModuleUnitHomGroundLinearEquivGlobalSections pi
    (genericNormalizationQuotientSheaf X)).finrank_eq
  dsimp only [I, X, pi, N, ν] at h0 h1 hQ ⊢
  omega

end PfaffianDescent.Coray
