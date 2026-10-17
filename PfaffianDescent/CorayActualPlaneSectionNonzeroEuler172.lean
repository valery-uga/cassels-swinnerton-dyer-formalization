import PfaffianDescent.PlaneCubicSectionCokernelZeroCycle172
import PfaffianDescent.CorayProperGeometricallyIntegralUnitSectionsRankOne
import PfaffianDescent.CorayActualGenericPlaneSectionH1Bound
import PfaffianDescent.SchemeModuleFinitePointSequenceBalance

/-! SOURCE ONLY172. A given nonzero section on the actual generic plane
cubic derives nonnegative Euler number and zero-Euler section rank <=1.
All unit ranks, cokernel geometry, finiteness and exactness are constructed.
No Euler formula for the coefficient or sharp section bound is input. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem rankBalance_nonnegativeEuler_zeroEuler_bound172
    (a b c d : ℕ) (hc : c ≤ 1) (hb : b ≤ c)
    (hBalance : a + c = 1 + d + b) :
    0 ≤ (a : ℤ) - b ∧ ((a : ℤ) - b = 0 → a ≤ 1) := by
  constructor
  · omega
  · intro hzero
    omega

private theorem shortExact_finite_nonnegativeEuler_zeroEuler_bound172
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) →
    Module.Finite K (schemeModuleCohomology X S.X₁ 1) →
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) →
    Subsingleton (schemeModuleCohomology X S.X₃ 1) →
    Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) = 1 →
    Module.finrank K (schemeModuleCohomology X S.X₁ 1) ≤ 1 →
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) ∧
      Module.Finite K (schemeModuleCohomology X S.X₂ 1) ∧
      0 ≤ (Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology X S.X₂ 1) ∧
      (((Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology X S.X₂ 1) = 0) →
        Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) ≤ 1) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  intro h0 h1 hQ0 hQ1 h0rank h1rank
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) := h0
  letI : Module.Finite K (schemeModuleCohomology X S.X₁ 1) := h1
  letI : Subsingleton (schemeModuleCohomology X S.X₃ 1) := hQ1
  have hBalanceData := schemeModuleShortExact_finite_second_and_h0_h1_balance
    pi S hS h0 h1 hQ0 hQ1
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) := hBalanceData.1
  letI : Module.Finite K (schemeModuleCohomology X S.X₂ 1) := hBalanceData.2.1
  have hSurj := schemeModuleCohomologyOneMap_surjective_of_quotient_subsingleton pi S hS
  have hle : Module.finrank K (schemeModuleCohomology X S.X₂ 1) ≤
      Module.finrank K (schemeModuleCohomology X S.X₁ 1) :=
    LinearMap.finrank_le_finrank_of_surjective hSurj
  have hBalance := hBalanceData.2.2
  rw [h0rank] at hBalance
  have hBounds := rankBalance_nonnegativeEuler_zeroEuler_bound172
    (Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤))
    (Module.finrank K (schemeModuleCohomology X S.X₂ 1))
    (Module.finrank K (schemeModuleCohomology X S.X₁ 1))
    (Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤))
    h1rank hle hBalance
  exact ⟨hBalanceData.1, hBalanceData.2.1, hBounds.1, hBounds.2⟩

private theorem smoothPlaneCubic_nonzeroSection_euler_bound_cut172
    (p : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (scheme (equationIdeal p hp))] :
    let I := equationIdeal p hp
    let X := scheme I
    let pi := toBase I
    let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules :=
      CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.Finite K (SchemeModuleOpenSectionsOver pi O ⊤) →
    Module.finrank K (SchemeModuleOpenSectionsOver pi O ⊤) = 1 →
    Module.Finite K (schemeModuleCohomology X O 1) →
    Module.finrank K (schemeModuleCohomology X O 1) ≤ 1 →
    ∀ (M : X.Modules), schemeModuleLocallyRankOne M →
      ∀ (s : M.val.obj (op ⊤)), s ≠ 0 →
        Module.Finite K (SchemeModuleOpenSectionsOver pi M ⊤) ∧
        Module.Finite K (schemeModuleCohomology X M 1) ∧
        0 ≤ (Module.finrank K (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
          Module.finrank K (schemeModuleCohomology X M 1) ∧
        (((Module.finrank K (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
          Module.finrank K (schemeModuleCohomology X M 1) = 0) →
          Module.finrank K (SchemeModuleOpenSectionsOver pi M ⊤) ≤ 1) := by
  classical
  let I := equationIdeal p hp
  let X := scheme I
  let pi := toBase I
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  dsimp only
  intro h0 h0rank h1 h1rank M hM s hs
  let φ := schemeModuleTopSectionHom M s
  let S : ShortComplex X.Modules := ShortComplex.cokernelSequence φ
  obtain ⟨U, hgU, ⟨eU⟩⟩ := hM (genericPoint X)
  have hS : S.ShortExact :=
    (schemeModuleTopSectionHom_mono_and_cokernelSequence_shortExact pi M hM U hgU eU s hs).2
  obtain ⟨_hC, _hc, hQ0, hQ1, _hDegree⟩ :=
    planeCubic_nonzeroRankOneSection_cokernel_zeroCycle_data172 p hp hp0 M hM s hs
  exact shortExact_finite_nonnegativeEuler_zeroEuler_bound172 pi S hS
    h0 h1 hQ0 hQ1 h0rank h1rank

/-- SAME actual rectangular generic plane section and original parameter
field. Nonzero sections force chi >=0; if chi=0, their whole section space
has dimension <=1. Neither chi=3d-m nor vanishing H1(M) is assumed. -/
theorem smoothCubic_actualPlane_nonzeroRankOneSection_finite_nonnegativeEuler_zeroEuler_rank_le_one172
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    let L := GenericHyperplaneField K
    let pE := PfaffianDescent.rectangularSubstitution
      (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K L))
    let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
      (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K L))
    let I := equationIdeal pE hpE
    let E := scheme I
    let pi := toBase I
    letI : EnoughInjectives E.Modules := sheafOfModules_enoughInjectives E.ringCatSheaf
    letI : HasExt.{u} E.Modules :=
      CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} E.Modules
    letI : Linear L E.Modules := schemeModulesLinearOver pi
    ∀ (M : E.Modules), schemeModuleLocallyRankOne M →
      ∀ (s : M.val.obj (op ⊤)), s ≠ 0 →
        Module.Finite L (SchemeModuleOpenSectionsOver pi M ⊤) ∧
        Module.Finite L (schemeModuleCohomology E M 1) ∧
        0 ≤ (Module.finrank L (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
          Module.finrank L (schemeModuleCohomology E M 1) ∧
        (((Module.finrank L (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
          Module.finrank L (schemeModuleCohomology E M 1) = 0) →
          Module.finrank L (SchemeModuleOpenSectionsOver pi M ⊤) ≤ 1) := by
  classical
  let L := GenericHyperplaneField K
  let pE := PfaffianDescent.rectangularSubstitution
    (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K L))
  let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
    (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K L))
  let I := equationIdeal pE hpE
  let E := scheme I
  let pi := toBase I
  letI : EnoughInjectives E.Modules := sheafOfModules_enoughInjectives E.ringCatSheaf
  letI : HasExt.{u} E.Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} E.Modules
  letI : Linear L E.Modules := schemeModulesLinearOver pi
  letI : IsIntegral E := smoothCubic_actualLinearGenericPlaneSection_isIntegral p hp hp0
  letI : Smooth (hypersurfaceToBase pE hpE) :=
    smoothCubic_actualLinearGenericPlaneSection_smooth p hp hp0
  have hpE0 : pE ≠ 0 := by
    change PfaffianDescent.rectangularSubstitution (genericPlaneInclusionMatrix (K := K))
      (p.map (algebraMap K L)) ≠ 0
    rw [genericPlaneInclusionMatrix_restrictedEquation]
    exact genericPlaneCubic_ne_zero p hp hp0
  have hbase0 := smoothCubic_actualLinearGenericPlaneSection_unitTopSections_finite_and_finrank_one
    p hp hp0
  have hbase1 := smoothCubic_actualLinearGenericPlaneSection_unit_cohomology_one_finite_finrank_le_one
    p hp hp0
  exact smoothPlaneCubic_nonzeroSection_euler_bound_cut172 (K := L) pE hpE hpE0
    hbase0.1 hbase0.2 hbase1.1 hbase1.2

end PfaffianDescent.Coray
