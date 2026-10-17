import PfaffianDescent.CorayLiteralModelPushforwardUnitGroundRank
import PfaffianDescent.CorayNativeShortExactHZeroUpperBound
import PfaffianDescent.CorayLiteralModelUnitMono
import PfaffianDescent.CorayClosedComponentIntrinsicH1Bound
import PfaffianDescent.CorayHomogeneousPrimeComponentGeometry
import PfaffianDescent.CubicClosedDegreeElevenPointSerreExtension

/-! SAME original prime and finite/GI coefficient model. Genuine native LES,
proper/GI constants, and coarse intrinsic H1 derive the global gluing bound.
No desired defect/rank/genus or normalization-quotient identification occurs. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K M : Type u} [Field K] [CharZero K] [Field M]
variable [Algebra K M] [Module.Finite K M]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Literal global unit-cokernel H0 has rank at most r+G_n−1. Full original
constants rank is retained until only its derived positivity is used.
The ENTIRE actual cokernel belongs to SAME coefficientComponentToOriginal. -/
theorem selectedOriginalPrime_actualCoefficientModel_globalGluingHZero_finite_finrank_le
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hI : I.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (D : HomogeneousIdeal (homogeneousSubmodule (Fin 4) M))
    (hDmin : D.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal.minimalPrimes)
    [GeometricallyIntegral (toBase D)] :
    let X := scheme I
    let pi := toBase I
    let f := coefficientComponentToOriginal I D hDmin.le
    let a := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
    let Q := cokernel (C := X.Modules) a
    letI : HasExt.{u} X.Modules := schemeModules_hasExt X
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.Finite K (SchemeModuleOpenSectionsOver pi Q ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver pi Q ⊤) ≤
        Module.finrank K M + 3 * n * (n - 1) / 2 := by
  classical
  letI : I.toIdeal.IsPrime := hI.isPrime
  have hIrel := selectedProjectiveMinimalComponent_homogeneous_relevant
    p q hp hp0 n hq hnot I hI
  let etaAmbient : ProjectiveSpectrum (homogeneousSubmodule (Fin 4) K) :=
    ⟨I, hI.isPrime, hIrel⟩
  obtain ⟨x, _hx⟩ :=
    (quotientProjMap_mem_range_iff I etaAmbient).mpr (le_refl I.toIdeal)
  let X := scheme I
  let pi := toBase I
  let f := coefficientComponentToOriginal I D hDmin.le
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let a := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let S := ShortComplex.cokernelSequence (C := X.Modules) a
  letI : IsIntegral X := homogeneousPrime_projectiveScheme_isIntegral I hI.isPrime x
  letI hNativeExt : HasExt.{u} X.Modules := schemeModules_hasExt X
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  have hS : S.ShortExact :=
    originalPrime_minimalCoefficientComponent_unitCokernelSequence_shortExact (K := K) (M := M) I hIrel D hDmin
  have hB := coefficientComponentToOriginal_pushforwardUnit_topSections_finite_finrank
    (K := K) (M := M) I D hDmin.le
  have hHOne := projectiveIntersection_closedComponent_unit_cohomology_one_finite_finrank_le
    p q hp hp0 n hn hq hnot I hI.le
  have hO := integralProper_originalGlobalFunctions_field_and_unitSectionsFinite pi
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi O ⊤) := hO.2
  letI : Nontrivial (SchemeModuleOpenSectionsOver pi O ⊤) := by
    change Nontrivial Γ(X, ⊤)
    infer_instance
  have hPositiveConstants : 0 < Module.finrank K (SchemeModuleOpenSectionsOver pi O ⊤) :=
    Module.finrank_pos
  have hUpper := @schemeModuleShortExact_finite_third_and_hZero_hOne_upperBound.{u}
    K inferInstance X hNativeExt pi S hS hB.1 hHOne.1
  refine ⟨hUpper.1, ?_⟩
  change Module.finrank K (SchemeModuleOpenSectionsOver pi (cokernel a) ⊤) ≤
    Module.finrank K M + 3 * n * (n - 1) / 2
  have hDimension := hUpper.2
  change Module.finrank K (SchemeModuleOpenSectionsOver pi (cokernel a) ⊤) +
      Module.finrank K (SchemeModuleOpenSectionsOver pi O ⊤) ≤
    Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) +
      Module.finrank K (schemeModuleCohomology X O 1) at hDimension
  have hMiddleRank : Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) =
      Module.finrank K M := hB.2
  have hGenus : Module.finrank K (schemeModuleCohomology X O 1) ≤
      1 + 3 * n * (n - 1) / 2 := hHOne.2
  rw [hMiddleRank] at hDimension
  omega

end PfaffianDescent.Coray
