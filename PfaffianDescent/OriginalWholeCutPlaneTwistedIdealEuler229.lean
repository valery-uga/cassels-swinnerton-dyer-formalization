import PfaffianDescent.ActualWholeIdealTwistEulerBalance229
import PfaffianDescent.PlaneCubicPositiveIntrinsicEuler
import PfaffianDescent.CorayActualWholeCutPlaneTwistedQuotientRank
import PfaffianDescent.CorayActualWholeCutPlaneTwistedQuotientCohomologyOne
import PfaffianDescent.CubicClosedDegreeElevenPointSerreExtension
import PfaffianDescent.CorayProjectiveIntersectionIntrinsicH1Finite

/-! ORIGINAL cubic/selected component inputs construct native finite H0/H1
and χ(I_Z(d))=3d−m for d≥1 on SAME actual generic-plane cubic. The ENTIRE
original cut Z and its actual ideal-twist sequence remain unchanged. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open ProjectiveNegativeTwist ProjectivePlaneNative
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- ORIGINAL inputs derive the exact manuscript Euler number of the SAME
whole cut ideal tensor O_E(d), with original parameter-field scalar action.
No middle/quotient rank, acyclicity, finiteness or Euler certificate is an input. -/
theorem selectedOriginalWholeCurve_sameE_wholeTwistedIdeal_positiveDegrees_finite_euler229
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    ∃ hpC : p ∈ C.toIdeal,
      let F := GenericHyperplaneField K
      let pE := PfaffianDescent.rectangularSubstitution
        (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K F))
      let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
        (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K F))
      let I := equationIdeal pE hpE
      let X := scheme I
      let pi := hypersurfaceToBase pE hpE
      letI : HasExt.{u} X.Modules := schemeModules_hasExt X
      letI : Linear F X.Modules := schemeModulesLinearOver pi
      let i := wholeGenericCutPlaneImmersion C p hp hpC
      ∀ d : ℕ, 1 ≤ d →
        let S := PfaffianDescent.closedImmersionIdealTwistSequence i
          (positiveSheafOfModules (grading I) d)
        Module.Finite F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) ∧
          Module.Finite F (schemeModuleCohomology X S.X₁ 1) ∧
          ((Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) : ℤ) -
            Module.finrank F (schemeModuleCohomology X S.X₁ 1) =
              3 * (d : ℤ) - (actualCurveCoordinateHilbertDegree C : ℤ)) := by
  classical
  have hpC : p ∈ C.toIdeal := by
    apply hCmin.le
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (by simp)
  let F := GenericHyperplaneField K
  let pE := PfaffianDescent.rectangularSubstitution
    (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K F))
  let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
    (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K F))
  let I := equationIdeal pE hpE
  let X := scheme I
  let pi := hypersurfaceToBase pE hpE
  let i := wholeGenericCutPlaneImmersion C p hp hpC
  letI hXExt : HasExt.{u} X.Modules := schemeModules_hasExt X
  letI : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 3) F)).Modules :=
    schemeModules_hasExt _
  letI : Linear F X.Modules := schemeModulesLinearOver pi
  have hpE0 : pE ≠ 0 := by
    change PfaffianDescent.rectangularSubstitution (genericPlaneInclusionMatrix (K := K))
      (p.map (algebraMap K F)) ≠ 0
    rw [genericPlaneInclusionMatrix_restrictedEquation]
    exact genericPlaneCubic_ne_zero p hp hp0
  have hPrime : (Ideal.span ({pE} : Set (MvPolynomial (Fin 3) F))).IsPrime := by
    change (Ideal.span ({PfaffianDescent.rectangularSubstitution
      (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K F))} :
        Set (MvPolynomial (Fin 3) F))).IsPrime
    rw [genericPlaneInclusionMatrix_restrictedEquation]
    exact smoothCubic_actualGenericPlaneCubic_principalIdeal_prime p hp hp0
  letI : IsDomain (CoordinateRing I) := by
    change IsDomain (MvPolynomial (Fin 3) F ⧸ Ideal.span ({pE} : Set _))
    exact (Ideal.Quotient.isDomain_iff_prime _).mpr hPrime
  obtain ⟨hpC0, hQuotientData⟩ :=
    selectedOriginalWholeCurve_sameE_twistedIdealQuotient_allDegrees_finite_rank_and_shortExact
      p q hp hp0 n hq hnot C hCmin
  obtain ⟨hpC1, hQuotientOne⟩ :=
    selectedOriginalWholeCurve_sameE_twistedIdealQuotient_allDegrees_cohomology_one_subsingleton168
      p q hp hp0 n hq hnot C hCmin
  refine ⟨hpC, ?_⟩
  dsimp only
  intro d hd
  let S := PfaffianDescent.closedImmersionIdealTwistSequence i
    (positiveSheafOfModules (grading I) d)
  have hS : S.ShortExact := (hQuotientData d).1
  have hQ0 : Module.Finite F (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) :=
    (hQuotientData d).2.1
  have hQRank : Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) =
      actualCurveCoordinateHilbertDegree C := (hQuotientData d).2.2
  have hQ1 : Subsingleton (schemeModuleCohomology X S.X₃ 1) := hQuotientOne d
  have hMiddle :
      Module.Finite F (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) ∧
      Module.Finite F (schemeModuleCohomology X S.X₂ 1) ∧
      ((Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) : ℤ) -
        Module.finrank F (schemeModuleCohomology X S.X₂ 1) = 3 * (d : ℤ)) := by
    let L : X.Modules := positiveSheafOfModules (grading I) d
    have hL := planeCubicPositiveIntrinsic_finite_euler_three_degree
      F pE hpE hpE0 d hd
    let e : S.X₂ ≅ L := schemeModuleTensorUnitLeftIso L
    let e₀ := schemeModuleOpenTopIsoLinearEquivOver (K := F) (X := X) pi e
    let e₁ := schemeModuleCohomologyIsoLinearEquivOver.{u}
      (K := F) (X := X) pi e 1
    letI : Module.Finite F (SchemeModuleOpenSectionsOver pi L ⊤) := hL.1
    letI : Module.Finite F (schemeModuleCohomology X L 1) := hL.2.1
    letI : Module.Finite F (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) :=
      Module.Finite.of_surjective e₀.symm.toLinearMap e₀.symm.surjective
    letI : Module.Finite F (schemeModuleCohomology X S.X₂ 1) :=
      Module.Finite.of_surjective e₁.symm.toLinearMap e₁.symm.surjective
    refine ⟨inferInstance, inferInstance, ?_⟩
    rw [e₀.finrank_eq, e₁.finrank_eq]
    exact hL.2.2
  exact @actualWholeIdealTwist_finite_euler_of_middle_three_degree229.{u}
    F (inferInstance : Field F) X hXExt
    pi S hS d (actualCurveCoordinateHilbertDegree C)
    hMiddle.1 hMiddle.2.1 hMiddle.2.2 hQ0 hQRank hQ1

end PfaffianDescent.Coray
