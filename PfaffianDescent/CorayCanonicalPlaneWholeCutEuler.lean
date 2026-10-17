import PfaffianDescent.CorayProjectiveIntersectionIntrinsicH1Finite
import PfaffianDescent.CorayActualWholeCutPlaneCartier
import PfaffianDescent.FiniteProjectiveTwistQuotientCohomologyOne
import PfaffianDescent.SchemeIsoPushforwardUnit
import PfaffianDescent.ActualWholeIdealTwistEulerBalance229
import PfaffianDescent.PlaneCubicPositiveIntrinsicEuler
import PfaffianDescent.CubicClosedDegreeElevenPointSerreExtension

/-! SOURCE ONLY. The canonical Fin3 whole cut has the SAME rank and native
Euler action required by the actual coordinate-Hilbert consumer. No reduced
cut, coefficient/base-change certificate or numerical spectrum is assumed. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open ProjectiveNegativeTwist ProjectivePlaneNative
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Native finite-scheme rank is preserved by an actual source Iso. Both
field actions are constructed from their literal structural morphisms. -/
theorem finiteSchemeRank_comp_schemeIso_canonicalPlane001
    {X Y : Scheme.{u}} (pi : Y ⟶ Spec (.of K)) [IsFinite pi] (e : X ≅ Y) :
    finiteSchemeRank (e.hom ≫ pi) = finiteSchemeRank pi := by
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra pi
  have h := finitePushforwardUnit_topSections_finite_and_nativeRank pi e.hom
  let E := (schemeModuleOpenTopIsoLinearEquivOver pi
    (PfaffianDescent.schemeIsoPushforwardUnitIso e)).trans
      (finiteSchemeUnitTopCoefficientLinearEquiv pi)
  exact h.2.symm.trans (E.finrank_eq.trans
    (PfaffianDescent.finiteSchemeCoefficient_finrank pi))

/-- Original minimal-component geometry constructs the ENTIRE canonical
Fin3 cut's finite rank mu and every literal quotient's short exactness,
finite H0 of rank mu and zero H1. No quotient comparison is an input. -/
theorem selectedOriginalWholeCurve_canonicalPlane_quotient_nativeData001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    ∃ hpC : p ∈ C.toIdeal,
      let F := GenericHyperplaneField K
      let E := equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
      let X := scheme E
      let pi := toBase E
      let i := wholeGenericCutPlaneIdealImmersion C p hp hpC
      letI : HasExt.{u} X.Modules := schemeModules_hasExt X
      ∃ hfinite : IsFinite (toBase (wholeGenericCutPlaneIdeal C)),
        letI := hfinite
        finiteSchemeRank (toBase (wholeGenericCutPlaneIdeal C)) = actualCurveCoordinateHilbertDegree C ∧
        ∀ d : ℕ,
          let S := PfaffianDescent.closedImmersionIdealTwistSequence i
            (positiveSheafOfModules (grading E) d)
          S.ShortExact ∧
            Module.Finite F (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) ∧
            Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) =
              actualCurveCoordinateHilbertDegree C ∧
            Subsingleton (schemeModuleCohomology X S.X₃ 1) := by
  classical
  have hpC : p ∈ C.toIdeal := by
    apply hCmin.le
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (Set.mem_insert p {q})
  let F := GenericHyperplaneField K
  let E := equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
  let D := wholeGenericCutPlaneIdeal C
  let X := scheme E
  let pi := toBase E
  let i := wholeGenericCutPlaneIdealImmersion C p hp hpC
  letI : HasExt.{u} X.Modules := schemeModules_hasExt X
  obtain ⟨hOriginalFinite, hOriginalRank, _hOriginalCartier, _hOriginalGrades⟩ :=
    selectedOriginalWholeCurve_genericCut_finite_rank_degree p q hp hp0 n hq hnot C hCmin
  letI := hOriginalFinite
  have hFinite : IsFinite (toBase D) := by
    change IsFinite (toBase (wholeGenericCutPlaneIdeal C))
    rw [← wholeGenericCutPlaneSchemeIso_toBase C]
    infer_instance
  letI := hFinite
  have hRank : finiteSchemeRank (toBase D) = actualCurveCoordinateHilbertDegree C := by
    change finiteSchemeRank (toBase (wholeGenericCutPlaneIdeal C)) = actualCurveCoordinateHilbertDegree C
    simpa only [wholeGenericCutPlaneSchemeIso_toBase] using
      (finiteSchemeRank_comp_schemeIso_canonicalPlane001
        (toBase (wholeGenericCutIdeal C)) (wholeGenericCutPlaneSchemeIso C)).trans hOriginalRank
  have hbase : i ≫ pi = toBase D :=
    PfaffianDescent.schemeQuotientMap_toBase E D
      (genericPlaneCubic_ideal_le_wholeGenericCutPlaneIdeal C p hp hpC)
  letI : IsFinite (i ≫ pi) := hbase.symm ▸ hFinite
  letI : Infinite F := genericHyperplaneField_infinite
  have hRankSame : finiteSchemeRank (i ≫ pi) = actualCurveCoordinateHilbertDegree C := by
    simpa only [hbase] using hRank
  refine ⟨hpC, hFinite, hRank, ?_⟩
  dsimp only
  intro d
  have hQ := finiteProjectivePositiveTwistQuotient_topSections_finite_and_nativeRank E d i
  exact ⟨quotientPositiveTwist_closedImmersionIdealTwistSequence_shortExact E i d,
    hQ.1, hQ.2.trans hRankSame,
    finiteProjectivePositiveTwistQuotient_cohomology_one_subsingleton168 E d i⟩

/-- Native finite H0/H1 and Euler3d-mu for the literal CANONICAL Fin3
first ideal-twist term used by the accepted one-sided Hilbert consumer.
All original hypotheses/field/whole cut are retained; no spectrum premise. -/
theorem selectedOriginalWholeCurve_canonicalPlane_firstIdeal_finite_euler001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    ∃ hpC : p ∈ C.toIdeal,
      let F := GenericHyperplaneField K
      let E := equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
      let X := scheme E
      let pi := toBase E
      let i := wholeGenericCutPlaneIdealImmersion C p hp hpC
      letI : HasExt.{u} X.Modules := schemeModules_hasExt X
      letI : Linear F X.Modules := schemeModulesLinearOver pi
      ∀ d : ℕ, 1 ≤ d →
        let S := PfaffianDescent.closedImmersionIdealTwistSequence i
          (positiveSheafOfModules (grading E) d)
        Module.Finite F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) ∧
          Module.Finite F (schemeModuleCohomology X S.X₁ 1) ∧
          ((Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) : ℤ) -
            Module.finrank F (schemeModuleCohomology X S.X₁ 1) =
              3 * (d : ℤ) - (actualCurveCoordinateHilbertDegree C : ℤ)) := by
  classical
  obtain ⟨hpC, hFinite, _hRank, hQuotientData⟩ :=
    selectedOriginalWholeCurve_canonicalPlane_quotient_nativeData001 p q hp hp0 n hq hnot C hCmin
  let F := GenericHyperplaneField K
  let f := genericPlaneCubic p
  let hf := genericPlaneCubic_isHomogeneous p hp
  let E := equationIdeal f hf
  let X := scheme E
  let pi := toBase E
  let i := wholeGenericCutPlaneIdealImmersion C p hp hpC
  letI hXExt : HasExt.{u} X.Modules := schemeModules_hasExt X
  letI : HasExt.{u} (Proj (homogeneousSubmodule (Fin 3) F)).Modules := schemeModules_hasExt _
  letI : Linear F X.Modules := schemeModulesLinearOver pi
  letI : IsDomain (CoordinateRing E) := by
    change IsDomain (MvPolynomial (Fin 3) F ⧸ Ideal.span ({f} : Set _))
    exact (Ideal.Quotient.isDomain_iff_prime _).mpr
      (smoothCubic_actualGenericPlaneCubic_principalIdeal_prime p hp hp0)
  refine ⟨hpC, ?_⟩
  dsimp only
  intro d hd
  let S : ShortComplex X.Modules := PfaffianDescent.closedImmersionIdealTwistSequence i
    (positiveSheafOfModules (grading E) d)
  have hQ := hQuotientData d
  have hMiddle : Module.Finite F (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) ∧
      Module.Finite F (schemeModuleCohomology X S.X₂ 1) ∧
      ((Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) : ℤ) -
        Module.finrank F (schemeModuleCohomology X S.X₂ 1) = 3 * (d : ℤ)) := by
    let L : X.Modules := positiveSheafOfModules (grading E) d
    have hL := planeCubicPositiveIntrinsic_finite_euler_three_degree F f hf
      (genericPlaneCubic_ne_zero p hp hp0) d hd
    let e : S.X₂ ≅ L := schemeModuleTensorUnitLeftIso L
    let e0 := schemeModuleOpenTopIsoLinearEquivOver (K := F) (X := X) pi e
    let e1 := schemeModuleCohomologyIsoLinearEquivOver.{u} (K := F) (X := X) pi e 1
    letI : Module.Finite F (SchemeModuleOpenSectionsOver pi L ⊤) := hL.1
    letI : Module.Finite F (schemeModuleCohomology X L 1) := hL.2.1
    letI : Module.Finite F (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) :=
      Module.Finite.of_surjective e0.symm.toLinearMap e0.symm.surjective
    letI : Module.Finite F (schemeModuleCohomology X S.X₂ 1) :=
      Module.Finite.of_surjective e1.symm.toLinearMap e1.symm.surjective
    refine ⟨inferInstance, inferInstance, ?_⟩
    rw [e0.finrank_eq, e1.finrank_eq]
    exact hL.2.2
  exact @actualWholeIdealTwist_finite_euler_of_middle_three_degree229.{u}
    F (inferInstance : Field F) X hXExt pi S hQ.1 d (actualCurveCoordinateHilbertDegree C)
    hMiddle.1 hMiddle.2.1 hMiddle.2.2 hQ.2.1 hQ.2.2.1 hQ.2.2.2

end PfaffianDescent.Coray
