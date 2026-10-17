import PfaffianDescent.OriginalRectangularPlaneNonpositiveEulerCasesBeyond230
import PfaffianDescent.CorayCanonicalPlaneWholeCutEuler
import PfaffianDescent.CorayCanonicalPlaneWholeFirstIdealRankOne
import PfaffianDescent.CorayOriginalWholePlaneIdealNativeHZeroInjection

/-! Genuine remaining canonical d<lambda and d=lambda coefficient windows. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def planeCubicNonpositiveNativeSectionRanksProperty
    {F : Type u} [Field F] (f : MvPolynomial (Fin 3) F) (hf : f.IsHomogeneous 3) : Prop :=
    let E := equationIdeal f hf
    let X := scheme E
    let pi := toBase E
    letI : HasExt.{u} X.Modules := schemeModules_hasExt X
    letI : Linear F X.Modules := schemeModulesLinearOver pi
    ∀ M : X.Modules, schemeModuleLocallyRankOne M →
      (((Module.finrank F (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
        Module.finrank F (schemeModuleCohomology X M 1) < 0) →
          Subsingleton (SchemeModuleOpenSectionsOver pi M ⊤)) ∧
      (((Module.finrank F (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
        Module.finrank F (schemeModuleCohomology X M 1) = 0) →
          Module.finrank F (SchemeModuleOpenSectionsOver pi M ⊤) ≤ 1)

private theorem planeCubicEquation_nonpositiveNativeRanks_transport
    {F : Type u} [Field F] (f g : MvPolynomial (Fin 3) F)
    (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 3) (hfg : f = g) :
    planeCubicNonpositiveNativeSectionRanksProperty f hf →
      planeCubicNonpositiveNativeSectionRanksProperty g hg := by
  subst g
  exact fun h => h

/-- The ENTIRE native coefficient/base-action statement moves along the
literal equation equality. No H0/H1/rank conclusion is supplied as an input. -/
theorem smoothCubic_canonicalPlane_nonpositiveNativeSectionRanks001
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    planeCubicNonpositiveNativeSectionRanksProperty
      (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp) := by
  let F := GenericHyperplaneField K
  let f := PfaffianDescent.rectangularSubstitution
    (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K F))
  let hf := PfaffianDescent.rectangularSubstitution_homogeneous
    (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K F))
  have hRect : planeCubicNonpositiveNativeSectionRanksProperty f hf := by
    dsimp only [planeCubicNonpositiveNativeSectionRanksProperty]
    intro M hM
    exact ⟨smoothCubic_actualPlane_negativeEuler_topSections_subsingleton_beyond230
      p hp hp0 M hM,
      smoothCubic_actualPlane_zeroEuler_topSections_finrank_le_one_beyond230
        p hp hp0 M hM⟩
  have hEquation : f = genericPlaneCubic p := genericPlaneInclusionMatrix_restrictedEquation p
  exact planeCubicEquation_nonpositiveNativeRanks_transport f (genericPlaneCubic p)
    hf (genericPlaneCubic_isHomogeneous p hp) hEquation hRect

/-- Degree mu=3lambda constructs both remaining positive-degree windows:
below lambda all ideal sections vanish; at lambda the whole native H0 and
literal coordinate-ideal grade have rank at most one. No outcome premise. -/
theorem selectedOriginalWholeCurve_canonicalPlane_lowDegree_nativeHZero_and_idealGrade001
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
      ∀ lambda : ℕ, actualCurveCoordinateHilbertDegree C = 3 * lambda →
        ∀ d : ℕ, 1 ≤ d →
          let S := PfaffianDescent.closedImmersionIdealTwistSequence i
            (positiveSheafOfModules (grading E) d)
          ((d < lambda) → Subsingleton (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) ∧
            Module.finrank F (wholeIdealGrade (grading E)
              (wholeOriginalPlaneCutCoordinateIdeal C p hp) d) = 0) ∧
          ((d = lambda) → Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) ≤ 1 ∧
            Module.finrank F (wholeIdealGrade (grading E)
              (wholeOriginalPlaneCutCoordinateIdeal C p hp) d) ≤ 1) := by
  classical
  obtain ⟨hpC, hEulerData⟩ := selectedOriginalWholeCurve_canonicalPlane_firstIdeal_finite_euler001
    p q hp hp0 n hq hnot C hCmin
  obtain ⟨hpC', hRankOne⟩ :=
    selectedOriginalWholeCurve_canonicalPlane_firstIdeal_allDegrees_locallyRankOne001
      p q hp hp0 n hq hnot C hCmin
  let F := GenericHyperplaneField K
  let E := equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
  let X := scheme E
  let pi := toBase E
  let i := wholeGenericCutPlaneIdealImmersion C p hp hpC
  letI : HasExt.{u} X.Modules := schemeModules_hasExt X
  letI : Linear F X.Modules := schemeModulesLinearOver pi
  refine ⟨hpC, ?_⟩
  dsimp only
  intro lambda hMu d hd
  let S : ShortComplex X.Modules := PfaffianDescent.closedImmersionIdealTwistSequence i
    (positiveSheafOfModules (grading E) d)
  have hData := hEulerData d hd
  letI : Module.Finite F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) := hData.1
  have hM : schemeModuleLocallyRankOne S.X₁ := hRankOne d
  have hProperty := smoothCubic_canonicalPlane_nonpositiveNativeSectionRanks001 p hp hp0
  have hLow :
      (((Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) : ℤ) -
        Module.finrank F (schemeModuleCohomology X S.X₁ 1) < 0) →
          Subsingleton (SchemeModuleOpenSectionsOver pi S.X₁ ⊤)) ∧
      (((Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) : ℤ) -
        Module.finrank F (schemeModuleCohomology X S.X₁ 1) = 0) →
          Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) ≤ 1) := hProperty S.X₁ hM
  have hEuler :
      (Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) : ℤ) -
        Module.finrank F (schemeModuleCohomology X S.X₁ 1) =
          3 * (d : ℤ) - (actualCurveCoordinateHilbertDegree C : ℤ) := hData.2.2
  have hMuInt : (actualCurveCoordinateHilbertDegree C : ℤ) = 3 * (lambda : ℤ) := by
    exact_mod_cast hMu
  have hGrade : Module.finrank F (wholeIdealGrade (grading E)
      (wholeOriginalPlaneCutCoordinateIdeal C p hp) d) ≤
      Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) :=
    @originalWholePlaneIdealGrade_finrank_le_nativeHZero.{u}
      K inferInstance p hp hp0 inferInstance C hpC d hData.1
  constructor
  · intro hWindow
    have hWindowInt : (d : ℤ) < (lambda : ℤ) := by exact_mod_cast hWindow
    have hNegative : (Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) : ℤ) -
        Module.finrank F (schemeModuleCohomology X S.X₁ 1) < 0 := by omega
    have hZero := hLow.1 hNegative
    letI : Subsingleton (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) := hZero
    have hRankZero : Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) = 0 :=
      Module.finrank_zero_of_subsingleton
    exact ⟨hZero, Nat.eq_zero_of_le_zero (hGrade.trans hRankZero.le)⟩
  · intro hWindow
    have hWindowInt : (d : ℤ) = (lambda : ℤ) := by exact_mod_cast hWindow
    have hZero : (Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) : ℤ) -
        Module.finrank F (schemeModuleCohomology X S.X₁ 1) = 0 := by omega
    have hNative := hLow.2 hZero
    exact ⟨hNative, hGrade.trans hNative⟩

end PfaffianDescent.Coray
