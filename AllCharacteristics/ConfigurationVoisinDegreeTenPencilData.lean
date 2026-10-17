import AllCharacteristics.ProjectiveConfigurationCurveFiniteSubscheme
import AllCharacteristics.HomogeneousConfigurationQuotient
import PfaffianDescent.VoisinFiniteSubschemeRankTwoFamily

/-!
# Configuration curves as Voisin's three finite-flat pencils

A projective configuration curve carries a finite flat incidence subscheme.
After identifying its two endpoint incidence schemes with the selected
residual data, it gives one of the actual finite-subscheme pencils in
Voisin's degree-ten argument.  This module assembles the three such curves.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits PfaffianDescent

namespace AllCharacteristics.HomogeneousProjective

universe u v

variable {A : Type u} [CommRing A]
variable {K : Type u} [Field K]
variable {sigma : Type v} [SetLike sigma A] [AddSubgroupClass sigma A]
variable (graded : ℕ → sigma) [GradedRing graded]
variable (f : Proj graded ⟶ Spec (.of K)) [IsSeparated f]

/-- Three configuration-space curves whose endpoint incidence schemes are
identified with Voisin's residual data give the concrete finite-flat pencil
package.  Thus a later geometric construction of those curves feeds the
cycle arithmetic without any further conversion through abstract families. -/
noncomputable def voisinDegreeTenPointPencilData_of_configurationCurves
    (D₁₆ : FiniteSubschemeDatum f 16)
    (D₁₁ : FiniteSubschemeDatum f 11)
    (h₁₆₁₁ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₁₆))
      (Set.range (finiteSubschemeDatumSpecMap f D₁₁)))
    (D₂₇ : FiniteSubschemeDatum f 27)
    (c₂₇ : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f 27).toScheme)
    (hc₂₇ : c₂₇ ≫ projectiveConfigurationQuotientToBase graded f 27 =
      projectiveLineProjToBase K)
    (zero₂₇Iso : (finiteSubschemeDatumAtLineEndpoint f 27
      (projectiveConfigurationCurveFiniteSubscheme graded f 27 c₂₇ hc₂₇) false).val.subscheme ≅
        (finiteSubschemeDatumOfTwoDisjointData f D₁₆ D₁₁ h₁₆₁₁).val.subscheme)
    (zero₂₇_over : zero₂₇Iso.hom ≫
      (finiteSubschemeDatumOfTwoDisjointData f D₁₆ D₁₁ h₁₆₁₁).val.subschemeι =
        (finiteSubschemeDatumAtLineEndpoint f 27
          (projectiveConfigurationCurveFiniteSubscheme graded f 27 c₂₇ hc₂₇) false).val.subschemeι)
    (infinity₂₇Iso : (finiteSubschemeDatumAtLineEndpoint f 27
      (projectiveConfigurationCurveFiniteSubscheme graded f 27 c₂₇ hc₂₇) true).val.subscheme ≅
        D₂₇.val.subscheme)
    (infinity₂₇_over : infinity₂₇Iso.hom ≫ D₂₇.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint f 27
        (projectiveConfigurationCurveFiniteSubscheme graded f 27 c₂₇ hc₂₇) true).val.subschemeι)
    (D₃ : FiniteSubschemeDatum f 3)
    (D₈ : FiniteSubschemeDatum f 8)
    (h₈₃ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
      (Set.range (finiteSubschemeDatumSpecMap f D₃)))
    (c₁₁ : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f 11).toScheme)
    (hc₁₁ : c₁₁ ≫ projectiveConfigurationQuotientToBase graded f 11 =
      projectiveLineProjToBase K)
    (zero₁₁Iso : (finiteSubschemeDatumAtLineEndpoint f 11
      (projectiveConfigurationCurveFiniteSubscheme graded f 11 c₁₁ hc₁₁) false).val.subscheme ≅
        (degreeEightAndDegreeThreeDatum f D₈ D₃ h₈₃).val.subscheme)
    (zero₁₁_over : zero₁₁Iso.hom ≫
      (degreeEightAndDegreeThreeDatum f D₈ D₃ h₈₃).val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint f 11
        (projectiveConfigurationCurveFiniteSubscheme graded f 11 c₁₁ hc₁₁) false).val.subschemeι)
    (infinity₁₁Iso : (finiteSubschemeDatumAtLineEndpoint f 11
      (projectiveConfigurationCurveFiniteSubscheme graded f 11 c₁₁ hc₁₁) true).val.subscheme ≅
        D₁₁.val.subscheme)
    (infinity₁₁_over : infinity₁₁Iso.hom ≫ D₁₁.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint f 11
        (projectiveConfigurationCurveFiniteSubscheme graded f 11 c₁₁ hc₁₁) true).val.subschemeι)
    (D₄ : FiniteSubschemeDatum f 4)
    (h₈₄ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
      (Set.range (finiteSubschemeDatumSpecMap f D₄)))
    (D₁₂ : FiniteSubschemeDatum f 12)
    (c₁₂ : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f 12).toScheme)
    (hc₁₂ : c₁₂ ≫ projectiveConfigurationQuotientToBase graded f 12 =
      projectiveLineProjToBase K)
    (zero₁₂Iso : (finiteSubschemeDatumAtLineEndpoint f 12
      (projectiveConfigurationCurveFiniteSubscheme graded f 12 c₁₂ hc₁₂) false).val.subscheme ≅
        (finiteSubschemeDatumOfTwoDisjointData f D₈ D₄ h₈₄).val.subscheme)
    (zero₁₂_over : zero₁₂Iso.hom ≫
      (finiteSubschemeDatumOfTwoDisjointData f D₈ D₄ h₈₄).val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint f 12
        (projectiveConfigurationCurveFiniteSubscheme graded f 12 c₁₂ hc₁₂) false).val.subschemeι)
    (infinity₁₂Iso : (finiteSubschemeDatumAtLineEndpoint f 12
      (projectiveConfigurationCurveFiniteSubscheme graded f 12 c₁₂ hc₁₂) true).val.subscheme ≅
        D₁₂.val.subscheme)
    (infinity₁₂_over : infinity₁₂Iso.hom ≫ D₁₂.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint f 12
        (projectiveConfigurationCurveFiniteSubscheme graded f 12 c₁₂ hc₁₂) true).val.subschemeι) :
    VoisinDegreeTenPointPencilData f where
  D₁₆ := D₁₆
  D₁₁ := D₁₁
  disjoint₁₆₁₁ := h₁₆₁₁
  D₂₇ := D₂₇
  cubicPencil := projectiveConfigurationCurveFiniteSubschemePencil_retarget graded f 27
    c₂₇ hc₂₇ (finiteSubschemeDatumOfTwoDisjointData f D₁₆ D₁₁ h₁₆₁₁) D₂₇
    zero₂₇Iso zero₂₇_over infinity₂₇Iso infinity₂₇_over
  D₃ := D₃
  D₈ := D₈
  disjoint₈₃ := h₈₃
  rankTwoPencil := projectiveConfigurationCurveFiniteSubschemePencil_retarget graded f 11
    c₁₁ hc₁₁ (degreeEightAndDegreeThreeDatum f D₈ D₃ h₈₃) D₁₁
    zero₁₁Iso zero₁₁_over infinity₁₁Iso infinity₁₁_over
  D₄ := D₄
  disjoint₈₄ := h₈₄
  D₁₂ := D₁₂
  quadricPencil := projectiveConfigurationCurveFiniteSubschemePencil_retarget graded f 12
    c₁₂ hc₁₂ (finiteSubschemeDatumOfTwoDisjointData f D₈ D₄ h₈₄) D₁₂
    zero₁₂Iso zero₁₂_over infinity₁₂Iso infinity₁₂_over
/-- Configuration curves whose endpoint incidence schemes are the three residual
subschemes give Voisin's exact degree-ten point steps after their endpoint
cycle classes are calculated. -/
theorem voisinDegreeTenPointSteps_of_configurationCurves_and_cycleClasses
    [Infinite K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (C : DegreeTenRankSixteenCompletion p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx))
    (D₁₁ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11)
    (h₁₆₁₁ : Disjoint (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) C.datum))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₁)))
    (D₂₇ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 27)
    (c₂₇ : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 27).toScheme)
    (hc₂₇ : c₂₇ ≫ projectiveConfigurationQuotientToBase
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 27 =
      projectiveLineProjToBase K)
    (zero₂₇Iso : (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 27
      (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 27 c₂₇ hc₂₇) false).val.subscheme ≅
        (finiteSubschemeDatumOfTwoDisjointData (hypersurfaceToBase p hp)
          C.datum D₁₁ h₁₆₁₁).val.subscheme)
    (zero₂₇_over : zero₂₇Iso.hom ≫
      (finiteSubschemeDatumOfTwoDisjointData (hypersurfaceToBase p hp)
        C.datum D₁₁ h₁₆₁₁).val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 27
        (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 27 c₂₇ hc₂₇) false).val.subschemeι)
    (infinity₂₇Iso : (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 27
      (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 27 c₂₇ hc₂₇) true).val.subscheme ≅
        D₂₇.val.subscheme)
    (infinity₂₇_over : infinity₂₇Iso.hom ≫ D₂₇.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 27
        (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 27 c₂₇ hc₂₇) true).val.subschemeι)
    (D₃ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (h₈₃ : Disjoint (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
    (c₁₁ : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 11).toScheme)
    (hc₁₁ : c₁₁ ≫ projectiveConfigurationQuotientToBase
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 11 =
      projectiveLineProjToBase K)
    (zero₁₁Iso : (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 11
      (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 11 c₁₁ hc₁₁) false).val.subscheme ≅
        (degreeEightAndDegreeThreeDatum (hypersurfaceToBase p hp) D₈ D₃ h₈₃).val.subscheme)
    (zero₁₁_over : zero₁₁Iso.hom ≫
      (degreeEightAndDegreeThreeDatum (hypersurfaceToBase p hp) D₈ D₃ h₈₃).val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 11
        (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 11 c₁₁ hc₁₁) false).val.subschemeι)
    (infinity₁₁Iso : (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 11
      (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 11 c₁₁ hc₁₁) true).val.subscheme ≅
        D₁₁.val.subscheme)
    (infinity₁₁_over : infinity₁₁Iso.hom ≫ D₁₁.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 11
        (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 11 c₁₁ hc₁₁) true).val.subschemeι)
    (D₄ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4)
    (h₈₄ : Disjoint (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₄)))
    (D₁₂ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 12)
    (c₁₂ : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 12).toScheme)
    (hc₁₂ : c₁₂ ≫ projectiveConfigurationQuotientToBase
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 12 =
      projectiveLineProjToBase K)
    (zero₁₂Iso : (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 12
      (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 12 c₁₂ hc₁₂) false).val.subscheme ≅
        (finiteSubschemeDatumOfTwoDisjointData (hypersurfaceToBase p hp)
          D₈ D₄ h₈₄).val.subscheme)
    (zero₁₂_over : zero₁₂Iso.hom ≫
      (finiteSubschemeDatumOfTwoDisjointData (hypersurfaceToBase p hp)
        D₈ D₄ h₈₄).val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 12
        (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 12 c₁₂ hc₁₂) false).val.subschemeι)
    (infinity₁₂Iso : (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 12
      (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 12 c₁₂ hc₁₂) true).val.subscheme ≅
        D₁₂.val.subscheme)
    (infinity₁₂_over : infinity₁₂Iso.hom ≫ D₁₂.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 12
        (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 12 c₁₂ hc₁₂) true).val.subschemeι)
    (h : EffectiveZeroCycle (hypersurface p hp))
    (hfirst : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.first).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (hsecond : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.second).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (cycle₂₇ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) D₂₇).toZeroCycle =
        9 • curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (cycle₃ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) D₃).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (cycle₁₂ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) D₁₂).toZeroCycle =
        4 • curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle) :
    VoisinDegreeTenPointSteps (hypersurfaceToBase p hp) h (Finsupp.single x 1) := by
  let _ : IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp)) := by
    exact ‹IsSeparated (hypersurfaceToBase p hp)›
  let S := voisinDegreeTenPointPencilData_of_configurationCurves
    (grading (equationIdeal p hp))
    (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
      toBase (equationIdeal p hp))
    C.datum D₁₁ h₁₆₁₁ D₂₇ c₂₇ hc₂₇ zero₂₇Iso zero₂₇_over infinity₂₇Iso infinity₂₇_over
    D₃ D₈ h₈₃ c₁₁ hc₁₁ zero₁₁Iso zero₁₁_over infinity₁₁Iso infinity₁₁_over
    D₄ h₈₄ D₁₂ c₁₂ hc₁₂ zero₁₂Iso zero₁₂_over infinity₁₂Iso infinity₁₂_over
  apply voisinDegreeTenPointSteps_of_completion_and_cycleClasses p hp x hx C h
    hfirst hsecond S
  · dsimp [S, voisinDegreeTenPointPencilData_of_configurationCurves]
  · dsimp [S, voisinDegreeTenPointPencilData_of_configurationCurves]
    exact cycle₂₇
  · dsimp [S, voisinDegreeTenPointPencilData_of_configurationCurves]
    exact cycle₃
  · dsimp [S, voisinDegreeTenPointPencilData_of_configurationCurves]
    exact cycle₁₂


/-- The zero endpoint of a retargeted configuration pencil has the class of
the corresponding configuration fiber. -/
theorem projectiveConfigurationCurveFiniteSubschemePencil_retarget_zero_cycleClass_eq_configurationCycle
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K)
    (zeroDatum infinityDatum : FiniteSubschemeDatum f n)
    (zeroIso : (finiteSubschemeDatumAtLineEndpoint f n
      (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) false).val.subscheme ≅
        zeroDatum.val.subscheme)
    (zero_over : zeroIso.hom ≫ zeroDatum.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint f n
        (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) false).val.subschemeι)
    (infinityIso : (finiteSubschemeDatumAtLineEndpoint f n
      (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) true).val.subscheme ≅
        infinityDatum.val.subscheme)
    (infinity_over : infinityIso.hom ≫ infinityDatum.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint f n
        (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) true).val.subschemeι) :
    curveFamilyCycleClass f (finiteSubschemeDatumCycle f zeroDatum).toZeroCycle =
      curveFamilyCycleClass f (projectiveConfigurationCycle graded f n
        (projectiveLineEndpoint K false ≫ c) (by
          rw [Category.assoc, hc, projectiveLineEndpoint_toBase])).toZeroCycle := by
  let P := projectiveConfigurationCurveFiniteSubschemePencil_retarget graded f n c hc
    zeroDatum infinityDatum zeroIso zero_over infinityIso infinity_over
  let D := projectiveConfigurationCurveFiniteSubscheme graded f n c hc
  let F := rationalCycleFamily_of_configurationCurve graded f n c hc
  calc
    curveFamilyCycleClass f (finiteSubschemeDatumCycle f zeroDatum).toZeroCycle =
        curveFamilyCycleClass f ((FiniteSubschemeDatumPencil.toRationalCycleFamily f P).fiberCycle false).toZeroCycle := by
      rw [FiniteSubschemeDatumPencil.fiberCycle_zero]
    _ = curveFamilyCycleClass f ((rationalCycleFamily_of_finiteSubschemeDatum f n D).fiberCycle false).toZeroCycle := by
      rfl
    _ = curveFamilyCycleClass f (F.fiberCycle false).toZeroCycle := by
      rw [rationalCycleFamily_of_projectiveConfigurationCurveFiniteSubscheme_fiberCycle_eq]
    _ = curveFamilyCycleClass f (projectiveConfigurationCycle graded f n
        (projectiveLineEndpoint K false ≫ c) (by
          rw [Category.assoc, hc, projectiveLineEndpoint_toBase])).toZeroCycle := by
      rw [rationalCycleFamily_of_configurationCurve_fiberCycle_eq_projectiveConfigurationCycle]

/-- The infinity endpoint of a retargeted configuration pencil has the class
of the corresponding configuration fiber. -/
theorem projectiveConfigurationCurveFiniteSubschemePencil_retarget_infinity_cycleClass_eq_configurationCycle
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K)
    (zeroDatum infinityDatum : FiniteSubschemeDatum f n)
    (zeroIso : (finiteSubschemeDatumAtLineEndpoint f n
      (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) false).val.subscheme ≅
        zeroDatum.val.subscheme)
    (zero_over : zeroIso.hom ≫ zeroDatum.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint f n
        (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) false).val.subschemeι)
    (infinityIso : (finiteSubschemeDatumAtLineEndpoint f n
      (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) true).val.subscheme ≅
        infinityDatum.val.subscheme)
    (infinity_over : infinityIso.hom ≫ infinityDatum.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint f n
        (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) true).val.subschemeι) :
    curveFamilyCycleClass f (finiteSubschemeDatumCycle f infinityDatum).toZeroCycle =
      curveFamilyCycleClass f (projectiveConfigurationCycle graded f n
        (projectiveLineEndpoint K true ≫ c) (by
          rw [Category.assoc, hc, projectiveLineEndpoint_toBase])).toZeroCycle := by
  let P := projectiveConfigurationCurveFiniteSubschemePencil_retarget graded f n c hc
    zeroDatum infinityDatum zeroIso zero_over infinityIso infinity_over
  let D := projectiveConfigurationCurveFiniteSubscheme graded f n c hc
  let F := rationalCycleFamily_of_configurationCurve graded f n c hc
  calc
    curveFamilyCycleClass f (finiteSubschemeDatumCycle f infinityDatum).toZeroCycle =
        curveFamilyCycleClass f ((FiniteSubschemeDatumPencil.toRationalCycleFamily f P).fiberCycle true).toZeroCycle := by
      rw [FiniteSubschemeDatumPencil.fiberCycle_infinity]
    _ = curveFamilyCycleClass f ((rationalCycleFamily_of_finiteSubschemeDatum f n D).fiberCycle true).toZeroCycle := by
      rfl
    _ = curveFamilyCycleClass f (F.fiberCycle true).toZeroCycle := by
      rw [rationalCycleFamily_of_projectiveConfigurationCurveFiniteSubscheme_fiberCycle_eq]
    _ = curveFamilyCycleClass f (projectiveConfigurationCycle graded f n
        (projectiveLineEndpoint K true ≫ c) (by
          rw [Category.assoc, hc, projectiveLineEndpoint_toBase])).toZeroCycle := by
      rw [rationalCycleFamily_of_configurationCurve_fiberCycle_eq_projectiveConfigurationCycle]


attribute [local instance] MvPolynomial.gradedAlgebra


/-- The cycle of an endpoint of a projective configuration curve on a cubic
hypersurface, written in the cubic's standard `hypersurface` presentation. -/
noncomputable def cubicConfigurationCurveEndpointCycle
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (toBase (equationIdeal p hp)) n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase
      (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n =
      projectiveLineProjToBase K)
    (b : Bool) : EffectiveZeroCycle (hypersurface p hp) := by
  exact @projectiveConfigurationCycle _ _ _ _ _
    (grading (equationIdeal p hp)) _ K _ (toBase (equationIdeal p hp))
    (isSeparated_homogeneousToBase (equationIdeal p hp)) n
    (projectiveLineEndpoint K b ≫ c) (by
      rw [Category.assoc, hc, projectiveLineEndpoint_toBase])

/-- The endpoint class of a retargeted configuration pencil equals the class
of its cubic configuration endpoint. -/
theorem finiteSubschemeDatumPencil_retarget_infinity_cycleClass_eq_cubicConfigurationCurveEndpoint
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (toBase (equationIdeal p hp)) n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase
      (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n =
      projectiveLineProjToBase K)
    (zeroDatum infinityDatum : FiniteSubschemeDatum (toBase (equationIdeal p hp)) n)
    (zeroIso : (finiteSubschemeDatumAtLineEndpoint (toBase (equationIdeal p hp)) n
      (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
        (toBase (equationIdeal p hp)) n c hc) false).val.subscheme ≅ zeroDatum.val.subscheme)
    (zero_over : zeroIso.hom ≫ zeroDatum.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint (toBase (equationIdeal p hp)) n
        (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
          (toBase (equationIdeal p hp)) n c hc) false).val.subschemeι)
    (infinityIso : (finiteSubschemeDatumAtLineEndpoint (toBase (equationIdeal p hp)) n
      (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
        (toBase (equationIdeal p hp)) n c hc) true).val.subscheme ≅ infinityDatum.val.subscheme)
    (infinity_over : infinityIso.hom ≫ infinityDatum.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint (toBase (equationIdeal p hp)) n
        (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
          (toBase (equationIdeal p hp)) n c hc) true).val.subschemeι) :
    curveFamilyCycleClass (toBase (equationIdeal p hp))
      (finiteSubschemeDatumCycle (toBase (equationIdeal p hp)) infinityDatum).toZeroCycle =
      curveFamilyCycleClass (toBase (equationIdeal p hp))
        (cubicConfigurationCurveEndpointCycle p hp n c hc true).toZeroCycle := by
  exact @projectiveConfigurationCurveFiniteSubschemePencil_retarget_infinity_cycleClass_eq_configurationCycle
    _ _ _ _ _ _ _ (grading (equationIdeal p hp)) _ (toBase (equationIdeal p hp))
    (isSeparated_homogeneousToBase (equationIdeal p hp)) n c hc
    zeroDatum infinityDatum zeroIso zero_over infinityIso infinity_over


/-- Configuration curves whose endpoint incidence schemes are the three residual
subschemes give Voisin's exact degree-ten point steps after their endpoint
cycle classes are calculated. -/
theorem voisinDegreeTenPointSteps_of_configurationCurves_and_configurationEndpointCycleClasses
    [Infinite K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (C : DegreeTenRankSixteenCompletion p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx))
    (D₁₁ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11)
    (h₁₆₁₁ : Disjoint (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) C.datum))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₁)))
    (D₂₇ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 27)
    (c₂₇ : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 27).toScheme)
    (hc₂₇ : c₂₇ ≫ projectiveConfigurationQuotientToBase
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 27 =
      projectiveLineProjToBase K)
    (zero₂₇Iso : (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 27
      (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 27 c₂₇ hc₂₇) false).val.subscheme ≅
        (finiteSubschemeDatumOfTwoDisjointData (hypersurfaceToBase p hp)
          C.datum D₁₁ h₁₆₁₁).val.subscheme)
    (zero₂₇_over : zero₂₇Iso.hom ≫
      (finiteSubschemeDatumOfTwoDisjointData (hypersurfaceToBase p hp)
        C.datum D₁₁ h₁₆₁₁).val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 27
        (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 27 c₂₇ hc₂₇) false).val.subschemeι)
    (infinity₂₇Iso : (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 27
      (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 27 c₂₇ hc₂₇) true).val.subscheme ≅
        D₂₇.val.subscheme)
    (infinity₂₇_over : infinity₂₇Iso.hom ≫ D₂₇.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 27
        (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 27 c₂₇ hc₂₇) true).val.subschemeι)
    (D₃ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (h₈₃ : Disjoint (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
    (c₁₁ : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 11).toScheme)
    (hc₁₁ : c₁₁ ≫ projectiveConfigurationQuotientToBase
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 11 =
      projectiveLineProjToBase K)
    (zero₁₁Iso : (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 11
      (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 11 c₁₁ hc₁₁) false).val.subscheme ≅
        (degreeEightAndDegreeThreeDatum (hypersurfaceToBase p hp) D₈ D₃ h₈₃).val.subscheme)
    (zero₁₁_over : zero₁₁Iso.hom ≫
      (degreeEightAndDegreeThreeDatum (hypersurfaceToBase p hp) D₈ D₃ h₈₃).val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 11
        (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 11 c₁₁ hc₁₁) false).val.subschemeι)
    (infinity₁₁Iso : (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 11
      (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 11 c₁₁ hc₁₁) true).val.subscheme ≅
        D₁₁.val.subscheme)
    (infinity₁₁_over : infinity₁₁Iso.hom ≫ D₁₁.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 11
        (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 11 c₁₁ hc₁₁) true).val.subschemeι)
    (D₄ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4)
    (h₈₄ : Disjoint (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₄)))
    (D₁₂ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 12)
    (c₁₂ : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 12).toScheme)
    (hc₁₂ : c₁₂ ≫ projectiveConfigurationQuotientToBase
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 12 =
      projectiveLineProjToBase K)
    (zero₁₂Iso : (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 12
      (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 12 c₁₂ hc₁₂) false).val.subscheme ≅
        (finiteSubschemeDatumOfTwoDisjointData (hypersurfaceToBase p hp)
          D₈ D₄ h₈₄).val.subscheme)
    (zero₁₂_over : zero₁₂Iso.hom ≫
      (finiteSubschemeDatumOfTwoDisjointData (hypersurfaceToBase p hp)
        D₈ D₄ h₈₄).val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 12
        (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 12 c₁₂ hc₁₂) false).val.subschemeι)
    (infinity₁₂Iso : (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 12
      (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 12 c₁₂ hc₁₂) true).val.subscheme ≅
        D₁₂.val.subscheme)
    (infinity₁₂_over : infinity₁₂Iso.hom ≫ D₁₂.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint (hypersurfaceToBase p hp) 12
        (projectiveConfigurationCurveFiniteSubscheme (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 12 c₁₂ hc₁₂) true).val.subschemeι)
    (h : EffectiveZeroCycle (hypersurface p hp))
    (hfirst : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.first).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (hsecond : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.second).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (cycle₂₇ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (cubicConfigurationCurveEndpointCycle p hp 27 c₂₇ hc₂₇ true).toZeroCycle =
        9 • curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (cycle₃ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) D₃).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (cycle₁₂ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (cubicConfigurationCurveEndpointCycle p hp 12 c₁₂ hc₁₂ true).toZeroCycle =
        4 • curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle) :
    VoisinDegreeTenPointSteps (hypersurfaceToBase p hp) h (Finsupp.single x 1) := by
  let S := voisinDegreeTenPointPencilData_of_configurationCurves
    (grading (equationIdeal p hp))
    (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
      toBase (equationIdeal p hp))
    C.datum D₁₁ h₁₆₁₁ D₂₇ c₂₇ hc₂₇ zero₂₇Iso zero₂₇_over infinity₂₇Iso infinity₂₇_over
    D₃ D₈ h₈₃ c₁₁ hc₁₁ zero₁₁Iso zero₁₁_over infinity₁₁Iso infinity₁₁_over
    D₄ h₈₄ D₁₂ c₁₂ hc₁₂ zero₁₂Iso zero₁₂_over infinity₁₂Iso infinity₁₂_over
  apply voisinDegreeTenPointSteps_of_completion_and_cycleClasses p hp x hx C h
    hfirst hsecond S
  · dsimp [S, voisinDegreeTenPointPencilData_of_configurationCurves]
  · dsimp [S, voisinDegreeTenPointPencilData_of_configurationCurves]
    calc
      curveFamilyCycleClass (hypersurfaceToBase p hp)
          (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) D₂₇).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp)
          (cubicConfigurationCurveEndpointCycle p hp 27 c₂₇ hc₂₇ true).toZeroCycle := by
          exact finiteSubschemeDatumPencil_retarget_infinity_cycleClass_eq_cubicConfigurationCurveEndpoint
            p hp 27 c₂₇ hc₂₇
            (finiteSubschemeDatumOfTwoDisjointData (hypersurfaceToBase p hp)
              C.datum D₁₁ h₁₆₁₁) D₂₇ zero₂₇Iso zero₂₇_over infinity₂₇Iso infinity₂₇_over
      _ = _ := cycle₂₇
  · dsimp [S, voisinDegreeTenPointPencilData_of_configurationCurves]
    exact cycle₃
  · dsimp [S, voisinDegreeTenPointPencilData_of_configurationCurves]
    calc
      curveFamilyCycleClass (hypersurfaceToBase p hp)
          (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) D₁₂).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp)
          (cubicConfigurationCurveEndpointCycle p hp 12 c₁₂ hc₁₂ true).toZeroCycle := by
          exact finiteSubschemeDatumPencil_retarget_infinity_cycleClass_eq_cubicConfigurationCurveEndpoint
            p hp 12 c₁₂ hc₁₂
            (finiteSubschemeDatumOfTwoDisjointData (hypersurfaceToBase p hp)
              D₈ D₄ h₈₄) D₁₂ zero₁₂Iso zero₁₂_over infinity₁₂Iso infinity₁₂_over
      _ = _ := cycle₁₂


/-- An endpoint of a cubic configuration curve has the prescribed degree. -/
theorem cubicConfigurationCurveEndpointCycle_degree
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (toBase (equationIdeal p hp)) n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase
      (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n =
      projectiveLineProjToBase K)
    (b : Bool) :
    EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
      (cubicConfigurationCurveEndpointCycle p hp n c hc b) = n := by
  exact @projectiveConfigurationCycle_degree _ _ _ _ _
    (grading (equationIdeal p hp)) _ K _ (toBase (equationIdeal p hp))
    (isSeparated_homogeneousToBase (equationIdeal p hp)) n
    (projectiveLineEndpoint K b ≫ c) (by
      rw [Category.assoc, hc, projectiveLineEndpoint_toBase])


end AllCharacteristics.HomogeneousProjective
