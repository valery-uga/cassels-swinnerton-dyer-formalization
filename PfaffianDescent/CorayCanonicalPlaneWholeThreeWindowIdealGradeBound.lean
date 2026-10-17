import PfaffianDescent.CorayCanonicalPlaneWholeLowDegreeSectionBounds
import PfaffianDescent.CorayCanonicalPlaneWholePositiveDegreeCohomology
import PfaffianDescent.CorayOriginalWholePlaneIdealNativeHZeroInjection

/-! SAME canonical whole coefficient supplies all positive ideal-grade windows. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- All three degree windows are derived on the literal canonical cut.
The positive-degree H1 input is constructed by the imported genuine producer. -/
theorem charZero_selectedOriginalWholeCurve_canonicalPlane_threeWindow_idealGradeBound001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (lambda : ℕ) (hMu : actualCurveCoordinateHilbertDegree C = 3 * lambda)
    (d : ℕ) (hd : 1 ≤ d) :
    Module.finrank (GenericHyperplaneField K)
      (wholeIdealGrade
        (grading (equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)))
        (wholeOriginalPlaneCutCoordinateIdeal C p hp) d) ≤
      (if 3 * d = 3 * lambda then 1 else 3 * d - 3 * lambda) := by
  classical
  obtain ⟨hpC, hLow⟩ :=
    selectedOriginalWholeCurve_canonicalPlane_lowDegree_nativeHZero_and_idealGrade001
      p q hp hp0 n hq hnot C hCmin
  have hWindows := hLow lambda hMu d hd
  by_cases hEqual : 3 * d = 3 * lambda
  · rw [if_pos hEqual]
    exact (hWindows.2 (by omega)).2
  · rw [if_neg hEqual]
    by_cases hBelow : d < lambda
    · have hZero := (hWindows.1 hBelow).2
      rw [hZero]
      exact Nat.zero_le _
    · have hAbove : actualCurveCoordinateHilbertDegree C < 3 * d := by omega
      obtain ⟨hpC', hHigh⟩ :=
        charZero_selectedOriginalWholeCurve_canonicalPlane_positiveDegree_firstIdeal_hOne_exactHZero001
          p q hp hp0 n hq hnot C hCmin
      let F := GenericHyperplaneField K
      let E := equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
      let X := scheme E
      let pi := toBase E
      let i := wholeGenericCutPlaneIdealImmersion C p hp hpC'
      letI : IsClosedImmersion i :=
        inferInstanceAs (IsClosedImmersion (wholeGenericCutPlaneIdealImmersion C p hp hpC'))
      letI : HasExt.{u} X.Modules := schemeModules_hasExt X
      letI : Linear F X.Modules := schemeModulesLinearOver pi
      let S : ShortComplex X.Modules := PfaffianDescent.closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (grading E) d)
      have hData := hHigh d hd hAbove
      have hGrade : Module.finrank F (wholeIdealGrade (grading E)
          (wholeOriginalPlaneCutCoordinateIdeal C p hp) d) ≤
          Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) :=
        @originalWholePlaneIdealGrade_finrank_le_nativeHZero.{u}
          K inferInstance p hp hp0 inferInstance C hpC' d hData.1
      have hSum : Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) +
          actualCurveCoordinateHilbertDegree C = 3 * d := hData.2.2
      have hRank : Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) =
          3 * d - 3 * lambda := by omega
      exact hGrade.trans hRank.le

end PfaffianDescent.Coray
