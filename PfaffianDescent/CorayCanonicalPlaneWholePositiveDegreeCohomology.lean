import PfaffianDescent.CorayCanonicalPlaneWholeFirstIdealRankOne
import PfaffianDescent.CorayCanonicalPlaneWholeCutEuler
import PfaffianDescent.CorayOriginalPlanePositiveEulerHOne
import PfaffianDescent.ActualPositiveEulerSectionEquationTransport230

/-! Canonical HF9 coefficient consumer; no supplied rank/H1/Cartier/section data. -/
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

variable [CharZero K]

/-- The SAME canonical whole coefficient has zero H1 and exact native H0
when its actual degree mu is less than3d. Positive Euler constructs the section. -/
theorem charZero_selectedOriginalWholeCurve_canonicalPlane_positiveDegree_firstIdeal_hOne_exactHZero001
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
      ∀ d : ℕ, 1 ≤ d → actualCurveCoordinateHilbertDegree C < 3 * d →
        let S := PfaffianDescent.closedImmersionIdealTwistSequence i
          (positiveSheafOfModules (grading E) d)
        Module.Finite F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) ∧
          Subsingleton (schemeModuleCohomology X S.X₁ 1) ∧
          Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) +
            actualCurveCoordinateHilbertDegree C = 3 * d := by
  classical
  obtain ⟨hpC, hEulerData⟩ :=
    selectedOriginalWholeCurve_canonicalPlane_firstIdeal_finite_euler001
      p q hp hp0 n hq hnot C hCmin
  obtain ⟨hpC', hRankOne⟩ :=
    selectedOriginalWholeCurve_canonicalPlane_firstIdeal_allDegrees_locallyRankOne001
      p q hp hp0 n hq hnot C hCmin
  let F := GenericHyperplaneField K
  let E := equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
  let X := scheme E
  let pi := toBase E
  let i := wholeGenericCutPlaneIdealImmersion C p hp hpC
  letI hNativeExt : HasExt.{u} X.Modules := schemeModules_hasExt X
  letI : Linear F X.Modules := schemeModulesLinearOver pi
  refine ⟨hpC, ?_⟩
  dsimp only
  intro d hd hDegree
  let S : ShortComplex X.Modules := PfaffianDescent.closedImmersionIdealTwistSequence i
    (positiveSheafOfModules (grading E) d)
  have hData := hEulerData d hd
  have hM : schemeModuleLocallyRankOne S.X₁ := hRankOne d
  have hEuler :
      ((Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) : ℤ) -
        Module.finrank F (schemeModuleCohomology X S.X₁ 1) =
          3 * (d : ℤ) - (actualCurveCoordinateHilbertDegree C : ℤ)) := hData.2.2
  have hDegreeInt : (actualCurveCoordinateHilbertDegree C : ℤ) < 3 * (d : ℤ) := by
    exact_mod_cast hDegree
  have hPositive : 0 <
      (Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) : ℤ) -
        Module.finrank F (schemeModuleCohomology X S.X₁ 1) := by
    omega
  obtain ⟨s, hs⟩ := @schemeModule_exists_nonzero_top_section_of_positiveEuler230.{u}
    F inferInstance X hNativeExt pi S.X₁ hPositive
  have hOne : Subsingleton (schemeModuleCohomology X S.X₁ 1) :=
    charZero_originalGenericPlane_positiveEulerSection_hOne_subsingleton001
      p hp hp0 S.X₁ hM s hs hPositive
  letI : Subsingleton (schemeModuleCohomology X S.X₁ 1) := hOne
  have hOneRank : Module.finrank F (schemeModuleCohomology X S.X₁ 1) = 0 :=
    Module.finrank_zero_of_subsingleton
  refine ⟨hData.1, hOne, ?_⟩
  rw [hOneRank] at hEuler
  have hSum : (Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) : ℤ) +
      (actualCurveCoordinateHilbertDegree C : ℤ) = 3 * (d : ℤ) := by
    omega
  exact_mod_cast hSum

end PfaffianDescent.Coray
