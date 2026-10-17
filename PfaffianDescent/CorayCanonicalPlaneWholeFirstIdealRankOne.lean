import PfaffianDescent.CorayActualWholeIdealTwistRankOne172

/-! SAME canonical Fin3 whole cut, without replacing it by its rectangular model. -/
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

/-- Original minimal-component geometry constructs rank one for the literal
canonical whole first ideal-twist term in every degree. No Cartier/rank premise. -/
theorem selectedOriginalWholeCurve_canonicalPlane_firstIdeal_allDegrees_locallyRankOne001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    ∃ hpC : p ∈ C.toIdeal,
      let E := equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
      let i := wholeGenericCutPlaneIdealImmersion C p hp hpC
      ∀ d : ℕ, schemeModuleLocallyRankOne
        (PfaffianDescent.closedImmersionIdealTwistSequence i
          (positiveSheafOfModules (grading E) d)).X₁ := by
  classical
  have hpC : p ∈ C.toIdeal := by
    apply hCmin.le
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (Set.mem_insert p {q})
  let E := equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
  let i := wholeGenericCutPlaneIdealImmersion C p hp hpC
  obtain ⟨H⟩ := selectedOriginalWholeCurve_wholePlaneIdeal_regularPrincipalImmersion
    p q hp hp0 n hq hnot C hCmin hpC
  refine ⟨hpC, ?_⟩
  dsimp only
  intro d
  change schemeModuleLocallyRankOne (schemeModuleTensor
    (IdealSheafDataModule.closedImmersionModule i) (positiveSheafOfModules (grading E) d))
  exact schemeModuleLocallyRankOne_tensor _ _ H.inverseCartierTwist_locallyRankOne
    (planePositiveTwist_locallyRankOne172 E d)

end PfaffianDescent.Coray
