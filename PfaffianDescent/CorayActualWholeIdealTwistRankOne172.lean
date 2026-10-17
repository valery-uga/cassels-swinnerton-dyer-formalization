import PfaffianDescent.CorayActualWholeCutPlaneCartier
import PfaffianDescent.CorayActualWholeCutPlaneTwistedQuotientRank
import PfaffianDescent.RegularPrincipalImmersionNativeRankOne
import PfaffianDescent.VoisinHypersurfacePositiveTwistLocal

/-! SOURCE ONLY172. Discharge the actual whole-ideal coefficient's
locally-rank-one input to the new nonzero-section geometry, preserving
the literal first term of158's original ideal twist sequence. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist MvPolynomial
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem planePositiveTwist_locallyRankOne172
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) K)) (d : ℕ) :
    schemeModuleLocallyRankOne (positiveSheafOfModules (grading I) d) := by
  intro x
  have hx : x ∈ (⨆ j : Fin 3, quotientCoordinateOpen I j) := by
    rw [quotientCoordinateOpen_iSup]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
  let U := quotientCoordinateOpen I j
  let O : (scheme I).Modules := SheafOfModules.unit (scheme I).ringCatSheaf
  exact ⟨U, hj, ⟨overFunctorIsoUnit_of_restrictIsoUnit U
    (quotientCoordinatePositiveTwistUnitIso_all I j d) ≪≫
      (PfaffianDescent.SheafOfModules.overFunctor_globalUnitIso U (Iso.refl O)).symm⟩⟩

/-- Original selected whole curve constructs local rank one of the
ENTIRE actual I_Z tensor O_E(d) for every d. No radical, normalization,
point-word representation or cohomological certificate is introduced. -/
theorem selectedOriginalWholeCurve_sameE_wholeTwistedIdeal_allDegrees_locallyRankOne172
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    ∃ hpC : p ∈ C.toIdeal,
      let I := equationIdeal
        (PfaffianDescent.rectangularSubstitution (genericPlaneInclusionMatrix (K := K))
          (p.map (algebraMap K (GenericHyperplaneField K))))
        (PfaffianDescent.rectangularSubstitution_homogeneous
          (genericPlaneInclusionMatrix (K := K)) (hp.map _))
      let i := wholeGenericCutPlaneImmersion C p hp hpC
      ∀ d : ℕ, schemeModuleLocallyRankOne
        (PfaffianDescent.closedImmersionIdealTwistSequence i
          (positiveSheafOfModules (grading I) d)).X₁ := by
  classical
  have hpC : p ∈ C.toIdeal := by
    apply hCmin.le
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (by simp)
  let I := equationIdeal
    (PfaffianDescent.rectangularSubstitution (genericPlaneInclusionMatrix (K := K))
      (p.map (algebraMap K (GenericHyperplaneField K))))
    (PfaffianDescent.rectangularSubstitution_homogeneous
      (genericPlaneInclusionMatrix (K := K)) (hp.map _))
  let i := wholeGenericCutPlaneImmersion C p hp hpC
  obtain ⟨H⟩ := selectedOriginalWholeCurve_genericCutPlane_regularPrincipalImmersion
    p q hp hp0 n hq hnot C hCmin hpC
  refine ⟨hpC, ?_⟩
  dsimp only
  intro d
  change schemeModuleLocallyRankOne (schemeModuleTensor
    (IdealSheafDataModule.closedImmersionModule i) (positiveSheafOfModules (grading I) d))
  exact schemeModuleLocallyRankOne_tensor _ _ H.inverseCartierTwist_locallyRankOne
    (planePositiveTwist_locallyRankOne172 I d)

end PfaffianDescent.Coray
