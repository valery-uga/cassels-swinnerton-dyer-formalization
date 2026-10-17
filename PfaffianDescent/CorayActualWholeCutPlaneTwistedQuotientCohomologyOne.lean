import PfaffianDescent.FiniteProjectiveTwistQuotientCohomologyOne
import PfaffianDescent.CorayActualWholeCutPlaneTwistedQuotientRank

/-! SOURCE ONLY168. Original-input SAME-E every-degree quotient H1 zero.
No supplied finite-cut, Cartier, genus, section-bound or acyclicity premise.
This does not assert H1 vanishing for the ideal FIRST term. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- For the ENTIRE original cut into SAME actual plane cubic, the quotient
of its literal twisted ideal sequence has zero H1 in EVERY degree. Original
K and original parameter field remain unchanged; infinitude of the latter
and actual cut finiteness are derived inside the proof. -/
theorem selectedOriginalWholeCurve_sameE_twistedIdealQuotient_allDegrees_cohomology_one_subsingleton168
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
      letI : EnoughInjectives (scheme I).Modules :=
        sheafOfModules_enoughInjectives (scheme I).ringCatSheaf
      letI : HasExt.{u} (scheme I).Modules :=
        CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} (scheme I).Modules
      let i := wholeGenericCutPlaneImmersion C p hp hpC
      ∀ d : ℕ,
        let S := PfaffianDescent.closedImmersionIdealTwistSequence i
          (positiveSheafOfModules (grading I) d)
        Subsingleton (schemeModuleCohomology (scheme I) S.X₃ 1) := by
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
  obtain ⟨hfinite, _hrank, _hcartier, _hgrades⟩ :=
    selectedOriginalWholeCurve_genericCut_finite_rank_degree p q hp hp0 n hq hnot C hCmin
  letI := hfinite
  have hbase : i ≫ toBase I = toBase (wholeGenericCutIdeal C) :=
    wholeGenericCutPlaneImmersion_toBase C p hp hpC
  letI : IsFinite (i ≫ toBase I) := hbase.symm ▸ hfinite
  letI : Infinite (GenericHyperplaneField K) := genericHyperplaneField_infinite
  letI : EnoughInjectives (scheme I).Modules :=
    sheafOfModules_enoughInjectives (scheme I).ringCatSheaf
  letI : HasExt.{u} (scheme I).Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} (scheme I).Modules
  refine ⟨hpC, ?_⟩
  dsimp only
  intro d
  exact finiteProjectivePositiveTwistQuotient_cohomology_one_subsingleton168 I d i

end PfaffianDescent.Coray
