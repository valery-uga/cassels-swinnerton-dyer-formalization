import PfaffianDescent.FiniteProjectiveTwistQuotientRank
import PfaffianDescent.CorayActualWholeCutPlaneDivisorCycleDegree
import PfaffianDescent.CorayActualGenericPlaneCubicIntegral

/-! SOURCE ONLY / UNVERIFIED158. The entire finite generic cut in SAME E
constructs every-degree twisted quotient H0 rank m and the genuine native
twisted ideal ShortExact sequence, from ORIGINAL inputs only. The desired
elliptic H0 bound for its first term is not assumed or concluded. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem nativeFiniteRank_congr158
    {F : Type u} [Field F] {Z : Scheme.{u}}
    (g h : Z ⟶ Spec (.of F)) [IsFinite g] [IsFinite h] (e : g = h) :
    finiteSchemeRank g = finiteSchemeRank h := by
  subst h
  rfl

/-- ORIGINAL input constructs the canonical twisted ideal sequence on SAME
actual E for EVERY d. Its quotient has exact native original-parameter-field
rank m and finite top sections, and the whole sequence is ShortExact.
No Cartier, finiteness, quotient rank or section inequality is supplied. -/
theorem selectedOriginalWholeCurve_sameE_twistedIdealQuotient_allDegrees_finite_rank_and_shortExact
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
      ∀ d : ℕ,
        let S := PfaffianDescent.closedImmersionIdealTwistSequence i
          (positiveSheafOfModules (grading I) d)
        S.ShortExact ∧
        Module.Finite (GenericHyperplaneField K)
          (SchemeModuleOpenSectionsOver (toBase I) S.X₃ ⊤) ∧
        Module.finrank (GenericHyperplaneField K)
          (SchemeModuleOpenSectionsOver (toBase I) S.X₃ ⊤) =
            actualCurveCoordinateHilbertDegree C := by
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
  obtain ⟨hfinite, hrank, _hcartier, _hgrades⟩ :=
    selectedOriginalWholeCurve_genericCut_finite_rank_degree p q hp hp0 n hq hnot C hCmin
  letI := hfinite
  have hbase : i ≫ toBase I = toBase (wholeGenericCutIdeal C) :=
    wholeGenericCutPlaneImmersion_toBase C p hp hpC
  letI : IsFinite (i ≫ toBase I) := hbase.symm ▸ hfinite
  letI : Infinite (GenericHyperplaneField K) := genericHyperplaneField_infinite
  have hrankSame : finiteSchemeRank (i ≫ toBase I) = actualCurveCoordinateHilbertDegree C :=
    (nativeFiniteRank_congr158 (i ≫ toBase I) (toBase (wholeGenericCutIdeal C)) hbase).trans hrank
  refine ⟨hpC, ?_⟩
  dsimp only
  intro d
  have hQ := finiteProjectivePositiveTwistQuotient_topSections_finite_and_nativeRank I d i
  exact ⟨quotientPositiveTwist_closedImmersionIdealTwistSequence_shortExact I i d,
    hQ.1, hQ.2.trans hrankSame⟩

end PfaffianDescent.Coray
