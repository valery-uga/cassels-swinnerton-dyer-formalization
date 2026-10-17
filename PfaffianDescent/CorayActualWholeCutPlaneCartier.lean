import PfaffianDescent.CorayActualWholeCutPlaneIdealTransport
import PfaffianDescent.CorayWholePlaneGradeEquivalence
import PfaffianDescent.CorayHilbertDeficitHomogeneousMember
import PfaffianDescent.CorayPlaneCubicHilbertFunction
import PfaffianDescent.CorayActualWholeGenericCutFinite
import PfaffianDescent.CorayActualGenericPlaneCubicIntegral
import PfaffianDescent.CorayPlaneCubicWholeIdealCartier

/-! SOURCE ONLY / UNCOMPILED156. ORIGINAL p,q,C inputs produce a Cartier
presentation for the ENTIRE generic cut into SAME actual149 E. The derived
whole finite-cut eventual grades and native cubic3d internally produce a
surviving equation. No finite/Cartier/regular-chart/rank/component premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Finiteness and actual native whole-cut grades force an actual homogeneous
member of the ENTIRE Fin3 ideal outside SAME(F). Original degree/rank is retained. -/
theorem selectedOriginalWholeCurve_wholePlaneIdeal_exists_survivingHomogeneousEquation
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    ∃ d, 1 ≤ d ∧ ∃ f : MvPolynomial (Fin 3) (GenericHyperplaneField K),
      f.IsHomogeneous d ∧ f ∈ (wholeGenericCutPlaneIdeal C).toIdeal ∧
      f ∉ (equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)).toIdeal := by
  classical
  obtain ⟨hfinite, hrest⟩ := selectedOriginalWholeCurve_genericCut_finite_rank_degree
    p q hp hp0 n hq hnot C hCmin
  letI := hfinite
  obtain ⟨_hrank, _hregular, N, hN⟩ := hrest
  have hpC : p ∈ C.toIdeal := by
    apply hCmin.le
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (Set.mem_insert p {q})
  let d := max N 1 + actualCurveCoordinateHilbertDegree C + 1
  have hdN : N ≤ d := by
    have := le_max_left N 1
    dsimp [d]
    omega
  have hd1 : 1 ≤ d := by
    have := le_max_right N 1
    dsimp [d]
    omega
  have hm : actualCurveCoordinateHilbertDegree C < 3 * d := by dsimp [d]; omega
  have hDgrade : finrank (GenericHyperplaneField K) (grading (wholeGenericCutPlaneIdeal C) d) =
      actualCurveCoordinateHilbertDegree C := by
    have heq := wholePlaneCoordinateGrade_finrank_eq
      (genericHyperplaneCoefficient (K := K)) (wholeGenericCutIdeal C)
      (wholeGenericCut_contains_planeRelation C) d
    exact heq.symm.trans (hN d hdN)
  have hFgrade : finrank (GenericHyperplaneField K)
      (grading (equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)) d) =
        3 * d :=
    planeCubicCoordinateGrade_finrank_eq_three_mul _ _
      (genericPlaneCubic_ne_zero p hp hp0) d hd1
  have hdeficit : finrank (GenericHyperplaneField K) (grading (wholeGenericCutPlaneIdeal C) d) <
      finrank (GenericHyperplaneField K)
        (grading (equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)) d) := by
    rw [hDgrade, hFgrade]
    exact hm
  exact ⟨d, hd1, homogeneousMember_of_strictCoordinateGrade_finrank
    _ (wholeGenericCutPlaneIdeal C)
    (genericPlaneCubic_ideal_le_wholeGenericCutPlaneIdeal C p hp hpC) d hdeficit⟩

/-- The ACTUAL entire Fin3 cut immersion into literal SAME F is Cartier;
all smoothness, prime, nonzero-kernel, PID and covering inputs are derived. -/
theorem selectedOriginalWholeCurve_wholePlaneIdeal_regularPrincipalImmersion
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (hpC : p ∈ C.toIdeal) :
    Nonempty (PfaffianDescent.RegularPrincipalImmersion
      (wholeGenericCutPlaneIdealImmersion C p hp hpC)) := by
  obtain ⟨d, _hd, f, hfd, hfD, hfF⟩ :=
    selectedOriginalWholeCurve_wholePlaneIdeal_exists_survivingHomogeneousEquation
      p q hp hp0 n hq hnot C hCmin
  letI : Smooth (hypersurfaceToBase (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)) :=
    smoothCubic_actualGenericPlaneCubic_smooth p hp hp0
  exact ⟨planeCubicWholeIdeal_regularPrincipalImmersion
    (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
    (genericPlaneCubic_ne_zero p hp hp0)
    (smoothCubic_actualGenericPlaneCubic_principalIdeal_prime p hp hp0)
    (wholeGenericCutPlaneIdeal C) (genericPlaneCubic_ideal_le_wholeGenericCutPlaneIdeal C p hp hpC)
    f hfd hfD hfF⟩

/-- Iso transport gives the actual whole Fin3 cut immersion into SAME actual149
E. The only comparison used is the CONSTRUCTED accepted151 pair comparison. -/
theorem selectedOriginalWholeCurve_wholePlaneIdealToSameE_regularPrincipalImmersion
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (hpC : p ∈ C.toIdeal) :
    Nonempty (PfaffianDescent.RegularPrincipalImmersion
      (wholeGenericCutPlaneIdealToSameE C p hp hpC)) := by
  obtain ⟨H⟩ := selectedOriginalWholeCurve_wholePlaneIdeal_regularPrincipalImmersion
    p q hp hp0 n hq hnot C hCmin hpC
  refine ⟨H.ofIso (genericPlaneCubicToActualSectionIso p hp).symm (Iso.refl _) ?_⟩
  simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom,
    wholeGenericCutPlaneIdealToSameE, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The ENTIRE original literal Fin4 generic cut into SAME E is Cartier.
Its actual original immersion is the155 one, with all original thickness. -/
theorem selectedOriginalWholeCurve_genericCutPlane_regularPrincipalImmersion
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (hpC : p ∈ C.toIdeal) :
    Nonempty (PfaffianDescent.RegularPrincipalImmersion
      (wholeGenericCutPlaneImmersion C p hp hpC)) := by
  obtain ⟨H⟩ := selectedOriginalWholeCurve_wholePlaneIdealToSameE_regularPrincipalImmersion
    p q hp hp0 n hq hnot C hCmin hpC
  refine ⟨H.ofIso (Iso.refl _) (wholeGenericCutPlaneSchemeIso C).symm ?_⟩
  simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
  rw [← wholeGenericCutPlaneSchemeIso_sameE_triangle]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]


/-- Final original-input construction: even original cubic containment is
constructed from the selected ORIGINAL component, not supplied to the caller. -/
theorem selectedOriginalWholeCurve_genericCutPlane_cartier
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    ∃ hpC : p ∈ C.toIdeal,
      Nonempty (PfaffianDescent.RegularPrincipalImmersion
        (wholeGenericCutPlaneImmersion C p hp hpC)) := by
  have hpC : p ∈ C.toIdeal := by
    apply hCmin.le
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (Set.mem_insert p {q})
  exact ⟨hpC, selectedOriginalWholeCurve_genericCutPlane_regularPrincipalImmersion
    p q hp hp0 n hq hnot C hCmin hpC⟩

end PfaffianDescent.Coray
