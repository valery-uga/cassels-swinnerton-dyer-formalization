import PfaffianDescent.FiniteClosedImmersionStalkQuotientDegree
import PfaffianDescent.CorayActualWholeGenericCutFinite
import PfaffianDescent.CorayWholeGenericCutImmersion

/-! SOURCE ONLY / UNVERIFIED157. ORIGINAL p,q,C construct the canonical
whole-cut cycle on SAME actual E, its degree m and actual ambient quotient
length coefficients. No Cartier, degree comparison, reducedness or constants
rank premise is supplied. Cartier156 makes this cycle the actual divisor
cycle; a line-bundle degree/Euler comparison is still a separate obligation. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial AllCharacteristics
open AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem iso_inverse_toBase157
    {𝒞 : Type*} [Category 𝒞] {E P B : 𝒞}
    (e : E ≅ P) (p : P ⟶ B) (q : E ⟶ B) (h : e.hom ≫ p = q) :
    e.inv ≫ q = p := by
  exact (congrArg (fun a => e.inv ≫ a) h.symm).trans
    ((Category.assoc e.inv e.hom p).symm.trans
      ((congrArg (fun a => a ≫ p) e.inv_hom_id).trans (Category.id_comp p)))

/-- The actual whole Z→SAME E immersion commutes with the actual original
parameter-field structure maps. The proof only composes the accepted
pair-triangle structure equality; it does not unfold Proj maps. -/
theorem wholeGenericCutPlaneImmersion_toBase
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpC : p ∈ C.toIdeal) :
    wholeGenericCutPlaneImmersion C p hp hpC ≫
      hypersurfaceToBase
        (PfaffianDescent.rectangularSubstitution (genericPlaneInclusionMatrix (K := K))
          (p.map (algebraMap K (GenericHyperplaneField K))))
        (PfaffianDescent.rectangularSubstitution_homogeneous
          (genericPlaneInclusionMatrix (K := K)) (hp.map _)) =
      toBase (wholeGenericCutIdeal C) := by
  have hinv := iso_inverse_toBase157 (actualGenericPlanePairSchemeIso p hp)
    (toBase (genericPlaneSectionPairIdeal p hp)) _
    (actualGenericPlanePairSchemeIso_hom_toBase p hp)
  change (wholeGenericCutPairImmersion C p hp hpC ≫
    (actualGenericPlanePairSchemeIso p hp).inv) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => wholeGenericCutPairImmersion C p hp hpC ≫ a) hinv).trans
      (wholeGenericCutPairImmersion_toBase C p hp hpC))

/-- Original smooth cubic/minimal-curve input produces degree m for the
canonical entire finite-cut fundamental cycle. The displayed sum uses
actual full residue degrees and actual nilpotent stalk lengths. -/
theorem selectedOriginalWholeCurve_genericCut_fundamentalCycle_degree_and_lengths
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    ∃ hfinite : IsFinite (toBase (wholeGenericCutIdeal C)),
      letI := hfinite
      EffectiveZeroCycle.degree (toBase (wholeGenericCutIdeal C))
        (PfaffianDescent.finiteSchemeFundamentalCycle (toBase (wholeGenericCutIdeal C))) =
          actualCurveCoordinateHilbertDegree C ∧
      (letI := PfaffianDescent.finiteScheme_isArtinian (toBase (wholeGenericCutIdeal C))
       letI : Fintype (closedPoints (scheme (wholeGenericCutIdeal C))) := Fintype.ofFinite _
       (∑ x : closedPoints (scheme (wholeGenericCutIdeal C)),
         (Module.length ((scheme (wholeGenericCutIdeal C)).presheaf.stalk x.val)
           ((scheme (wholeGenericCutIdeal C)).presheaf.stalk x.val)).toNat *
             (toBase (wholeGenericCutIdeal C)).residueDegree x.val) =
         actualCurveCoordinateHilbertDegree C) := by
  classical
  obtain ⟨hfinite, hrank, _hcartier, _hgrades⟩ :=
    selectedOriginalWholeCurve_genericCut_finite_rank_degree p q hp hp0 n hq hnot C hCmin
  letI := hfinite
  have hdegree := (PfaffianDescent.finiteSchemeFundamentalCycle_degree
    (toBase (wholeGenericCutIdeal C))).trans hrank
  refine ⟨hfinite, hdegree, ?_⟩
  letI := PfaffianDescent.finiteScheme_isArtinian (toBase (wholeGenericCutIdeal C))
  letI : Fintype (closedPoints (scheme (wholeGenericCutIdeal C))) := Fintype.ofFinite _
  exact (fundamentalZeroCycle_degree_eq_sum (toBase (wholeGenericCutIdeal C))).symm.trans hdegree

/-- ORIGINAL input constructs the SAME E cycle canonically from the entire
finite Z, proves degree m, and identifies all image coefficients with full
ambient stalk-quotient lengths. The final finite sum uses E's own residue
degrees. No supplied finite/Cartier/degree or scheme-comparison certificate. -/
theorem selectedOriginalWholeCurve_sameE_entireDivisorCycle_degree_and_lengths
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    ∃ hpC : p ∈ C.toIdeal,
    ∃ hfinite : IsFinite (toBase (wholeGenericCutIdeal C)),
      letI := hfinite
      let E := PfaffianDescent.linearHypersurfaceSection (genericPlaneInclusionMatrix (K := K))
        (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)
      let i := wholeGenericCutPlaneImmersion C p hp hpC
      let pi := hypersurfaceToBase
        (PfaffianDescent.rectangularSubstitution (genericPlaneInclusionMatrix (K := K))
          (p.map (algebraMap K (GenericHyperplaneField K))))
        (PfaffianDescent.rectangularSubstitution_homogeneous
          (genericPlaneInclusionMatrix (K := K)) (hp.map _))
      let z := pushforwardClosedCycle i
        (PfaffianDescent.finiteSchemeFundamentalCycle (toBase (wholeGenericCutIdeal C)))
      EffectiveZeroCycle.degree pi z = actualCurveCoordinateHilbertDegree C ∧
      (∀ x : closedPoints (scheme (wholeGenericCutIdeal C)),
        z (closedPointMap i x) =
          (Module.length (E.presheaf.stalk (i x.val))
            (E.presheaf.stalk (i x.val) ⧸ RingHom.ker (i.stalkMap x.val).hom)).toNat) ∧
      (∀ x : scheme (wholeGenericCutIdeal C),
        IsFiniteLength (E.presheaf.stalk (i x))
          (E.presheaf.stalk (i x) ⧸ RingHom.ker (i.stalkMap x).hom)) ∧
      (letI := PfaffianDescent.finiteScheme_isArtinian (toBase (wholeGenericCutIdeal C))
       letI : Fintype (closedPoints (scheme (wholeGenericCutIdeal C))) := Fintype.ofFinite _
       (∑ x : closedPoints (scheme (wholeGenericCutIdeal C)),
         (Module.length (E.presheaf.stalk (i x.val))
           (E.presheaf.stalk (i x.val) ⧸ RingHom.ker (i.stalkMap x.val).hom)).toNat *
             pi.residueDegree (i x.val)) = actualCurveCoordinateHilbertDegree C) := by
  classical
  have hpC : p ∈ C.toIdeal := by
    apply hCmin.le
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (by simp)
  obtain ⟨hfinite, hrank, _hcartier, _hgrades⟩ :=
    selectedOriginalWholeCurve_genericCut_finite_rank_degree p q hp hp0 n hq hnot C hCmin
  letI := hfinite
  refine ⟨hpC, hfinite, ?_, ?_, ?_, ?_⟩
  · exact (PfaffianDescent.finiteFundamentalCycle_pushforward_degree_eq_nativeRank
      (wholeGenericCutPlaneImmersion C p hp hpC) _ (toBase (wholeGenericCutIdeal C))
      (wholeGenericCutPlaneImmersion_toBase C p hp hpC)).trans hrank
  · intro x
    exact PfaffianDescent.finiteFundamentalCycle_pushforward_apply_entireStalkQuotient
      (wholeGenericCutPlaneImmersion C p hp hpC) (toBase (wholeGenericCutIdeal C)) x
  · intro x
    exact PfaffianDescent.finiteClosedImmersion_entireStalkQuotient_isFiniteLength
      (wholeGenericCutPlaneImmersion C p hp hpC) (toBase (wholeGenericCutIdeal C)) x
  · exact (PfaffianDescent.finiteClosedImmersion_entireStalkQuotient_weighted_sum_eq_nativeRank
      (wholeGenericCutPlaneImmersion C p hp hpC) _ (toBase (wholeGenericCutIdeal C))
      (wholeGenericCutPlaneImmersion_toBase C p hp hpC)).trans hrank

end PfaffianDescent.Coray
