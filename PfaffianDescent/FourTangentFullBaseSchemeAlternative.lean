import PfaffianDescent.QuarticNonexceptionalFullBaseFinite
import PfaffianDescent.QuarticExceptionalTwistedCubicPresentation
import PfaffianDescent.FiniteClosedImmersionRank
import AllCharacteristics.SectionFour

/-! The FULL tangent-quadric base scheme: in the finite branch its canonical
closed immersion from the four actual dual-number points is an isomorphism.
The other branch is the actual embedded twisted-cubic homogeneous ideal. -/

noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem skewTangentDirections_diagonal_zero (a b c d e f : K) :
    ∀ i, skewTangentDirections a b c d e f i i = 0 := by
  intro i
  fin_cases i <;> simp [skewTangentDirections]

theorem skewTangentDirections_rows_nonzero
    (a b c d e f : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∀ i, ∃ j, skewTangentDirections a b c d e f i j ≠ 0 := by
  intro i
  fin_cases i
  · exact ⟨1, by simpa [skewTangentDirections] using ha⟩
  · exact ⟨0, by simpa [skewTangentDirections] using neg_ne_zero.mpr ha⟩
  · exact ⟨0, by simpa [skewTangentDirections] using neg_ne_zero.mpr hb⟩
  · exact ⟨0, by simpa [skewTangentDirections] using neg_ne_zero.mpr hc⟩

/-- Equality with the generated triple is derived from the FULL actual
quadratic dual-evaluation kernel. -/
theorem fourTangentFullBase_eq_triple
    (a b c d e f : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    fourTangentFullQuadraticBaseIdeal (skewTangentDirections a b c d e f) =
      tripleCompleteIntersectionHomogeneousIdeal
        (scaledBaseLocusQuadricPolynomials a b c d e f 0)
        (scaledBaseLocusQuadricPolynomials a b c d e f 1)
        (scaledBaseLocusQuadricPolynomials a b c d e f 2)
        (scaledBaseLocusQuadricPolynomials_homogeneous a b c d e f 0)
        (scaledBaseLocusQuadricPolynomials_homogeneous a b c d e f 1)
        (scaledBaseLocusQuadricPolynomials_homogeneous a b c d e f 2) := by
  apply HomogeneousIdeal.toIdeal_injective
  rw [fourTangentFullQuadraticBaseIdeal_eq_scaled_ideal a b c d e f ha hb hc]
  change Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f)) =
    Ideal.span ({scaledBaseLocusQuadricPolynomials a b c d e f 0,
      scaledBaseLocusQuadricPolynomials a b c d e f 1,
      scaledBaseLocusQuadricPolynomials a b c d e f 2} : Set (MvPolynomial (Fin 4) K))
  congr 1
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl | rfl)
    · exact Set.mem_range_self 0
    · exact Set.mem_range_self 1
    · exact Set.mem_range_self 2

/-- The canonical map itself is an isomorphism, so the finite base scheme is
exactly the four specified tangent double points, including their nilpotents. -/
theorem nonexceptional_fourTangentDualToFullBase_isIso [IsAlgClosed K]
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f ≠ 0) :
    IsIso (fourTangentDualToFullBase (skewTangentDirections a b c d e f)) := by
  let U := skewTangentDirections a b c d e f
  let I := fourTangentFullQuadraticBaseIdeal U
  let l := fourTangentDualToFullBase U
  let Q := scaledBaseLocusQuadricPolynomials a b c d e f
  let hQ := scaledBaseLocusQuadricPolynomials_homogeneous a b c d e f
  have hI : I = tripleCompleteIntersectionHomogeneousIdeal
      (Q 0) (Q 1) (Q 2) (hQ 0) (hQ 1) (hQ 2) :=
    fourTangentFullBase_eq_triple a b c d e f ha hb hc
  letI : IsFinite (toBase I) :=
    nonexceptional_fourTangentFullBase_isFinite a b c d e f ha hb hc hd he hdelta
  letI : IsClosedImmersion l := fourTangentDualToFullBase_isClosedImmersion U
    (skewTangentDirections_diagonal_zero a b c d e f)
    (skewTangentDirections_rows_nonzero a b c d e f ha hb hc)
  have hnonempty : Nonempty (scheme I) := Nonempty.map l inferInstance
  have hTfinite : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (Q 0) (Q 1) (Q 2) (hQ 0) (hQ 1) (hQ 2))) := by
    rw [← hI]
    infer_instance
  letI := hTfinite
  have hTnonempty : Nonempty (scheme (tripleCompleteIntersectionHomogeneousIdeal
      (Q 0) (Q 1) (Q 2) (hQ 0) (hQ 1) (hQ 2))) := by
    rw [← hI]
    exact hnonempty
  have hseq := AllCharacteristics.sectionFour_triple_quadrics_isRegular_of_finite_of_nonempty
    (Q 0) (Q 1) (Q 2) (hQ 0) (hQ 1) (hQ 2) hTnonempty
  have hI8 : AllCharacteristics.finiteSchemeRank (toBase I) = 8 := by
    have transfer (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
        (hEq : I = J) [IsFinite (toBase J)] :
        AllCharacteristics.finiteSchemeRank (toBase J) = 8 →
          AllCharacteristics.finiteSchemeRank (toBase I) = 8 := by
      subst J
      exact fun h => h
    exact transfer _ hI
      (triple_quadrics_intersection_length_eight_of_regular_sequence
        (Q 0) (Q 1) (Q 2) (hQ 0) (hQ 1) (hQ 2) hseq)
  apply isIso_of_finite_closedImmersion_of_finiteSchemeRank_eq l (toBase I)
  rw [AllCharacteristics.finiteSchemeRank_eq_finrank,
    fourTangentDualToFullBase_toBase, Scheme.Hom.finrank_SpecMap_algebraMap]
  exact (congrFun (Module.rankAtStalk_eq_finrank_of_free
    (R := K) (M := FourTangentDualAlgebra K)) _).trans
    (fourTangentDualAlgebra_finrank.trans hI8.symm)

/-- The exceptional ideal is also the FULL tangent quadratic base ideal. -/
theorem exceptional_fourTangentFullBase_groundPresentation
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0) :
    GroundTwistedCubicPresentation
      (fourTangentFullQuadraticBaseIdeal (skewTangentDirections a b c d e f)) := by
  have hI : fourTangentFullQuadraticBaseIdeal (skewTangentDirections a b c d e f) =
      exceptionalTwistedCubicHomogeneousIdeal a b c d e f := by
    apply HomogeneousIdeal.toIdeal_injective
    exact fourTangentFullQuadraticBaseIdeal_eq_scaled_ideal a b c d e f ha hb hc
  rw [hI]
  exact exceptionalTwistedCubic_groundPresentation a b c d e f ha hb hc hd he hdelta

/-- The scheme-theoretic disjunction in the geometric base-locus lemma.
Every input is a scalar tangent-coordinate hypothesis; the finite branch
asserts that the canonical four-double-point closed immersion is an ISO. -/
theorem fourTangentFullQuadraticBase_scheme_alternative [IsAlgClosed K]
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (_hf : f ≠ 0) :
    IsIso (fourTangentDualToFullBase (skewTangentDirections a b c d e f)) ∨
      GroundTwistedCubicPresentation
        (fourTangentFullQuadraticBaseIdeal (skewTangentDirections a b c d e f)) := by
  by_cases hdelta : baseLocusDelta a b c d e f = 0
  · exact Or.inr (exceptional_fourTangentFullBase_groundPresentation
      a b c d e f ha hb hc hd he hdelta)
  · exact Or.inl (nonexceptional_fourTangentDualToFullBase_isIso
      a b c d e f ha hb hc hd he hdelta)

end PfaffianDescent.QuarticNet
