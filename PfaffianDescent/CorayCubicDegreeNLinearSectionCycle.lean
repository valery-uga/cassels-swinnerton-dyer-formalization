import PfaffianDescent.CorayCubicDegreeNLinearSectionLength
import PfaffianDescent.CorayProjectiveIntersectionChartDimension
import PfaffianDescent.HomogeneousQuotientMap
import AllCharacteristics.FiniteSchemeCycle

/-! Genuine cycle of the ACTUAL cubic--degree-n--linear section, on the
SAME original p/q curve. Native finite-scheme fundamental-cycle lengths
retain multiplicities and full original-K residues. The original linear
equation's nonzerodivisor hypothesis is explicit; hyperplane selection and
regularity of its support are NOT proved here. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory AllCharacteristics
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubic_degree_n_linear_section_curveIdeal_le
    (p q H : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous n) (hH : H.IsHomogeneous 1) :
    (projectiveIntersectionIdeal p q hp hq).toIdeal ≤
      (tripleCompleteIntersectionHomogeneousIdeal p q H hp hq hH).toIdeal := by
  rw [projectiveIntersectionIdeal_toIdeal]
  change Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤
    Ideal.span ({p, q, H} : Set (MvPolynomial (Fin 4) K))
  apply Ideal.span_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

/-- The literal linear section's SAME quotient immersion into SAME p/q
curve; no chosen replacement or field transport. -/
def cubic_degree_n_linear_section_curveImmersion
    (p q H : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous n) (hH : H.IsHomogeneous 1) :
    scheme (tripleCompleteIntersectionHomogeneousIdeal p q H hp hq hH) ⟶
      scheme (projectiveIntersectionIdeal p q hp hq) :=
  schemeQuotientMap (projectiveIntersectionIdeal p q hp hq)
    (tripleCompleteIntersectionHomogeneousIdeal p q H hp hq hH)
    (cubic_degree_n_linear_section_curveIdeal_le p q H hp hq hH)

theorem cubic_degree_n_linear_section_curveImmersion_isClosedImmersion
    (p q H : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous n) (hH : H.IsHomogeneous 1) :
    IsClosedImmersion (cubic_degree_n_linear_section_curveImmersion p q H hp hq hH) :=
  schemeQuotientMap_closedImmersion (projectiveIntersectionIdeal p q hp hq)
    (tripleCompleteIntersectionHomogeneousIdeal p q H hp hq hH)
    (cubic_degree_n_linear_section_curveIdeal_le p q H hp hq hH)

theorem cubic_degree_n_linear_section_curveImmersion_toBase
    (p q H : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous n) (hH : H.IsHomogeneous 1) :
    cubic_degree_n_linear_section_curveImmersion p q H hp hq hH ≫
      toBase (projectiveIntersectionIdeal p q hp hq) =
        toBase (tripleCompleteIntersectionHomogeneousIdeal p q H hp hq hH) :=
  schemeQuotientMap_toBase (projectiveIntersectionIdeal p q hp hq)
    (tripleCompleteIntersectionHomogeneousIdeal p q H hp hq hH)
    (cubic_degree_n_linear_section_curveIdeal_le p q H hp hq hH)

/-- Construct the ACTUAL effective section cycle on SAME original curve,
with degree3*n derived internally. Its nonreduced multiplicities come from
the finite scheme's own affine fundamental cycle, not a reduced point set. -/
theorem cubic_degree_n_linear_section_exists_curve_cycle_degree_three_mul [Infinite K]
    (p q H : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous n) (hH : H.IsHomogeneous 1)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      H * x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) :
    ∃ z : EffectiveZeroCycle (scheme (projectiveIntersectionIdeal p q hp hq)),
      EffectiveZeroCycle.degree (toBase (projectiveIntersectionIdeal p q hp hq)) z = 3 * n := by
  classical
  let J := tripleCompleteIntersectionHomogeneousIdeal p q H hp hq hH
  let I := projectiveIntersectionIdeal p q hp hq
  let i := cubic_degree_n_linear_section_curveImmersion p q H hp hq hH
  letI : IsClosedImmersion i :=
    cubic_degree_n_linear_section_curveImmersion_isClosedImmersion p q H hp hq hH
  letI : IsFinite (toBase J) :=
    cubic_degree_n_linear_section_finite p q H hp hq hH hp0 hq0 hrel hregular
  obtain ⟨zJ, hdegree⟩ := exists_effectiveZeroCycle_degree_finiteSchemeRank (toBase J)
  refine ⟨pushforwardClosedCycle i zJ, ?_⟩
  rw [degree_pushforwardClosedCycle]
  have hbase : i ≫ toBase I = toBase J :=
    cubic_degree_n_linear_section_curveImmersion_toBase p q H hp hq hH
  rw [hbase, hdegree]
  exact cubic_degree_n_linear_section_length_three_mul p q H hp hq hH hp0 hq0 hrel hregular

end PfaffianDescent.Coray
