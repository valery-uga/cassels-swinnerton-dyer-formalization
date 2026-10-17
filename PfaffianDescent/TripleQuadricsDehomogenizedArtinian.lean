import PfaffianDescent.TripleQuadricsFiniteChartArtinian
import AllCharacteristics.PolynomialCoordinateOne
import AllCharacteristics.CoordinateCharts

/-!
# Dehomogenized finite charts of three-quadric intersections

The quotient by three homogeneous equations together with `X_j - 1` is
identified with the quotient of a three-variable polynomial ring by their
dehomogenizations.  Hence a finite projective three-quadric intersection has
Artinian dehomogenized coordinate quotients.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

section

variable {K : Type u} [Field K] {a b c : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The three equations after setting the `j`-th homogeneous coordinate to
one and eliminating it. -/
noncomputable def tripleCompleteIntersectionDehomogenizedIdeal
    (p q r : MvPolynomial (Fin 4) K) (j : Fin 4) :
    Ideal (MvPolynomial {i : Fin 4 // i ≠ j} K) :=
  Ideal.span {coordinateOneEvaluation j p, coordinateOneEvaluation j q,
    coordinateOneEvaluation j r}

private theorem map_coordinateOne_threeGeneratorIdeal
    (p q r : MvPolynomial (Fin 4) K) (j : Fin 4) :
    Ideal.map (coordinateOneQuotientEquiv (R := K) j).toRingHom
      ((Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K))).map
        (Ideal.Quotient.mk (coordinateOneIdeal j))) =
      tripleCompleteIntersectionDehomogenizedIdeal p q r j := by
  rw [Ideal.map_map, Ideal.map_span]
  apply congrArg Ideal.span
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with hy | hy | hy
    · subst y
      exact Or.inl (by
        change coordinateOneQuotientEquiv j
          (Ideal.Quotient.mk (coordinateOneIdeal j) p) = coordinateOneEvaluation j p
        exact coordinateOneQuotientEquiv_mk j p)
    · subst y
      exact Or.inr (Or.inl (by
        change coordinateOneQuotientEquiv j
          (Ideal.Quotient.mk (coordinateOneIdeal j) q) = coordinateOneEvaluation j q
        exact coordinateOneQuotientEquiv_mk j q))
    · subst y
      exact Or.inr (Or.inr (by
        change coordinateOneQuotientEquiv j
          (Ideal.Quotient.mk (coordinateOneIdeal j) r) = coordinateOneEvaluation j r
        exact coordinateOneQuotientEquiv_mk j r))
  · intro hx
    rcases hx with hx | hx | hx
    · refine ⟨p, Or.inl rfl, ?_⟩
      change (coordinateOneQuotientEquiv (R := K) j).toRingHom.comp
          (Ideal.Quotient.mk (coordinateOneIdeal j)) p = _
      have hp' : coordinateOneQuotientEquiv j
          (Ideal.Quotient.mk (coordinateOneIdeal j) p) = coordinateOneEvaluation j p := by
        exact coordinateOneQuotientEquiv_mk j p
      exact hp'.trans hx.symm
    · refine ⟨q, Or.inr (Or.inl rfl), ?_⟩
      change (coordinateOneQuotientEquiv (R := K) j).toRingHom.comp
          (Ideal.Quotient.mk (coordinateOneIdeal j)) q = _
      have hq' : coordinateOneQuotientEquiv j
          (Ideal.Quotient.mk (coordinateOneIdeal j) q) = coordinateOneEvaluation j q := by
        exact coordinateOneQuotientEquiv_mk j q
      exact hq'.trans hx.symm
    · refine ⟨r, Or.inr (Or.inr rfl), ?_⟩
      change (coordinateOneQuotientEquiv (R := K) j).toRingHom.comp
          (Ideal.Quotient.mk (coordinateOneIdeal j)) r = _
      have hr' : coordinateOneQuotientEquiv j
          (Ideal.Quotient.mk (coordinateOneIdeal j) r) = coordinateOneEvaluation j r := by
        exact coordinateOneQuotientEquiv_mk j r
      exact hr'.trans hx.symm

/-- Eliminating the distinguished coordinate identifies the four-relation
chart quotient with the quotient by the three dehomogenized equations. -/
noncomputable def tripleCompleteIntersection_dehomogenizedQuotientEquiv
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (j : Fin 4) :
    (MvPolynomial (Fin 4) K ⧸
      Ideal.span (Set.range (tripleCompleteIntersectionChartRelations p q r j))) ≃+*
      (MvPolynomial {i : Fin 4 // i ≠ j} K ⧸
        tripleCompleteIntersectionDehomogenizedIdeal p q r j) := by
  let I : Ideal (MvPolynomial (Fin 4) K) := coordinateOneIdeal j
  let J : Ideal (MvPolynomial (Fin 4) K) := Ideal.span {p, q, r}
  have hrelations' : Ideal.span (Set.range (tripleCompleteIntersectionChartRelations p q r j)) =
      coordinateOneIdeal j ⊔ Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K)) := by
    rw [span_range_tripleCompleteIntersectionChartRelations p q r hp hq hr j,
      chartPresentationIdeal, tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
      tripleCompleteIntersectionIdeal]
    change (Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K)) ⊔ coordinateOneIdeal j) =
      coordinateOneIdeal j ⊔ Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K))
    apply le_antisymm
    · exact sup_le le_sup_right le_sup_left
    · exact sup_le le_sup_right le_sup_left
  have hrelations : Ideal.span (Set.range (tripleCompleteIntersectionChartRelations p q r j)) =
      I ⊔ J := by
    simpa only [I, J] using hrelations'
  have hmap : Ideal.map (coordinateOneQuotientEquiv (R := K) j).toRingHom
      (J.map (Ideal.Quotient.mk I)) =
      tripleCompleteIntersectionDehomogenizedIdeal p q r j := by
    exact map_coordinateOne_threeGeneratorIdeal p q r j
  exact (Ideal.quotEquivOfEq hrelations).trans
    ((DoubleQuot.quotQuotEquivQuotSup I J).symm.trans
      (Ideal.quotientEquiv (J.map (Ideal.Quotient.mk I))
        (tripleCompleteIntersectionDehomogenizedIdeal p q r j)
        (coordinateOneQuotientEquiv (R := K) j).toRingEquiv hmap.symm))

/-- Each dehomogenized three-quadric chart is Artinian whenever the
projective intersection is finite. -/
theorem tripleCompleteIntersection_dehomogenized_isArtinian_of_finite
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (j : Fin 4) :
    IsArtinianRing (MvPolynomial {i : Fin 4 // i ≠ j} K ⧸
      tripleCompleteIntersectionDehomogenizedIdeal p q r j) := by
  letI : IsArtinianRing (MvPolynomial (Fin 4) K ⧸
      Ideal.span (Set.range (tripleCompleteIntersectionChartRelations p q r j))) :=
    tripleCompleteIntersection_chartRelations_isArtinian_of_finite p q r hp hq hr j
  exact (tripleCompleteIntersection_dehomogenizedQuotientEquiv p q r hp hq hr j).isArtinianRing

/-- A nonempty projective three-quadric intersection has a nonempty standard
affine chart.  Equivalently, the corresponding dehomogenized ideal is proper
on at least one chart. -/
theorem exists_tripleCompleteIntersection_dehomogenized_proper_of_nonempty
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (hX : Nonempty (scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ j : Fin 4, tripleCompleteIntersectionDehomogenizedIdeal p q r j ≠ ⊤ := by
  classical
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let x : scheme I := Classical.choice (by simpa [I] using hX)
  obtain ⟨j, y, _⟩ := exists_coordinate_chart I x
  have hchart : Nontrivial (ChartRing I j) := PrimeSpectrum.nontrivial y
  letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : Nontrivial (ChartRing I j) := hchart
  let e₁ : (MvPolynomial (Fin 4) K ⧸
      Ideal.span (Set.range (tripleCompleteIntersectionChartRelations p q r j))) ≃+*
      ChartRing I j :=
    (tripleCompleteIntersectionChartRelationsEquiv p q r hp hq hr j).toRingEquiv
  letI : Nontrivial (MvPolynomial (Fin 4) K ⧸
      Ideal.span (Set.range (tripleCompleteIntersectionChartRelations p q r j))) :=
    Equiv.nontrivial e₁.toEquiv
  let e₂ := tripleCompleteIntersection_dehomogenizedQuotientEquiv p q r hp hq hr j
  letI : Nontrivial (MvPolynomial {i : Fin 4 // i ≠ j} K ⧸
      tripleCompleteIntersectionDehomogenizedIdeal p q r j) :=
    Equiv.nontrivial e₂.symm.toEquiv
  exact ⟨j, Ideal.Quotient.nontrivial_iff.mp inferInstance⟩

end

end PfaffianDescent
