import PfaffianDescent.TripleCompleteIntersectionJacobian
import PfaffianDescent.UnramifiedSquarePresentation
import PfaffianDescent.VoisinCubicTwoQuadricSingularScheme
import PfaffianDescent.HomogeneousQuotientMap
import PfaffianDescent.ProjectiveCoordinateNilpotentEmpty
import PfaffianDescent.VoisinQuadraticJacobianUniversalFamily
import PfaffianDescent.LinearNormalizedProjectivePoint
import PfaffianDescent.VoisinQuadraticSingularChartBadLocusCriterion

/-!
# Étaleness forces the complete-intersection Jacobian to be invertible

The existing Jacobian criterion constructs an étale projective intersection
from units on all four normalized charts.  Here we prove its converse for
the square three-equation chart presentation.  This lets an independently
constructed reduced twelve-point intersection supply the same Jacobian
certificate used by the degree-eight restriction-kernel family.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- On each normalized chart of a projective three-equation intersection,
étaleness over the coefficient field forces the square Jacobian determinant
to be a unit. -/
theorem tripleCompleteIntersectionChartJacobian_isUnit_of_etale
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hr : r.IsHomogeneous c)
    [hEtale : Etale
      (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (j : Fin 4) :
    IsUnit (tripleCompleteIntersectionChartJacobian p q r hp hq hr j) := by
  let J := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let S := ChartRing J j
  letI : Algebra K S := (chartBaseMap J j).toAlgebra
  haveI : Etale (chartι J j ≫ toBase J) := inferInstance
  have hChart : Etale (Spec.map (CommRingCat.ofHom (chartBaseMap J j))) := by
    simpa only [chartι_toBase] using
      (inferInstance : Etale (chartι J j ≫ toBase J))
  haveI : Algebra.Etale K S := by
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp hChart
  let P := tripleCompleteIntersectionChartPrePresentation p q r hp hq hr j
  have hP : IsUnit P.jacobian :=
    presentation_jacobian_isUnit_of_unramified P
  simpa only [P, tripleCompleteIntersectionChartPrePresentation_jacobian] using hP

/-- For the square projective complete-intersection presentation, all chart
Jacobian determinants are units exactly when the intersection is étale. -/
theorem tripleCompleteIntersection_etale_iff_chartJacobian_isUnit
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hr : r.IsHomogeneous c) :
    Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ↔
      ∀ j : Fin 4,
        IsUnit (tripleCompleteIntersectionChartJacobian p q r hp hq hr j) := by
  constructor
  · intro hEtale j
    letI : Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
      p q r hp hq hr)) := hEtale
    exact tripleCompleteIntersectionChartJacobian_isUnit_of_etale
      p q r hp hq hr j
  · exact etale_tripleCompleteIntersection_toBase_of_chartJacobian_isUnit
      p q r hp hq hr

/-- The mixed-degree singular homogeneous ideal contains the underlying
three-equation ideal. -/
theorem cubicTwoQuadric_intersectionIdeal_le_singularIdeal
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) :
    (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr).toIdeal ≤
      (cubicTwoQuadricSingularHomogeneousIdeal p q r hp hq hr).toIdeal := by
  rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
    tripleCompleteIntersectionIdeal,
    cubicTwoQuadricSingularHomogeneousIdeal_toIdeal,
    cubicTwoQuadricSingularIdeal, Ideal.span_le]
  intro s hs
  apply Ideal.subset_span
  exact Or.inl hs

/-- A unit Jacobian on every normalized chart rules out all points of the
projective singular scheme. -/
theorem cubicTwoQuadric_singularScheme_isEmpty_of_chartJacobian_isUnit
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (hunit : ∀ j : Fin 4,
      IsUnit (tripleCompleteIntersectionChartJacobian p q r hp hq hr j)) :
    IsEmpty (scheme (cubicTwoQuadricSingularHomogeneousIdeal p q r hp hq hr)) := by
  let J := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let I := cubicTwoQuadricSingularHomogeneousIdeal p q r hp hq hr
  have hJI : J.toIdeal ≤ I.toIdeal :=
    cubicTwoQuadric_intersectionIdeal_le_singularIdeal p q r hp hq hr
  refine ⟨fun s => ?_⟩
  obtain ⟨j, y, _hy⟩ := exists_coordinate_chart I s
  let F := tripleCompleteIntersectionChartJacobianPolynomial p q r j
  have hFmem : F ∈ I.toIdeal := by
    change F ∈ cubicTwoQuadricSingularIdeal p q r
    apply Ideal.subset_span
    exact Or.inr ⟨j, rfl⟩
  have hzero : F.eval₂ (chartBaseMap I j) (chartCoordinate I j) = 0 :=
    eval₂_chartCoordinate_eq_zero_of_mem I j F hFmem
  have hunitI : IsUnit (F.eval₂ (chartBaseMap I j) (chartCoordinate I j)) := by
    rw [← chartQuotientMap_eval₂ J I hJI j F]
    exact (hunit j).map (chartQuotientMap J I hJI j)
  letI : Nontrivial (ChartRing I j) := PrimeSpectrum.nontrivial y
  exact not_isUnit_zero (hzero ▸ hunitI)

/-- For a cubic and two quadrics, the projective intersection is étale
exactly when its explicit simultaneous Jacobian singular scheme is empty. -/
theorem cubicTwoQuadric_etale_iff_singularScheme_isEmpty
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) :
    Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ↔
      IsEmpty (scheme (cubicTwoQuadricSingularHomogeneousIdeal p q r hp hq hr)) := by
  constructor
  · intro hetale
    exact cubicTwoQuadric_singularScheme_isEmpty_of_chartJacobian_isUnit
      p q r hp hq hr
      ((tripleCompleteIntersection_etale_iff_chartJacobian_isUnit
        p q r hp hq hr).mp hetale)
  · exact etale_cubicTwoQuadric_toBase_of_isEmpty_singularScheme
      p q r hp hq hr

/-- Étaleness of a cubic--quadric--quadric intersection is equivalent to a
finite coordinate-power ideal-membership certificate in its explicit
Jacobian singular ideal. -/
theorem cubicTwoQuadric_etale_iff_coordinatePowers_mem_singularIdeal
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) :
    Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ↔
      ∀ j : Fin 4, ∃ n : ℕ,
        (MvPolynomial.X j : MvPolynomial (Fin 4) K) ^ n ∈
          cubicTwoQuadricSingularIdeal p q r := by
  rw [cubicTwoQuadric_etale_iff_singularScheme_isEmpty]
  exact isEmpty_projectiveScheme_iff_coordinate_powers_mem
    (cubicTwoQuadricSingularHomogeneousIdeal p q r hp hq hr)

/-- The exact field-valued universal singular fiber is empty when its
specialized three-equation intersection is étale. -/
theorem cubicTwoQuadricUniversalSingularChartFiber_isEmpty_of_etale
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L)
    (hEtale :
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
        (p.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (q.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (((cubicTwoQuadricUniversalQuadric v).map
          (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)).map g)
        (hp.map _) (hq.map _)
        ((cubicTwoQuadricUniversalQuadric_isHomogeneous v).map _ |>.map g)))) :
    IsEmpty (scheme (cubicTwoQuadricUniversalSingularChartFiberIdeal
      p q hp hq v i g)) := by
  exact (cubicTwoQuadric_etale_iff_singularScheme_isEmpty
    (p.map (g.comp (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
    (q.map (g.comp (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
    (((cubicTwoQuadricUniversalQuadric v).map
      (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)).map g)
    (hp.map _) (hq.map _)
    ((cubicTwoQuadricUniversalQuadric_isHomogeneous v).map _ |>.map g)).mp hEtale

/-- A normalized nonzero coefficient vector gives a field-valued point of
the standard parameter chart, with precisely those specialized coordinates. -/
theorem exists_quadraticParameterChartHom_of_normalizedCoordinates
    {n : ℕ} (c : Fin n → K) (i : Fin n) (hci : c i = 1) :
    ∃ g : ChartRing
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* K,
      g.comp (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i) =
        RingHom.id K ∧
      ∀ j : Fin n,
        g (chartCoordinate
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i j) = c j := by
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin n) K) := ⊥
  have he : ∀ s ∈ I.toIdeal,
      (eval₂Hom (RingHom.id K) c) s = 0 := by
    intro s hs
    have hs0 : s = 0 := Ideal.mem_bot.mp hs
    subst s
    exact map_zero _
  have hOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (RingHom.id K) c) he) (coordinate I i) = 1 := by
    change (eval₂Hom (RingHom.id K) c) (X i) = 1
    simpa using hci
  let g : ChartRing I i →+* K :=
    linearNormalizedPointChartMapAt I c he (coordinate I i)
      (coordinate_mem I i) hOne
  refine ⟨g, ?_, ?_⟩
  · apply RingHom.ext
    intro a
    exact linearNormalizedPointChartMapAt_base I c he
      (coordinate I i) (coordinate_mem I i) hOne a
  · intro j
    exact linearNormalizedPointChartMapAt_coordinate I c he
      (coordinate I i) (coordinate_mem I i) hOne j

/-- On the normalized source chart, specializing the universal quadric
reproduces the coefficient combination exactly. -/
theorem cubicTwoQuadricUniversalQuadric_specialize_normalizedCoordinates
    {n : ℕ} (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (c : Fin n → K) (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* K)
    (hgbase : g.comp (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i) =
        RingHom.id K)
    (hgcoord : ∀ j : Fin n,
      g (chartCoordinate
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i j) = c j) :
    ((cubicTwoQuadricUniversalQuadric v).map
      (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)).map g =
        ∑ j, C (c j) * (v j).1 := by
  rw [MvPolynomial.map_map,
    cubicTwoQuadricParameterChartCoefficientMap_comp i g]
  have hcomp :
      MvPolynomial.eval₂Hom
        (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i))
        (fun j => g (chartCoordinate
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i j)) =
        MvPolynomial.eval₂Hom (RingHom.id K) c := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simpa [hgbase]
    · intro j
      simpa using hgcoord j
  rw [hcomp, cubicTwoQuadricUniversalQuadric_map]
  apply Finset.sum_congr rfl
  intro j _
  rw [MvPolynomial.map_id]

/-- One étale member of an explicitly framed quadratic system makes the
closed simultaneous-singular parameter locus proper. The member is required
only as a witness, so this avoids any claim about arbitrary degree-eight
data. -/
theorem cubicTwoQuadricUniversalSingularParameterLocus_ne_univ_of_etale_member
    {n : ℕ} (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (c : Fin n → K) (i : Fin n) (hci : c i = 1)
    (hrc : r = ∑ j, C (c j) * (v j).1)
    (hEtale : Etale
      (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    cubicTwoQuadricUniversalSingularParameterLocus p q hp hq v ≠ Set.univ := by
  obtain ⟨g, hgbase, hgcoord⟩ :=
    exists_quadraticParameterChartHom_of_normalizedCoordinates c i hci
  have hpoly :
      ((cubicTwoQuadricUniversalQuadric v).map
        (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)).map g = r := by
    rw [cubicTwoQuadricUniversalQuadric_specialize_normalizedCoordinates
      v c i g hgbase hgcoord]
    exact hrc.symm
  have hpmap :
      p.map (g.comp (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)) = p := by
    rw [hgbase]
    exact MvPolynomial.map_id p
  have hqmap :
      q.map (g.comp (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)) = q := by
    rw [hgbase]
    exact MvPolynomial.map_id q
  have hEtaleFiber :
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
        (p.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (q.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (((cubicTwoQuadricUniversalQuadric v).map
          (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)).map g)
        (hp.map _) (hq.map _)
        ((cubicTwoQuadricUniversalQuadric_isHomogeneous v).map _ |>.map g))) := by
    have hIdeal :
        tripleCompleteIntersectionHomogeneousIdeal
          (p.map (g.comp (chartBaseMap
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
          (q.map (g.comp (chartBaseMap
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
          (((cubicTwoQuadricUniversalQuadric v).map
            (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)).map g)
          (hp.map _) (hq.map _)
          ((cubicTwoQuadricUniversalQuadric_isHomogeneous v).map _ |>.map g) =
        tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr := by
      apply HomogeneousIdeal.ext
      simp only [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
        tripleCompleteIntersectionIdeal, hpmap, hqmap, hpoly]
    rw [hIdeal]
    exact hEtale
  have hEmpty := cubicTwoQuadricUniversalSingularChartFiber_isEmpty_of_etale
    p q hp hq v i g hEtaleFiber
  exact cubicTwoQuadricUniversalSingularParameterLocus_ne_univ_of_fiber_isEmpty
    p q hp hq v i g (fun z => isEmptyElim z)

end PfaffianDescent
