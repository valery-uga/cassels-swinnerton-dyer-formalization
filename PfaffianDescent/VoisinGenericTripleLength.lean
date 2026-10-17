import PfaffianDescent.VoisinGenericTripleFinite
import PfaffianDescent.VoisinGenericTripleSelectedPoints
import PfaffianDescent.VoisinFiniteTripleBezout

/-! The selected generic triple intersection has scheme length twelve. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem relativeTripleIntersection_generic_rank_twelve
    {R : Type u} [CommRing R] [IsDomain R]
    [Infinite (FractionRing R)]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hEight : HasEightDistinctGenericTriplePoints
      p q r hp hq hr ell hell x)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (algebraMap R (FractionRing R)))
      (q.map (algebraMap R (FractionRing R)))
      (r.map (algebraMap R (FractionRing R)))
      (hp.map (algebraMap R (FractionRing R)))
      (hq.map (algebraMap R (FractionRing R)))
      (hr.map (algebraMap R (FractionRing R)))))] :
    let f := algebraMap R (FractionRing R)
    AllCharacteristics.finiteSchemeRank
      (toBase (tripleCompleteIntersectionHomogeneousIdeal
        (p.map f) (q.map f) (r.map f)
        (hp.map f) (hq.map f) (hr.map f))) = 12 := by
  dsimp only
  let f := algebraMap R (FractionRing R)
  obtain ⟨hzero, hnorm, _⟩ := hEight
  have hX : Nonempty (scheme (tripleCompleteIntersectionHomogeneousIdeal
      (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f))) := by
    exact ⟨genericTripleIntersectionSelectedPoints
      p q r hp hq hr ell hell x hzero hnorm 0
        (IsLocalRing.closedPoint (FractionRing R))⟩
  exact cubicTwoQuadrics_finite_nonempty_rank_twelve
    (p.map f) (q.map f) (r.map f)
    (hp.map f) (hq.map f) (hr.map f) hX

/-- A finite neighborhood together with eight selected points gives the
actual generic fiber both finite and length twelve. -/
theorem relativeTripleIntersection_generic_finite_and_rank_twelve
    {R : Type u} [CommRing R] [IsDomain R]
    [Infinite (FractionRing R)]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hEight : HasEightDistinctGenericTriplePoints
      p q r hp hq hr ell hell x)
    (V : (Spec (.of R)).Opens)
    (hη : genericPoint (Spec (.of R)) ∈ V)
    [IsFinite ((relativeTripleIntersectionToBase p q r hp hq hr) ∣_ V)] :
    let f := algebraMap R (FractionRing R)
    ∃ hfin : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
        (p.map f) (q.map f) (r.map f)
        (hp.map f) (hq.map f) (hr.map f))),
      letI := hfin
      AllCharacteristics.finiteSchemeRank
        (toBase (tripleCompleteIntersectionHomogeneousIdeal
          (p.map f) (q.map f) (r.map f)
          (hp.map f) (hq.map f) (hr.map f))) = 12 := by
  dsimp only
  letI := relativeTripleIntersection_generic_isFinite_of_finiteNeighborhood
    p q r hp hq hr V hη
  exact ⟨inferInstance,
    relativeTripleIntersection_generic_rank_twelve
      p q r hp hq hr ell hell x hEight⟩

end PfaffianDescent
