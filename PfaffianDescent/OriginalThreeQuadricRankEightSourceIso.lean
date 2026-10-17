import PfaffianDescent.FiniteClosedImmersionRank
import AllCharacteristics.SectionFour

/-! SOURCE ONLY / UNVERIFIED. Original rank-eight closed subscheme
nonemptiness and source-isomorphism lemmas, independent of the cubic H0
dictionary. The two complete declarations below are moved unchanged from
ActualP3ThreeQuadricCubicGlobalIso; no new source or rank certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- The SAME original rank-eight closed scheme makes the actual triple
nonempty, with no chosen point or geometric comparison premise. -/
theorem p3ThreeQuadricOriginalLift_nonempty
    (f g h : PS 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property)) [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank
      (l ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal
        f.val g.val h.val f.property g.property h.property)) = 8) :
    Nonempty (scheme (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property)) := by
  let T := tripleCompleteIntersectionHomogeneousIdeal f.val g.val h.val
    f.property g.property h.property
  obtain ⟨z, hz⟩ := AllCharacteristics.exists_effectiveZeroCycle_degree_finiteSchemeRank
    (l ≫ toBase T)
  obtain ⟨x, _, _⟩ := AllCharacteristics.EffectiveZeroCycle.exists_coprime_degree
    (l ≫ toBase T) z (by rw [hz, hZ]; norm_num)
  exact Nonempty.map l ⟨x.1⟩

/-- Scheme equality is derived from actual length eight, retaining nilpotents. -/
theorem p3ThreeQuadricOriginalLift_isIso
    (f g h : PS 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property)) [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank
      (l ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal
        f.val g.val h.val f.property g.property h.property)) = 8) : IsIso l := by
  let T := tripleCompleteIntersectionHomogeneousIdeal f.val g.val h.val
    f.property g.property h.property
  have hT := p3ThreeQuadricOriginalLift_nonempty f g h l hZ
  have hseq := AllCharacteristics.sectionFour_triple_quadrics_isRegular_of_finite_of_nonempty
    f.val g.val h.val f.property g.property h.property hT
  have hT8 : AllCharacteristics.finiteSchemeRank (toBase T) = 8 :=
    triple_quadrics_intersection_length_eight_of_regular_sequence
      f.val g.val h.val f.property g.property h.property hseq
  exact isIso_of_finite_closedImmersion_of_finiteSchemeRank_eq
    l (toBase T) (hZ.trans hT8.symm)

end PfaffianDescent
