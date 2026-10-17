import PfaffianDescent.TripleQuadricsArbitraryFieldLength
import PfaffianDescent.TripleCompleteIntersectionToHypersurface
import PfaffianDescent.FiniteClosedImmersionRank

/-!
# The degree-eight equality step for a net of quadrics

When a length-eight closed subscheme lies in a regular complete intersection
of three quadrics, the two finite schemes coincide.  This packages the
scheme-theoretic Bézout argument in Lemma 5.2 of `2-proofs.tex`.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

section

variable {K : Type u} [Field K]

/-- Equality of a finite rank-eight three-quadric intersection with any
contained finite rank-eight closed subscheme.  This is the pure
scheme-theoretic degree comparison behind the net-of-quadrics argument; the
regular-sequence calculation is only one way to provide the rank hypothesis. -/
theorem triple_quadrics_lift_isIso_of_finite_rank_eight
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))]
    (hW : AllCharacteristics.finiteSchemeRank
      (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 8)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface f hf) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase f hf)]
    (hker : (tripleCompleteIntersectionToHypersurface f g h hf hg hh).ker ≤ i.ker)
    (hZ : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase f hf) = 8) :
    IsIso (tripleCompleteIntersectionLift f g h hf hg hh i hker) := by
  let j := tripleCompleteIntersectionLift f g h hf hg hh i hker
  have hbase : j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) =
      i ≫ hypersurfaceToBase f hf := by
    rw [← tripleCompleteIntersectionToHypersurface_toBase,
      ← Category.assoc, tripleCompleteIntersectionLift_fac]
  let _ : IsFinite (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) := by
    rw [hbase]
    infer_instance
  apply isIso_of_finite_closedImmersion_of_finiteSchemeRank_eq j
    (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
  have hZ' : AllCharacteristics.finiteSchemeRank (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 8 := by
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank, hbase,
      ← AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact hZ
  rw [hZ', hW]

/-- A length-eight closed subscheme of a regular complete intersection of
three quadrics is the complete intersection itself. -/
theorem triple_quadrics_lift_isIso_of_rank_eight
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2)
    (hh : h.IsHomogeneous 2) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface f hf) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase f hf)]
    (hker : (tripleCompleteIntersectionToHypersurface f g h hf hg hh).ker ≤ i.ker)
    (hZ : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase f hf) = 8) :
    IsIso (tripleCompleteIntersectionLift f g h hf hg hh i hker) := by
  let _ := triple_quadrics_intersection_finite
    f g h hf hg hh hf0 hg0 hrel hregular
  let j := tripleCompleteIntersectionLift f g h hf hg hh i hker
  have hbase : j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) =
      i ≫ hypersurfaceToBase f hf := by
    rw [← tripleCompleteIntersectionToHypersurface_toBase,
      ← Category.assoc, tripleCompleteIntersectionLift_fac]
  let _ : IsFinite (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) := by
    rw [hbase]
    infer_instance
  have hseq : RingTheory.Sequence.IsRegular (MvPolynomial (Fin 4) K) [f, g, h] :=
    (triple_quadrics_isRegular_iff_sequential_regular f g h hf hg hh).mpr
      ⟨hf0, regular_mod_span_singleton_of_isRelPrime hrel, hregular⟩
  have hW : AllCharacteristics.finiteSchemeRank (toBase
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 8 :=
    triple_quadrics_intersection_length_eight_of_regular_sequence
      f g h hf hg hh hseq
  apply isIso_of_finite_closedImmersion_of_finiteSchemeRank_eq j
    (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
  have hZ' : AllCharacteristics.finiteSchemeRank (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 8 := by
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank, hbase,
      ← AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact hZ
  rw [hZ', hW]

end

end PfaffianDescent
