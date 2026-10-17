import PfaffianDescent.PolynomialCoefficientFaithfullyFlat
import PfaffianDescent.TripleCompleteIntersectionLength
import PfaffianDescent.TripleQuadricsSequentialRegularity
import AllCharacteristics.ProjectiveBaseChangeFiniteRank
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Regular.Flat

/-!
# Arbitrary-field length of a regular three-quadric intersection

The direct Hilbert-function proof of Bézout length uses an infinite field to
choose a nowhere-vanishing linear form.  This file removes that restriction:
it extends scalars to the rational-function field, applies the existing
infinite-field calculation there, and descends finite-scheme rank through
projective base change.
-/

namespace PfaffianDescent

open MvPolynomial
open RingTheory.Sequence
open AllCharacteristics.HomogeneousProjective
open AlgebraicGeometry

universe u

noncomputable section

variable {k : Type u} [Field k]

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

private theorem triple_quadrics_ratFunc_map_ideal
    (f g h : MvPolynomial (Fin 4) k)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2) :
    (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal.map
        (MvPolynomial.map (algebraMap k (RatFunc k))) =
      (tripleCompleteIntersectionHomogeneousIdeal
        (f.map (algebraMap k (RatFunc k)))
        (g.map (algebraMap k (RatFunc k)))
        (h.map (algebraMap k (RatFunc k)))
        (hf.map (algebraMap k (RatFunc k)))
        (hg.map (algebraMap k (RatFunc k)))
        (hh.map (algebraMap k (RatFunc k)))).toIdeal := by
  rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
    tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
    tripleCompleteIntersectionIdeal, Ideal.map_span,
    tripleCompleteIntersectionIdeal]
  apply congrArg Ideal.span
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with rfl | rfl | rfl <;> simp
  · intro hx
    rcases hx with hx | hx | hx
    · exact ⟨f, Or.inl rfl, hx.symm⟩
    · exact ⟨g, Or.inr (Or.inl rfl), hx.symm⟩
    · exact ⟨h, Or.inr (Or.inr rfl), hx.symm⟩

/-- Three homogeneous quadrics which form a regular sequence cut out a
finite projective scheme of rank eight over every field. -/
theorem triple_quadrics_intersection_length_eight_of_regular_sequence
    (f g h : MvPolynomial (Fin 4) k)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    (hseq : IsRegular (MvPolynomial (Fin 4) k) [f, g, h]) :
    letI : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) :=
      by
        obtain ⟨hf0, hgreg, hhregular⟩ :=
          (triple_quadrics_isRegular_iff_sequential_regular f g h hf hg hh).mp hseq
        exact triple_quadrics_intersection_finite_of_sequential_regular
          f g h hf hg hh hf0 hgreg hhregular
    AllCharacteristics.finiteSchemeRank (toBase
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 8 := by
  letI : Infinite (RatFunc k) :=
    Infinite.of_injective (algebraMap (Polynomial k) (RatFunc k))
      (RatFunc.algebraMap_injective k)
  letI : Module.FaithfullyFlat (MvPolynomial (Fin 4) k)
      (MvPolynomial (Fin 4) (RatFunc k)) :=
    mvPolynomial_coefficientExtension_faithfullyFlat
  have hmap : algebraMap (MvPolynomial (Fin 4) k)
      (MvPolynomial (Fin 4) (RatFunc k)) =
      MvPolynomial.map (algebraMap k (RatFunc k)) := rfl
  have hseq' := RingTheory.Sequence.IsRegular.of_faithfullyFlat
    (S := MvPolynomial (Fin 4) (RatFunc k)) hseq
  rw [hmap] at hseq'
  have hseq'' : IsRegular (MvPolynomial (Fin 4) (RatFunc k))
      [f.map (algebraMap k (RatFunc k)), g.map (algebraMap k (RatFunc k)),
        h.map (algebraMap k (RatFunc k))] := by
    simpa only [List.map_cons, List.map_nil] using hseq'
  obtain ⟨hf0, hgreg, hhregular⟩ :=
    (triple_quadrics_isRegular_iff_sequential_regular f g h hf hg hh).mp hseq
  letI : IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) :=
    triple_quadrics_intersection_finite_of_sequential_regular
      f g h hf hg hh hf0 hgreg hhregular
  obtain ⟨hf0', hgreg', hhregular'⟩ :=
    (triple_quadrics_isRegular_iff_sequential_regular
      (f.map (algebraMap k (RatFunc k)))
      (g.map (algebraMap k (RatFunc k)))
      (h.map (algebraMap k (RatFunc k)))
      (hf.map (algebraMap k (RatFunc k)))
      (hg.map (algebraMap k (RatFunc k)))
      (hh.map (algebraMap k (RatFunc k)))).mp hseq''
  letI : IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal
        (f.map (algebraMap k (RatFunc k)))
        (g.map (algebraMap k (RatFunc k)))
        (h.map (algebraMap k (RatFunc k)))
        (hf.map (algebraMap k (RatFunc k)))
        (hg.map (algebraMap k (RatFunc k)))
        (hh.map (algebraMap k (RatFunc k))))) :=
    triple_quadrics_intersection_finite_of_sequential_regular
      (f.map (algebraMap k (RatFunc k)))
      (g.map (algebraMap k (RatFunc k)))
      (h.map (algebraMap k (RatFunc k)))
      (hf.map (algebraMap k (RatFunc k)))
      (hg.map (algebraMap k (RatFunc k)))
      (hh.map (algebraMap k (RatFunc k)))
      hf0' hgreg' hhregular'
  have htarget : AllCharacteristics.finiteSchemeRank (toBase
      (tripleCompleteIntersectionHomogeneousIdeal
        (f.map (algebraMap k (RatFunc k)))
        (g.map (algebraMap k (RatFunc k)))
        (h.map (algebraMap k (RatFunc k)))
        (hf.map (algebraMap k (RatFunc k)))
        (hg.map (algebraMap k (RatFunc k)))
        (hh.map (algebraMap k (RatFunc k))))) = 8 :=
    triple_quadrics_intersection_length_eight_of_sequential_regular
      (f.map (algebraMap k (RatFunc k)))
      (g.map (algebraMap k (RatFunc k)))
      (h.map (algebraMap k (RatFunc k)))
      (hf.map (algebraMap k (RatFunc k)))
      (hg.map (algebraMap k (RatFunc k)))
      (hh.map (algebraMap k (RatFunc k)))
      hf0' hgreg' hhregular'
  exact (AllCharacteristics.HomogeneousProjective.projective_finiteSchemeRank_baseChange
    (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)
    (tripleCompleteIntersectionHomogeneousIdeal
      (f.map (algebraMap k (RatFunc k)))
      (g.map (algebraMap k (RatFunc k)))
      (h.map (algebraMap k (RatFunc k)))
      (hf.map (algebraMap k (RatFunc k)))
      (hg.map (algebraMap k (RatFunc k)))
      (hh.map (algebraMap k (RatFunc k))))
    (triple_quadrics_ratFunc_map_ideal f g h hf hg hh)).trans htarget

end
end PfaffianDescent
