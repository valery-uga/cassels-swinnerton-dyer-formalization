import PfaffianDescent.QuadraticFullBaseLocusFiniteTriple
import AllCharacteristics.ProjectiveBaseChange
import Mathlib.FieldTheory.RatFunc.Basic

/-! Arbitrary ground fields: extend the ENTIRE quadratic system to an infinite
field, prove its full base ideal is the actual coefficient base change, and
select the finite triple there. Descent of dimension/basis is still separate. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Extend the ENTIRE original linear system, rather than three selected
members, by taking their scalar span over the new coefficient field. -/
def quadraticSystemCoefficientExtension (W : Submodule K (MvPolynomial (Fin 4) K)) :
    Submodule L (MvPolynomial (Fin 4) L) :=
  Submodule.span L (MvPolynomial.map (algebraMap K L) ''
    (W : Set (MvPolynomial (Fin 4) K)))

theorem quadraticSystemCoefficientExtension_homogeneous
    (W : Submodule K (MvPolynomial (Fin 4) K))
    (hW : ∀ q ∈ W, q.IsHomogeneous 2) :
    ∀ q ∈ quadraticSystemCoefficientExtension (L := L) W, q.IsHomogeneous 2 := by
  have hle : quadraticSystemCoefficientExtension (L := L) W ≤
      homogeneousSubmodule (Fin 4) L 2 := by
    apply Submodule.span_le.mpr
    rintro q ⟨p, hp, rfl⟩
    exact (hW p hp).map (algebraMap K L)
  exact fun q hq => hle hq

/-- The full base ideal of the extended system is literally the coefficient
extension of the old full base ideal, with no base-locus comparison premise. -/
theorem quadraticSystemBaseLocusIdeal_coefficientExtension
    (W : Submodule K (MvPolynomial (Fin 4) K))
    (hW : ∀ q ∈ W, q.IsHomogeneous 2) :
    (quadraticSystemBaseLocusIdeal W hW).toIdeal.map (MvPolynomial.map (algebraMap K L)) =
      (quadraticSystemBaseLocusIdeal (quadraticSystemCoefficientExtension (L := L) W)
        (quadraticSystemCoefficientExtension_homogeneous W hW)).toIdeal := by
  change (Ideal.span (W : Set (MvPolynomial (Fin 4) K))).map _ =
    Ideal.span (quadraticSystemCoefficientExtension (L := L) W :
      Set (MvPolynomial (Fin 4) L))
  rw [Ideal.map_span]
  apply le_antisymm
  · apply Ideal.span_mono
    exact Submodule.subset_span
  · apply Ideal.span_le.mpr
    have hle : quadraticSystemCoefficientExtension (L := L) W ≤
        (Ideal.span (MvPolynomial.map (algebraMap K L) ''
          (W : Set (MvPolynomial (Fin 4) K)))).restrictScalars L := by
      apply Submodule.span_le.mpr
      exact Ideal.subset_span
    exact hle

/-- Full quadratic-base-locus finiteness is preserved by actual coefficient
base change. -/
theorem quadraticSystemBaseLocusIdeal_isFinite_coefficientExtension
    (W : Submodule K (MvPolynomial (Fin 4) K))
    (hW : ∀ q ∈ W, q.IsHomogeneous 2)
    [IsFinite (toBase (quadraticSystemBaseLocusIdeal W hW))] :
    IsFinite (toBase (quadraticSystemBaseLocusIdeal (quadraticSystemCoefficientExtension (L := L) W)
      (quadraticSystemCoefficientExtension_homogeneous W hW))) := by
  let I := quadraticSystemBaseLocusIdeal W hW
  let J := quadraticSystemBaseLocusIdeal (quadraticSystemCoefficientExtension (L := L) W)
    (quadraticSystemCoefficientExtension_homogeneous W hW)
  have hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap K L)) = J.toIdeal :=
    quadraticSystemBaseLocusIdeal_coefficientExtension W hW
  letI : IsFinite (pullback.snd (toBase I)
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) := inferInstance
  rw [← projectiveBaseChangeIso_hom_snd (algebraMap K L) I J hIJ]
  infer_instance

/-- Over an ARBITRARY ground field the literal finite-triple extraction is
available after the internally chosen infinite rational-function extension.
This is an intermediate statement, not the final ground-field proposition. -/
theorem exists_finite_triple_over_ratFunc_of_finite_full_quadratic_system
    (W : Submodule K (MvPolynomial (Fin 4) K))
    (hW : ∀ q ∈ W, q.IsHomogeneous 2)
    [IsFinite (toBase (quadraticSystemBaseLocusIdeal W hW))] :
    ∃ q : Fin 3 → quadraticSystemCoefficientExtension (L := RatFunc K) W,
      IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
        (q 0).val (q 1).val (q 2).val
        (quadraticSystemCoefficientExtension_homogeneous W hW _ (q 0).property)
        (quadraticSystemCoefficientExtension_homogeneous W hW _ (q 1).property)
        (quadraticSystemCoefficientExtension_homogeneous W hW _ (q 2).property))) := by
  letI : Infinite (RatFunc K) :=
    Infinite.of_injective (algebraMap (Polynomial K) (RatFunc K))
      (RatFunc.algebraMap_injective K)
  letI := quadraticSystemBaseLocusIdeal_isFinite_coefficientExtension (L := RatFunc K) W hW
  exact exists_finite_triple_of_finite_full_quadratic_system
    (quadraticSystemCoefficientExtension (L := RatFunc K) W)
    (quadraticSystemCoefficientExtension_homogeneous W hW)

end PfaffianDescent
