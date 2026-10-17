import PfaffianDescent.VoisinFiniteAlgebraPencilIdealDescent
import PfaffianDescent.VoisinRelativeTripleIntersectionFamily

/-!
# Projective comparison for the unordered quadratic pencil

The intrinsic projective intersection of eight ordered splitting points is
the base change of the cubic--quadric--quadric intersection defined by two
unordered-field quadrics, under the explicit kernel-detection hypotheses.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open CategoryTheory.Limits
open AllCharacteristics.UniversalHomogeneous
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem quadraticHomogeneousPair_intrinsicHomogeneousIdeal_eq_relative
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]
    (φ : Fin 8 → A →ₐ[K] L)
    (hφ : Function.Injective (fun t : A => fun i => φ i t))
    (x : Fin 4 → A)
    (q : Fin 2 → homogeneousSubmodule (Fin 4) K 2)
    (hq : LinearIndependent K q)
    (hzero : ∀ i, (q i).1.eval₂ (algebraMap K A) x = 0)
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (hminor : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun i j => φ i (x j))).det)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    intrinsicEightPointTripleHomogeneousIdeal
      (p.map (algebraMap K L)) (hp.map (algebraMap K L))
      (fun i j => φ i (x j)) =
    relativeTripleIntersectionHomogeneousIdeal
      (p.map (algebraMap K L))
      ((q 0).1.map (algebraMap K L))
      ((q 1).1.map (algebraMap K L))
      (hp.map (algebraMap K L))
      ((q 0).2.map (algebraMap K L))
      ((q 1).2.map (algebraMap K L)) := by
  apply HomogeneousIdeal.ext
  rw [intrinsicEightPointTripleHomogeneousIdeal_toIdeal,
    quadraticHomogeneousPair_intrinsicTripleIdeal_eq_mappedPolynomials
      φ hφ x q hq hzero m hminor p]
  change Ideal.span (insert (p.map (algebraMap K L))
      (Set.range (fun i : Fin 2 => (q i).1.map (algebraMap K L)))) =
    Ideal.span ({p.map (algebraMap K L),
      (q 0).1.map (algebraMap K L),
      (q 1).1.map (algebraMap K L)} : Set _)
  have hrange : Set.range (fun i : Fin 2 =>
      (q i).1.map (algebraMap K L)) =
      { (q 0).1.map (algebraMap K L),
        (q 1).1.map (algebraMap K L) } := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hz
      rcases hz with h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
  rw [hrange]

/-- The intrinsic ordered projective intersection is the pullback of the
unordered cubic--quadric--quadric family along the splitting-field point. -/
noncomputable def quadraticHomogeneousPair_intrinsicProjectiveBaseChangeIso
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]
    (φ : Fin 8 → A →ₐ[K] L)
    (hφ : Function.Injective (fun t : A => fun i => φ i t))
    (x : Fin 4 → A)
    (q : Fin 2 → homogeneousSubmodule (Fin 4) K 2)
    (hq : LinearIndependent K q)
    (hzero : ∀ i, (q i).1.eval₂ (algebraMap K A) x = 0)
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (hminor : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun i j => φ i (x j))).det)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    scheme (intrinsicEightPointTripleHomogeneousIdeal
      (p.map (algebraMap K L)) (hp.map (algebraMap K L))
      (fun i j => φ i (x j))) ≅
    pullback (relativeTripleIntersectionToBase
      p (q 0).1 (q 1).1 hp (q 0).2 (q 1).2)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  rw [quadraticHomogeneousPair_intrinsicHomogeneousIdeal_eq_relative
    φ hφ x q hq hzero m hminor p hp]
  exact relativeTripleIntersectionBaseChangeIso
    (algebraMap K L) p (q 0).1 (q 1).1 hp (q 0).2 (q 1).2

end PfaffianDescent
