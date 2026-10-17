import PfaffianDescent.VoisinFiniteAlgebraPencilProjectiveOverBase
import PfaffianDescent.VoisinCanonicalPencilCoefficients

/-! A finite intrinsic ordered triple intersection descends to a finite
unordered cubic--quadratic intersection when the two quadratic relations
come from a rank-eight coordinate algebra. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The two independent quadrics from a rank-eight algebra define a finite
intersection over the base field whenever the intrinsic ordered intersection
is finite over the splitting field. -/
theorem exists_rankEight_finiteUnorderedTriple_of_finiteIntrinsic
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Field L] [Algebra K L]
    (x : Fin 4 → A) (hA : Module.finrank K A = 8)
    (φ : Fin 8 → A →ₐ[K] L)
    (hφ : Function.Injective (fun t : A => fun i => φ i t))
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (hminor : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun i j => φ i (x j))).det)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [hfinite : IsFinite (toBase (intrinsicEightPointTripleHomogeneousIdeal
      (p.map (algebraMap K L)) (hp.map (algebraMap K L))
      (fun i j => φ i (x j))))] :
    ∃ q : Fin 2 → homogeneousSubmodule (Fin 4) K 2,
      LinearIndependent K q ∧
      (∀ i, (q i).1.eval₂ (algebraMap K A) x = 0) ∧
      IsFinite (relativeTripleIntersectionToBase
        p (q 0).1 (q 1).1 hp (q 0).2 (q 1).2) := by
  obtain ⟨q, hq, hzero⟩ :=
    exists_rankEight_independentVanishingHomogeneousQuadrics x hA
  let C := quadraticHomogeneousPair_intrinsicProjectiveComparisonOverBase
    φ hφ x q hq hzero m hminor p hp
  exact ⟨q, hq, hzero,
    C.isFinite_unordered p (q 0).1 (q 1).1 hp (q 0).2 (q 1).2 _⟩

end PfaffianDescent
