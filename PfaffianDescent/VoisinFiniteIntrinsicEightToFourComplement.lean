import PfaffianDescent.VoisinFiniteIntrinsicUnorderedPencil
import PfaffianDescent.VoisinFiniteAlgebraTripleComplement

/-! The same quadratic pencil that descends a finite ordered intersection
contains its rank-eight algebra and has a degree-four residual cycle. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_rankEight_degreeFourComplement_of_finiteIntrinsic
    {F A L : Type u} [Field F] [Infinite F]
    [CommRing A] [Algebra F A] [FiniteDimensional F A]
    [Field L] [Algebra F L]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (x : Fin 4 → A) (hA : Module.finrank F A = 8)
    (ell : MvPolynomial (Fin 4) F) (hell : ell.IsHomogeneous 1)
    (hxell : ell.eval₂ (algebraMap F A) x = 1)
    (hgen : Function.Surjective (eval₂Hom (algebraMap F A) x))
    (hpx : p.eval₂ (algebraMap F A) x = 0)
    (φ : Fin 8 → A →ₐ[F] L)
    (hφ : Function.Injective (fun t : A => fun i => φ i t))
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (hminor : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun i j => φ i (x j))).det)
    [IsFinite (toBase (intrinsicEightPointTripleHomogeneousIdeal
      (p.map (algebraMap F L)) (hp.map (algebraMap F L))
      (fun i j => φ i (x j))))] :
    ∃ e : CubicQuadraticTripleEmbedding (A := A) p hp,
      ∃ hfin : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
          p (e.q 0).1 (e.q 1).1 hp (e.q 0).2 (e.q 1).2)),
        letI := hfin
        ∃ z : EffectiveZeroCycle
            (scheme (tripleCompleteIntersectionHomogeneousIdeal
              p (e.q 0).1 (e.q 1).1 hp (e.q 0).2 (e.q 1).2)),
          EffectiveZeroCycle.degree
            (toBase (tripleCompleteIntersectionHomogeneousIdeal
              p (e.q 0).1 (e.q 1).1 hp (e.q 0).2 (e.q 1).2)) z = 4 := by
  obtain ⟨q, _, hzero, hfin⟩ :=
    exists_rankEight_finiteUnorderedTriple_of_finiteIntrinsic
      x hA φ hφ m hminor p hp
  obtain ⟨j, hj, hjbase⟩ :=
    closed_point_of_triple_complete_intersection_coordinates
      p (q 0).1 (q 1).1 hp (q 0).2 (q 1).2
      x ell hell hxell hgen hpx (hzero 0) (hzero 1)
  let e : CubicQuadraticTripleEmbedding (A := A) p hp :=
    ⟨q, j, hj, hjbase⟩
  have hfin' : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      p (q 0).1 (q 1).1 hp (q 0).2 (q 1).2)) := by
    exact hfin
  letI := hfin'
  obtain ⟨z, hz⟩ := e.exists_degreeFourComplementCycle p hp hA
  exact ⟨e, hfin', z, hz⟩

end PfaffianDescent
