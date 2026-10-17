import PfaffianDescent.VoisinGenericEightEmbeddedComparison
import PfaffianDescent.VoisinFiniteAlgebraTripleComplement

/-! Intrinsic ordered finiteness gives a degree-four unordered residual cycle. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The combined embedding and base-preserving comparison turn finiteness
of the intrinsic ordered intersection into a degree-four effective residual
cycle over the unordered coefficient field. -/
theorem CubicQuadraticTripleEmbeddedComparison.exists_degreeFourComplementCycle_of_intrinsicFinite
    {F A L : Type u} [Field F] [Infinite F]
    [CommRing A] [Algebra F A] [Module.Finite F A]
    [Field L] [Algebra F L]
    (φ : Fin 8 → A →ₐ[F] L)
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (C : CubicQuadraticTripleEmbeddedComparison φ p hp)
    (hA : Module.finrank F A = 8)
    [IsFinite (toBase (intrinsicEightPointTripleHomogeneousIdeal
      (p.map (algebraMap F L)) (hp.map (algebraMap F L))
      (fun i j => φ i (C.x j))))] :
    ∃ z : EffectiveZeroCycle (scheme (tripleCompleteIntersectionHomogeneousIdeal
        p (C.embedding.q 0).1 (C.embedding.q 1).1
        hp (C.embedding.q 0).2 (C.embedding.q 1).2)),
      EffectiveZeroCycle.degree (toBase (tripleCompleteIntersectionHomogeneousIdeal
        p (C.embedding.q 0).1 (C.embedding.q 1).1
        hp (C.embedding.q 0).2 (C.embedding.q 1).2)) z = 4 := by
  haveI : IsFinite (relativeTripleIntersectionToBase
      p (C.embedding.q 0).1 (C.embedding.q 1).1
      hp (C.embedding.q 0).2 (C.embedding.q 1).2) :=
    C.projectiveComparison.isFinite_unordered
      p (C.embedding.q 0).1 (C.embedding.q 1).1
      hp (C.embedding.q 0).2 (C.embedding.q 1).2 _
  haveI : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      p (C.embedding.q 0).1 (C.embedding.q 1).1
      hp (C.embedding.q 0).2 (C.embedding.q 1).2)) := by
    have hq₀ : (C.embedding.q 0).1.IsHomogeneous 2 :=
      (MvPolynomial.mem_homogeneousSubmodule 2 _).mp (C.embedding.q 0).2
    have hq₁ : (C.embedding.q 1).1.IsHomogeneous 2 :=
      (MvPolynomial.mem_homogeneousSubmodule 2 _).mp (C.embedding.q 1).2
    rw [← relativeTripleIntersectionHomogeneousIdeal_eq_triple
      p (C.embedding.q 0).1 (C.embedding.q 1).1 hp hq₀ hq₁]
    infer_instance
  exact C.embedding.exists_degreeFourComplementCycle p hp hA

end PfaffianDescent
