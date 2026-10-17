import PfaffianDescent.VoisinGenericEightTripleEmbedding
import PfaffianDescent.VoisinFiniteTripleBezout
import PfaffianDescent.FiniteClosedSubschemeCycleComplement

/-! The finite triple intersection containing a rank-eight algebra has a degree-four complement. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

/-- Once the selected cubic--two-quadrics intersection is finite, its actual
rank-eight closed subscheme has a degree-four effective complement cycle. -/
theorem CubicQuadraticTripleEmbedding.exists_degreeFourComplementCycle
    {F A : Type u} [Field F] [Infinite F] [CommRing A] [Algebra F A]
    [Module.Finite F A]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (e : CubicQuadraticTripleEmbedding (A := A) p hp)
    (hA : Module.finrank F A = 8)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      p (e.q 0).1 (e.q 1).1 hp (e.q 0).2 (e.q 1).2))] :
    ∃ z : EffectiveZeroCycle (scheme (tripleCompleteIntersectionHomogeneousIdeal
        p (e.q 0).1 (e.q 1).1 hp (e.q 0).2 (e.q 1).2)),
      EffectiveZeroCycle.degree (toBase (tripleCompleteIntersectionHomogeneousIdeal
        p (e.q 0).1 (e.q 1).1 hp (e.q 0).2 (e.q 1).2)) z = 4 := by
  let I := tripleCompleteIntersectionHomogeneousIdeal
    p (e.q 0).1 (e.q 1).1 hp (e.q 0).2 (e.q 1).2
  haveI : Nontrivial A := Module.finrank_pos_iff.mp (by rw [hA]; decide)
  have hpoints : Nonempty (Spec (.of A)) := inferInstance
  have hX : Nonempty (scheme I) := Nonempty.map e.j hpoints
  have h12 : finiteSchemeRank (toBase I) = 12 :=
    cubicTwoQuadrics_finite_nonempty_rank_twelve
      p (e.q 0).1 (e.q 1).1 hp (e.q 0).2 (e.q 1).2 hX
  haveI : IsClosedImmersion e.j := e.closed
  haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap F A))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  haveI : IsFinite (e.j ≫ toBase I) := by
    rw [e.toBase_eq]
    infer_instance
  have h8 : finiteSchemeRank (e.j ≫ toBase I) = 8 := by
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank, e.toBase_eq,
      Scheme.Hom.finrank_SpecMap_algebraMap]
    exact (congrFun (Module.rankAtStalk_eq_finrank_of_free
      (R := F) (M := A)) _).trans hA
  refine ⟨finiteClosedSubschemeComplementCycle e.j (toBase I), ?_⟩
  rw [finiteClosedSubschemeComplementCycle_degree, h12, h8]

end PfaffianDescent
