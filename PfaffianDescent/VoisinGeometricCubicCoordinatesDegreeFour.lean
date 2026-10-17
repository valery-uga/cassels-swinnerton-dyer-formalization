import PfaffianDescent.VoisinGenericEightGeometricCubicCoordinates
import PfaffianDescent.VoisinFiniteIntrinsicEightToFourComplement

/-! A finite canonical ordered intersection in one detecting cubic chart
has an unordered degree-four residual cycle. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GeometricDetectingCubicCoordinates.exists_degreeFourComplement
    {F A L : Type u} [Field F] [Infinite F]
    [CommRing A] [Algebra F A] [FiniteDimensional F A]
    [Field L] [Algebra F L]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (φ : Fin 8 → A →ₐ[F] L)
    (j : Spec (.of A) ⟶ Proj (homogeneousSubmodule (Fin 4) F))
    (d : GeometricDetectingCubicCoordinates p φ j)
    (hA : Module.finrank F A = 8)
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k r => φ k (d.x r))).det)
    [IsFinite (toBase (intrinsicEightPointTripleHomogeneousIdeal
      (p.map (algebraMap F L)) (hp.map (algebraMap F L))
      (fun k r => φ k (d.x r))))] :
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
  have hxell : d.ell.eval₂ (algebraMap F A) d.x = 1 := by
    change (eval₂Hom (algebraMap F A) d.x) d.ell = 1
    exact d.ellOne
  have hφ : Function.Injective (fun t : A => fun k => φ k t) :=
    eight_component_algHom_joint_injective_of_quadraticFrame_detection
      d.x hA φ d.detects
  exact exists_rankEight_degreeFourComplement_of_finiteIntrinsic
    p hp d.x hA d.ell d.ellHomogeneous hxell d.evalSurjective
    d.cubicVanish φ hφ m hm

end PfaffianDescent
