import PfaffianDescent.VoisinCanonicalOrderedCoordinateLift
import PfaffianDescent.VoisinOrderedChartNormalizedPoints

/-! Normalized coordinates for the canonical ordered generic cubic configuration. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every selected chart lift at the canonical ordered generic point yields
a normalized vector whose projective point is the corresponding canonical
marked point. The residue-field comparison is heterogeneous because the
canonical point and the chart generic image are propositionally equal. -/
theorem cubicOrderedPointOverGeneric_normalizedChartCoordinate
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    (zc : CoordinateRing (equationIdeal p hp))
    (hzc : zc ∈ grading (equationIdeal p hp) 1)
    (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
    (hellzc : Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell = zc)
    {U : Scheme.{u}} [IsIntegral U]
    (i : U ⟶ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left) [IsOpenImmersion i]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left)
    (hz : configurationQuotientMap (equationIdeal p hp) 8 z =
      (cubicConfigurationBase p hp 8).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 8))
        (IsLocalRing.closedPoint
          (cubicConfigurationBase p hp 8).functionField))
    (t : Fin 8 → (U ⟶ Spec (.of
      (Away (grading (equationIdeal p hp)) zc))))
    (ht : ∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp)) zc hzc
      (by decide : 0 < 1) =
        (i ≫ Over.Hom.left
          (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left)
    (k : Fin 8) :
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left
    let a := openImmersion_genericResidueLift i
    let b : K →+* O.residueField (i (genericPoint U)) :=
      (Spec.preimage (a ≫ i ≫
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom)).hom
    letI : Algebra K (O.residueField (i (genericPoint U))) := b.toAlgebra
    let x : Fin 4 → O.residueField (i (genericPoint U)) := fun j =>
      (Spec.preimage (a ≫ t k)).hom
        (linearChartCoordinate (equationIdeal p hp) zc hzc j)
    ell.eval₂ (algebraMap K _) x = 1 ∧
    ∃ (he : ∀ q ∈ (equationIdeal p hp).toIdeal,
      q.eval₂ (algebraMap K _) x = 0),
    ∃ (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K _) x) he) zc = 1),
      HEq (linearNormalizedPointAt (equationIdeal p hp) x he zc hzc hzOne)
        (O.fromSpecResidueField z ≫
          (Over.Hom.left
            (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8) ≫
            (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left)) := by
  dsimp only
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let a := openImmersion_genericResidueLift i
  let b : K →+* O.residueField (i (genericPoint U)) :=
    (Spec.preimage (a ≫ i ≫
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom)).hom
  letI : Algebra K (O.residueField (i (genericPoint U))) := b.toAlgebra
  obtain ⟨hnorm, he, hzOne, hpoint⟩ :=
    orderedChartLift_fieldPoint_normalizedPointAt
      (equationIdeal p hp) zc hzc ell hell hellzc U i t ht a k
  refine ⟨hnorm, he, hzOne, ?_⟩
  dsimp only [a] at hpoint
  exact (heq_of_eq hpoint).trans
    (cubicOrderedPointOverGeneric_chartCoordinate p hp i z hz
      (Proj.awayι (grading (equationIdeal p hp)) zc hzc (by decide : 0 < 1))
      t ht k)

end PfaffianDescent
