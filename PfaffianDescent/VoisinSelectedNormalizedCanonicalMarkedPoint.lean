import PfaffianDescent.VoisinSelectedNormalizedAmbientPoint

/-! Ordinary marked-point equality at the selected chart's generic image. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- At the selected chart's own generic image, its residue field is
definitionally the source field of the canonical marked-point map, so the
ambient point comparison is an ordinary equality. -/
theorem cubicSelectedGeneric_normalizedChartCoordinate_ambient_eq_marked
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
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
    (hz : configurationQuotientMap (equationIdeal p hp) 8
        (i (genericPoint U)) =
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
      (linearNormalizedPointAt (equationIdeal p hp) x he zc hzc hzOne) ≫
        hypersurfaceToAmbient p hp =
        O.fromSpecResidueField (i (genericPoint U)) ≫
          @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
            (grading (equationIdeal p hp)) _
            (hypersurfaceToBase p hp) hsep 8
            (hypersurfaceToAmbient p hp) k := by
  dsimp only
  obtain ⟨hnorm, he, hzOne, hpoint⟩ :=
    cubicOrderedPointOverGeneric_normalizedChartCoordinate_ambient
      p hp zc hzc ell hell hellzc i (i (genericPoint U)) hz t ht k
  exact ⟨hnorm, he, hzOne, eq_of_heq hpoint⟩

end PfaffianDescent
