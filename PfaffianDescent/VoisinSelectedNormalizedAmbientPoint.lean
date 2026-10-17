import PfaffianDescent.VoisinCanonicalGenericNormalizedPoints

/-! The selected normalized generic point in the original ambient space. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The marked-point map written through the ordered-family coordinate is
the canonical ordered marked point in ambient projective space. -/
theorem orderedFamilyMarkedPoint_comp_ambient_eq_projectivePoint
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left)
    (k : Fin 8) :
    ((orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left.fromSpecResidueField z ≫
      (Over.Hom.left
        (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left)) ≫
      hypersurfaceToAmbient p hp =
    (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left.fromSpecResidueField z ≫
      @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
        (grading (equationIdeal p hp)) _
        (hypersurfaceToBase p hp) hsep 8
        (hypersurfaceToAmbient p hp) k := by
  change ((orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left.fromSpecResidueField z ≫
        ((orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 8).ι ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left)) ≫
      hypersurfaceToAmbient p hp =
    (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left.fromSpecResidueField z ≫
      ((orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 8).ι ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left ≫
        hypersurfaceToAmbient p hp)
  exact (Category.assoc _ _ _).trans
    (congrArg (fun t =>
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).left.fromSpecResidueField z ≫ t)
      (Category.assoc _ _ _))

/-- The selected chart's normalized vector represents the canonical
ordered marked point after passing from the cubic to ambient projective
space. Its source-field equality remains heterogeneous until the equality
of the selected and canonical generic points is transported. -/
theorem cubicOrderedPointOverGeneric_normalizedChartCoordinate_ambient
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
      HEq ((linearNormalizedPointAt (equationIdeal p hp) x he zc hzc hzOne) ≫
        hypersurfaceToAmbient p hp)
        (O.fromSpecResidueField z ≫
          @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
            (grading (equationIdeal p hp)) _
            (hypersurfaceToBase p hp) hsep 8
            (hypersurfaceToAmbient p hp) k) := by
  have hzi := cubicOrderedPointOverGeneric_eq_chartGenericImage p hp i z hz
  subst z
  dsimp only
  obtain ⟨hnorm, he, hzOne, hpoint⟩ :=
    cubicOrderedPointOverGeneric_normalizedChartCoordinate
      p hp zc hzc ell hell hellzc i (i (genericPoint U)) hz t ht k
  refine ⟨hnorm, he, hzOne, ?_⟩
  have hmark := orderedFamilyMarkedPoint_comp_ambient_eq_projectivePoint
    p hp (i (genericPoint U)) k
  exact heq_of_eq ((congrArg
    (fun q => q ≫ hypersurfaceToAmbient p hp) (eq_of_heq hpoint)).trans hmark)

end PfaffianDescent
