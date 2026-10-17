import PfaffianDescent.VoisinSelectedNormalizedCanonicalMarkedPoint

/-! All eight selected generic chart vectors represent their marked points. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Assemble the eight pointwise normalized selected-chart vectors into one
family with their vanishing, normalization, and ambient marked-point proofs. -/
theorem exists_cubicSelectedGeneric_normalizedMarkedFamily
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
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left) :
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left
    let a := openImmersion_genericResidueLift i
    let b : K →+* O.residueField (i (genericPoint U)) :=
      (Spec.preimage (a ≫ i ≫
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom)).hom
    letI : Algebra K (O.residueField (i (genericPoint U))) := b.toAlgebra
    let x : Fin 8 → Fin 4 → O.residueField (i (genericPoint U)) :=
      fun k j => (Spec.preimage (a ≫ t k)).hom
        (linearChartCoordinate (equationIdeal p hp) zc hzc j)
    ∃ (he : ∀ k, ∀ q ∈ (equationIdeal p hp).toIdeal,
      q.eval₂ (algebraMap K _) (x k) = 0),
    ∃ (hzOne : ∀ k, (Ideal.Quotient.lift
      (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K _) (x k)) (he k)) zc = 1),
      ∀ k,
        (linearNormalizedPointAt (equationIdeal p hp) (x k)
          (he k) zc hzc (hzOne k)) ≫ hypersurfaceToAmbient p hp =
        O.fromSpecResidueField (i (genericPoint U)) ≫
          @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
            (grading (equationIdeal p hp)) _
            (hypersurfaceToBase p hp) hsep 8
            (hypersurfaceToAmbient p hp) k := by
  dsimp only
  classical
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let a := openImmersion_genericResidueLift i
  let b : K →+* O.residueField (i (genericPoint U)) :=
    (Spec.preimage (a ≫ i ≫
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom)).hom
  letI : Algebra K (O.residueField (i (genericPoint U))) := b.toAlgebra
  have hEach : ∀ k : Fin 8,
      ∃ (he : ∀ q ∈ (equationIdeal p hp).toIdeal,
        q.eval₂ (algebraMap K _) (fun j =>
          (Spec.preimage (openImmersion_genericResidueLift i ≫ t k)).hom
            (linearChartCoordinate (equationIdeal p hp) zc hzc j)) = 0),
      ∃ (hzOne : (Ideal.Quotient.lift
        (equationIdeal p hp).toIdeal
        (eval₂Hom (algebraMap K _) (fun j =>
          (Spec.preimage (openImmersion_genericResidueLift i ≫ t k)).hom
            (linearChartCoordinate (equationIdeal p hp) zc hzc j))) he) zc = 1),
        (linearNormalizedPointAt (equationIdeal p hp)
          (fun j => (Spec.preimage
            (openImmersion_genericResidueLift i ≫ t k)).hom
              (linearChartCoordinate (equationIdeal p hp) zc hzc j))
          he zc hzc hzOne) ≫ hypersurfaceToAmbient p hp =
        (orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 8).left.fromSpecResidueField
            (i (genericPoint U)) ≫
          @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
            (grading (equationIdeal p hp)) _
            (hypersurfaceToBase p hp) hsep 8
            (hypersurfaceToAmbient p hp) k := by
    intro k
    exact (cubicSelectedGeneric_normalizedChartCoordinate_ambient_eq_marked
      p hp zc hzc ell hell hellzc i hz t ht k).2
  choose he hzOne hpoint using hEach
  exact ⟨he, hzOne, hpoint⟩

end PfaffianDescent
