import PfaffianDescent.VoisinActualFiniteUnorderedPencil
import PfaffianDescent.VoisinFiniteIntrinsicEightToFourComplement
import PfaffianDescent.VoisinActualCanonicalFiniteBaseChange
import PfaffianDescent.VoisinGeometricCubicCoordinatesDegreeFour

/-! A finite canonical ordered generic fiber yields a degree-four
complement over the unordered configuration function field. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite cubic--quadratic intersection, its embedded rank-eight algebra,
and the effective degree-four residual cycle. -/
structure DegreeFourTripleComplement
    {F A : Type u} [Field F] [CommRing A] [Algebra F A]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3) where
  e : CubicQuadraticTripleEmbedding (A := A) p hp
  finite : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
    p (e.q 0).1 (e.q 1).1 hp (e.q 0).2 (e.q 1).2))
  cycle : EffectiveZeroCycle (scheme (tripleCompleteIntersectionHomogeneousIdeal
    p (e.q 0).1 (e.q 1).1 hp (e.q 0).2 (e.q 1).2))
  cycle_degree : EffectiveZeroCycle.degree
    (toBase (tripleCompleteIntersectionHomogeneousIdeal
      p (e.q 0).1 (e.q 1).1 hp (e.q 0).2 (e.q 1).2)) cycle = 4

theorem ActualGenericEightPresentation.exists_degreeFourComplement_of_canonicalFinite
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme]
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    [Infinite (cubicConfigurationBase p hp 8).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 8).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
      cubicConfigurationToBase p hp 8)
    {U : Scheme.{u}} [IsIntegral U]
    (i : U ⟶ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left) [IsOpenImmersion i]
    (hz : configurationQuotientMap (equationIdeal p hp) 8
        (i (genericPoint U)) =
      (cubicConfigurationBase p hp 8).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 8))
        (IsLocalRing.closedPoint
          (cubicConfigurationBase p hp 8).functionField))
    (w : ActualGenericEightPresentation p hp a ha i hz)
    [IsFinite (toBase (intrinsicEightPointTripleHomogeneousIdeal
      (p.map ((Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
        (orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 8).hom)).hom))
      (hp.map ((Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
        (orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 8).hom)).hom))
      (w.canonicalVectors p hp a ha i hz)))] :
    let Q := cubicConfigurationBase p hp 8
    let D := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap p hp 8 a ha
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    Nonempty (DegreeFourTripleComplement (A := Γ(D.val.subscheme, ⊤))
      (p.map a.hom) (hp.map a.hom)) := by
  dsimp only
  let Q := cubicConfigurationBase p hp 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let D := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp 8 a ha
  let b := quadraticOrderedLiftFunctionFieldHom p hp (i (genericPoint U)) hz
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField (i (genericPoint U))) :=
    b.toAlgebra
  haveI : Module.Finite Q.functionField Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite pD
  let φ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField]
      O.residueField (i (genericPoint U)) := fun k =>
    quadraticOrderedLiftCoefficientChangedComponentAlgHom
      p hp a ha (i (genericPoint U)) hz k
  have hA : Module.finrank Q.functionField Γ(D.val.subscheme, ⊤) = 8 := by
    apply (finiteSchemeCoefficient_finrank pD).trans
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact D.property.2.2.2 (IsLocalRing.closedPoint Q.functionField)
  obtain ⟨m, hm⟩ := w.exists_canonical_unitQuadraticMinor p hp a ha i hz
  have hcanon := w.canonicalIntrinsicFinite_baseChange p hp a ha i hz
  have hfinite : IsFinite (toBase
      (intrinsicEightPointTripleHomogeneousIdeal
        ((p.map a.hom).map (algebraMap Q.functionField
          (O.residueField (i (genericPoint U)))))
        ((hp.map a.hom).map (algebraMap Q.functionField
          (O.residueField (i (genericPoint U)))))
        (fun k j => φ k (w.d.x j)))) := by
    change IsFinite (toBase (intrinsicEightPointTripleHomogeneousIdeal
      ((p.map a.hom).map (algebraMap Q.functionField
        (O.residueField (i (genericPoint U)))))
      ((hp.map a.hom).map (algebraMap Q.functionField
        (O.residueField (i (genericPoint U)))))
      (w.canonicalVectors p hp a ha i hz)))
    exact hcanon
  letI := hfinite
  obtain ⟨e, hfin, z, hz⟩ := w.d.exists_degreeFourComplement
    (p.map a.hom) (hp.map a.hom) φ _ hA m hm
  exact ⟨⟨e, hfin, z, hz⟩⟩

end PfaffianDescent
