import PfaffianDescent.VoisinSelectedNormalizedMarkedFamily
import PfaffianDescent.VoisinCanonicalComponentMarkedFamily
import PfaffianDescent.VoisinEightPointComparisonData
import PfaffianDescent.VoisinGenericEightGeometricCubicCoordinates

/-! Inputs for comparing the actual selected and canonical generic eight points. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A selected common chart and geometric rank-eight presentation at the
same ordered generic point. The fields and marked points are fixed by the
parameters; the fields below retain the actual selected and canonical
coordinate maps. -/
structure ActualGenericEightPresentation
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 8).toScheme]
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left]
    [IsIntegral (cubicConfigurationBase p hp 8)]
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
          (cubicConfigurationBase p hp 8).functionField)) where
  zc : CoordinateRing (equationIdeal p hp)
  hzc : zc ∈ grading (equationIdeal p hp) 1
  ell : MvPolynomial (Fin 4) K
  hell : ell.IsHomogeneous 1
  hellzc : Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell = zc
  t : Fin 8 → (U ⟶ Spec (.of
    (Away (grading (equationIdeal p hp)) zc)))
  ht : ∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp)) zc hzc
    (by decide : 0 < 1) =
      (i ≫ Over.Hom.left
        (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left
  d :
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
    GeometricDetectingCubicCoordinates (p.map a.hom)
      (fun k => quadraticOrderedLiftCoefficientChangedComponentAlgHom
        p hp a ha (i (genericPoint U)) hz k)
      (D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
        hypersurfaceToAmbient (p.map a.hom) (hp.map a.hom))

/-- The selected chart's actual eight vectors in the ordered residue field. -/
noncomputable def ActualGenericEightPresentation.selectedVectors
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 8).toScheme]
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left]
    [IsIntegral (cubicConfigurationBase p hp 8)]
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
    (w : ActualGenericEightPresentation p hp a ha i hz) :
    Fin 8 → Fin 4 →
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).left.residueField (i (genericPoint U)) :=
  fun k j => (Spec.preimage (openImmersion_genericResidueLift i ≫ w.t k)).hom
    (linearChartCoordinate (equationIdeal p hp) w.zc w.hzc j)

/-- The geometric rank-eight algebra's actual component vectors in the
same ordered residue field. -/
noncomputable def ActualGenericEightPresentation.canonicalVectors
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 8).toScheme]
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left]
    [IsIntegral (cubicConfigurationBase p hp 8)]
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
    (w : ActualGenericEightPresentation p hp a ha i hz) :
    Fin 8 → Fin 4 →
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).left.residueField (i (genericPoint U)) := by
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
  let φ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField]
      O.residueField (i (genericPoint U)) := fun k =>
    quadraticOrderedLiftCoefficientChangedComponentAlgHom
      p hp a ha (i (genericPoint U)) hz k
  exact fun k j => φ k (w.d.x j)

end PfaffianDescent
