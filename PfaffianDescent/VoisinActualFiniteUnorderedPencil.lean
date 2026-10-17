import PfaffianDescent.VoisinActualCanonicalMinor
import PfaffianDescent.VoisinFiniteIntrinsicUnorderedPencil
import PfaffianDescent.VoisinSelectedCanonicalCubicCoefficients

/-! Descend finite intrinsic intersections for actual generic eight-point
presentations to the unordered coefficient field. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The cubic in the canonical intrinsic ideal is the scalar extension of
the cubic over the unordered configuration function field. -/
theorem ActualGenericEightPresentation.canonicalIntrinsicIdeal_baseChange
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme]
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
    let Q := cubicConfigurationBase p hp 8
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left
    let b := quadraticOrderedLiftFunctionFieldHom p hp (i (genericPoint U)) hz
    letI : Algebra Q.functionField (O.residueField (i (genericPoint U))) :=
      b.toAlgebra
    intrinsicEightPointTripleHomogeneousIdeal
      ((p.map a.hom).map (algebraMap Q.functionField
        (O.residueField (i (genericPoint U)))))
      ((hp.map a.hom).map (algebraMap Q.functionField
        (O.residueField (i (genericPoint U)))))
      (w.canonicalVectors p hp a ha i hz) =
    intrinsicEightPointTripleHomogeneousIdeal
      (p.map ((Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
        (orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 8).hom)).hom))
      (hp.map ((Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
        (orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 8).hom)).hom))
      (w.canonicalVectors p hp a ha i hz) := by
  dsimp only
  let Q := cubicConfigurationBase p hp 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let b := quadraticOrderedLiftFunctionFieldHom p hp (i (genericPoint U)) hz
  letI : Algebra Q.functionField (O.residueField (i (genericPoint U))) :=
    b.toAlgebra
  let β : K →+* O.residueField (i (genericPoint U)) :=
    (Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).hom)).hom
  have hcoeff :
      (algebraMap Q.functionField
        (O.residueField (i (genericPoint U)))).comp a.hom = β := by
    change b.comp a.hom = β
    exact eq_of_heq (cubicOrderedPointOverGeneric_selectedCubicCoefficients
      p hp a ha i (i (genericPoint U)) hz)
  have hpoly : (p.map a.hom).map
      (algebraMap Q.functionField
        (O.residueField (i (genericPoint U)))) = p.map β := by
    rw [MvPolynomial.map_map, hcoeff]
  apply HomogeneousIdeal.ext
  rw [intrinsicEightPointTripleHomogeneousIdeal_toIdeal,
    intrinsicEightPointTripleHomogeneousIdeal_toIdeal]
  exact congrArg (fun t => intrinsicEightPointTripleIdeal t
    (w.canonicalVectors p hp a ha i hz)) hpoly

/-- The canonical vectors of an actual rank-eight presentation yield two
independent quadrics whose cubic intersection is finite over the unordered
generic configuration field, provided the canonical ordered intersection
is finite. -/
theorem ActualGenericEightPresentation.exists_finiteUnorderedTriple
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme]
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
    (w : ActualGenericEightPresentation p hp a ha i hz)
    [IsFinite (toBase (intrinsicEightPointTripleHomogeneousIdeal
      (p.map ((Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
        (orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 8).hom)).hom))
      (hp.map ((Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
        (orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 8).hom)).hom))
      (w.canonicalVectors p hp a ha i hz)))] :
    ∃ q : Fin 2 → homogeneousSubmodule (Fin 4)
        (cubicConfigurationBase p hp 8).functionField 2,
      LinearIndependent (cubicConfigurationBase p hp 8).functionField q ∧
      IsFinite (relativeTripleIntersectionToBase
        (p.map a.hom) (q 0).1 (q 1).1
        (hp.map a.hom) (q 0).2 (q 1).2) := by
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
  have hφ : Function.Injective (fun t : Γ(D.val.subscheme, ⊤) =>
      fun k => φ k t) :=
    eight_component_algHom_joint_injective_of_quadraticFrame_detection
      w.d.x hA φ w.d.detects
  obtain ⟨m, hm⟩ := w.exists_canonical_unitQuadraticMinor p hp a ha i hz
  have hideal := w.canonicalIntrinsicIdeal_baseChange p hp a ha i hz
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
    rw [hideal]
    infer_instance
  letI := hfinite
  obtain ⟨q, hq, _, hfin⟩ :=
    exists_rankEight_finiteUnorderedTriple_of_finiteIntrinsic
      w.d.x hA φ hφ m hm (p.map a.hom) (hp.map a.hom)
  exact ⟨q, hq, hfin⟩

end PfaffianDescent
