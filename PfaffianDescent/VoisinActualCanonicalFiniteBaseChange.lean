import PfaffianDescent.VoisinActualFiniteUnorderedPencil

/-! Finiteness of the actual canonical intrinsic fiber expressed over the
unordered configuration function field. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ActualGenericEightPresentation.canonicalIntrinsicFinite_baseChange
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
    let Q := cubicConfigurationBase p hp 8
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left
    let b := quadraticOrderedLiftFunctionFieldHom p hp (i (genericPoint U)) hz
    letI : Algebra Q.functionField (O.residueField (i (genericPoint U))) :=
      b.toAlgebra
    IsFinite (toBase (intrinsicEightPointTripleHomogeneousIdeal
      ((p.map a.hom).map (algebraMap Q.functionField
        (O.residueField (i (genericPoint U)))))
      ((hp.map a.hom).map (algebraMap Q.functionField
        (O.residueField (i (genericPoint U)))))
      (w.canonicalVectors p hp a ha i hz))) := by
  dsimp only
  let Q := cubicConfigurationBase p hp 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let b := quadraticOrderedLiftFunctionFieldHom p hp (i (genericPoint U)) hz
  letI : Algebra Q.functionField (O.residueField (i (genericPoint U))) :=
    b.toAlgebra
  have hideal := w.canonicalIntrinsicIdeal_baseChange p hp a ha i hz
  rw [hideal]
  infer_instance

end PfaffianDescent
