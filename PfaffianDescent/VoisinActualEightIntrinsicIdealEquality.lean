import PfaffianDescent.VoisinActualEightComparison

/-! Intrinsic-ideal equality for the actual generic eight-point vectors. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual selected chart vectors and the canonical generic rank-eight
algebra component vectors define the same intrinsic eight-point ideal in
the ordered generic residue field. -/
theorem ActualGenericEightPresentation.intrinsicIdeal_eq
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 8).toScheme]
    [hordered : IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left]
    [hbase : IsIntegral (cubicConfigurationBase p hp 8)]
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
    let bCan := quadraticOrderedLiftFunctionFieldHom p hp
      (i (genericPoint U)) hz
    let bSel : K →+* O.residueField (i (genericPoint U)) :=
      (Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom)).hom
    letI : Algebra Q.functionField (O.residueField (i (genericPoint U))) :=
      bCan.toAlgebra
    letI : Algebra K (O.residueField (i (genericPoint U))) := bSel.toAlgebra
    intrinsicEightPointTripleHomogeneousIdeal
      (p.map bSel) (hp.map bSel)
      (w.canonicalVectors p hp a ha i hz) =
    intrinsicEightPointTripleHomogeneousIdeal
      (p.map bSel) (hp.map bSel)
      (w.selectedVectors p hp a ha i hz) := by
  dsimp only
  let Q := cubicConfigurationBase p hp 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let bCan := quadraticOrderedLiftFunctionFieldHom p hp
    (i (genericPoint U)) hz
  let bSel : K →+* O.residueField (i (genericPoint U)) :=
    (Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom)).hom
  letI : Algebra Q.functionField (O.residueField (i (genericPoint U))) :=
    bCan.toAlgebra
  letI : Algebra K (O.residueField (i (genericPoint U))) := bSel.toAlgebra
  obtain ⟨c, hx, hy⟩ := w.exists_comparison p hp a ha i hz
  have h := c.intrinsicIdeal_eq a.hom p hp
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q.functionField))
    (p.map bSel) (hp.map bSel)
  rw [hx, hy] at h
  exact h

end PfaffianDescent
