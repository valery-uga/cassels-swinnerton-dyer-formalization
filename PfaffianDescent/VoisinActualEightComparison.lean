import PfaffianDescent.VoisinActualEightPresentation

/-! Actual selected and canonical vectors in one comparison package. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every actual selected/canonical generic-eight presentation yields a
comparison package whose two vector families are exactly its chart and
finite-algebra component vectors. -/
theorem ActualGenericEightPresentation.exists_comparison
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
    ∃ c : EightPointNormalizedComparison (F := O.residueField (i (genericPoint U)))
        a.hom p hp
        (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin 4) Q.functionField)),
      c.x = w.selectedVectors p hp a ha i hz ∧
      c.y = w.canonicalVectors p hp a ha i hz := by
  dsimp only
  rcases w with ⟨zc, hzc, ell, hell, hellzc, t, ht, d⟩
  subst zc
  let Q := cubicConfigurationBase p hp 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let D := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp 8 a ha
  let bCan := quadraticOrderedLiftFunctionFieldHom p hp
    (i (genericPoint U)) hz
  let bSel : K →+* O.residueField (i (genericPoint U)) :=
    (Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom)).hom
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField (i (genericPoint U))) :=
    bCan.toAlgebra
  letI : Algebra K (O.residueField (i (genericPoint U))) := bSel.toAlgebra
  let φ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField]
      O.residueField (i (genericPoint U)) := fun k =>
    quadraticOrderedLiftCoefficientChangedComponentAlgHom
      p hp a ha (i (genericPoint U)) hz k
  let x : Fin 8 → Fin 4 → O.residueField (i (genericPoint U)) :=
    fun k j => (Spec.preimage (openImmersion_genericResidueLift i ≫ t k)).hom
      (linearChartCoordinate (equationIdeal p hp)
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell) hzc j)
  let y : Fin 8 → Fin 4 → O.residueField (i (genericPoint U)) :=
    fun k j => φ k (d.x j)
  obtain ⟨heX, hxOne, hmarkX⟩ :=
    exists_cubicSelectedGeneric_normalizedMarkedFamily
      p hp _ hzc ell hell rfl i hz t ht
  obtain ⟨hyOne, hmarkY⟩ :=
    d.canonicalComponentVectors_markedFamily p hp a ha
      (i (genericPoint U)) hz
  let I : HomogeneousIdeal
    (homogeneousSubmodule (Fin 4) Q.functionField) := ⊥
  let heY : ∀ k, ∀ q ∈ I.toIdeal,
      (eval₂Hom (algebraMap Q.functionField
        (O.residueField (i (genericPoint U)))) (y k)) q = 0 := by
    intro k q hq
    exact (Ideal.mem_bot.mp hq).symm ▸ map_zero _
  let marked : Fin 8 → (Spec (.of (O.residueField (i (genericPoint U)))) ⟶
      Proj (homogeneousSubmodule (Fin 4) K)) := fun k =>
    O.fromSpecResidueField (i (genericPoint U)) ≫
      @AllCharacteristics.UniversalHomogeneous.orderedConfigurationProjectivePoint
        K _ (Fin 4) _ _ _ _ _
        (grading (equationIdeal p hp)) _
        (hypersurfaceToBase p hp) hsep 8
        (hypersurfaceToAmbient p hp) k
  let c := EightPointNormalizedComparison.ofMarkedFamilies
    a.hom p hp I x y ell hell heX hxOne
    d.ell d.ellHomogeneous heY hyOne marked hmarkX hmarkY
  refine ⟨c, ?_, ?_⟩
  · rfl
  · rfl

end PfaffianDescent
