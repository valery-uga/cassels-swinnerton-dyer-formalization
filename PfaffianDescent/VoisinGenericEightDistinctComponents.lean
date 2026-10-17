import PfaffianDescent.VoisinGenericQuadraticEvaluation

/-! Distinct algebra homomorphisms from the actual ordered generic lift. -/

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective AllCharacteristics.UniversalHomogeneous
universe u

/-- The actual transported ordered generic components induce eight distinct
homomorphisms from the coefficient algebra to the ordered residue field. -/
theorem quadraticOrderedLiftCoefficientChangedComponentAlgHom_injective
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap cubic hcubic 8 ≫
        cubicConfigurationToBase cubic hcubic 8)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField)) :
    let Q := cubicConfigurationBase cubic hcubic 8
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
    let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    Function.Injective (fun i : Fin 8 =>
      quadraticOrderedLiftCoefficientChangedComponentAlgHom
        cubic hcubic a ha z hz i) := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 8).left
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
  let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  intro i j hij
  have h := congrArg
    (fun q : Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z =>
      Spec.map (CommRingCat.ofHom q.toRingHom) ≫
        D.val.subscheme.isoSpec.inv ≫
          cubicConfigurationCoefficientChangedAmbientMap cubic hcubic 8 a ha) hij
  have hi := quadraticOrderedLiftCoefficientChangedComponentAlgHom_spec_comp
    cubic hcubic a ha z hz i
    (cubicConfigurationCoefficientChangedAmbientMap cubic hcubic 8 a ha)
  have hj := quadraticOrderedLiftCoefficientChangedComponentAlgHom_spec_comp
    cubic hcubic a ha z hz j
    (cubicConfigurationCoefficientChangedAmbientMap cubic hcubic 8 a ha)
  have hp := hi.symm.trans (h.trans hj)
  rw [quadraticOrderedLiftCoefficientChangedComponentPoint_toAmbientProjective
      cubic hcubic a ha z hz i,
    quadraticOrderedLiftCoefficientChangedComponentPoint_toAmbientProjective
      cubic hcubic a ha z hz j] at hp
  have hmark := orderedConfigurationFieldPoint_coordinates_comp_injective
    (hypersurfaceToBase cubic hcubic) 8
    (hypersurfaceToAmbient cubic hcubic)
    ((orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left.fromSpecResidueField z)
  unfold orderedConfigurationProjectivePoint at hp
  exact hmark hp

end PfaffianDescent
