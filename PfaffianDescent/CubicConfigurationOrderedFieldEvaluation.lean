import PfaffianDescent.CubicConfigurationOrderedFieldComponents

/-! Actual component algebra maps of the coefficient-changed finite
configuration, with exact base and marked-point compatibility. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

variable {K E : Type u} [Field K] [Field E]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
variable [hB : IsIntegral (cubicConfigurationBase p hp n)]
variable (c : Spec (.of E) ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left)
variable (β : (cubicConfigurationBase p hp n).functionField →+* E)
variable (hβ : Spec.map (CommRingCat.ofHom β) ≫
    (cubicConfigurationBase p hp n).fromSpecStalk
      (genericPoint (cubicConfigurationBase p hp n)) =
  c ≫ configurationQuotientMap (equationIdeal p hp) n)
variable (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp n).functionField)
variable (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp n ≫
  cubicConfigurationToBase p hp n)

def cubicConfigurationOrderedFieldComponentAlgHom (k : Fin n) :
    let F := (cubicConfigurationBase p hp n).functionField
    let D := cubicConfigurationGenericFiniteSubscheme p hp n a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap p hp n a ha
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra F E := β.toAlgebra
    Γ(D.val.subscheme, ⊤) →ₐ[F] E := by
  dsimp only
  let F := (cubicConfigurationBase p hp n).functionField
  let D := cubicConfigurationGenericFiniteSubscheme p hp n a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp n a ha
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra F E := β.toAlgebra
  exact finiteSchemePointAlgHom pD
    (cubicConfigurationOrderedFieldCoefficientChangedComponentPoint p hp n c β hβ a ha k)
    β (cubicConfigurationOrderedFieldCoefficientChangedComponentPoint_toBase
      p hp n c β hβ a ha k)

theorem cubicConfigurationOrderedFieldComponentAlgHom_spec_comp
    (k : Fin n) {Y : Scheme.{u}}
    (j : (cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subscheme ⟶ Y) :
    let F := (cubicConfigurationBase p hp n).functionField
    let D := cubicConfigurationGenericFiniteSubscheme p hp n a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap p hp n a ha
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra F E := β.toAlgebra
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    Spec.map (CommRingCat.ofHom
        (cubicConfigurationOrderedFieldComponentAlgHom p hp n c β hβ a ha k).toRingHom) ≫
      D.val.subscheme.isoSpec.inv ≫ j =
        cubicConfigurationOrderedFieldCoefficientChangedComponentPoint p hp n c β hβ a ha k ≫ j := by
  dsimp only
  let F := (cubicConfigurationBase p hp n).functionField
  let D := cubicConfigurationGenericFiniteSubscheme p hp n a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp n a ha
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra F E := β.toAlgebra
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  exact finiteSchemePointAlgHom_spec_comp pD
    (cubicConfigurationOrderedFieldCoefficientChangedComponentPoint p hp n c β hβ a ha k)
    β (cubicConfigurationOrderedFieldCoefficientChangedComponentPoint_toBase
      p hp n c β hβ a ha k) j

theorem cubicConfigurationOrderedFieldComponentAlgHom_actualMarkedPoint (k : Fin n) :
    let F := (cubicConfigurationBase p hp n).functionField
    let D := cubicConfigurationGenericFiniteSubscheme p hp n a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap p hp n a ha
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra F E := β.toAlgebra
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    Spec.map (CommRingCat.ofHom
        (cubicConfigurationOrderedFieldComponentAlgHom p hp n c β hβ a ha k).toRingHom) ≫
      D.val.subscheme.isoSpec.inv ≫ cubicConfigurationCoefficientChangedAmbientMap p hp n a ha =
    ((c ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) n k).left) ≫
      hypersurfaceToAmbient p hp := by
  dsimp only
  rw [cubicConfigurationOrderedFieldComponentAlgHom_spec_comp]
  exact cubicConfigurationOrderedFieldCoefficientChangedComponentPoint_toMarkedPoint
    p hp n c β hβ a ha k

end PfaffianDescent
