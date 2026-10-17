import PfaffianDescent.CubicConfigurationOrderedFieldEvaluation
import AllCharacteristics.VoisinGenericCubicPoint

/-! The actual generic finite configuration is one field point. Each
native labeled component therefore detects literal coordinate-ring zeros.
-/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicConfigurationOrderedFieldComponentAlgHom_injective
    {K E : Type u} [Field K] [Field E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    [IsIntegral (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) n).left]
    [IsIntegral (cubicConfigurationBase p hp n)]
    (c : Spec (.of E) ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left)
    (β : (cubicConfigurationBase p hp n).functionField →+* E)
    (hβ : Spec.map (CommRingCat.ofHom β) ≫
        (cubicConfigurationBase p hp n).fromSpecStalk
          (genericPoint (cubicConfigurationBase p hp n)) =
      c ≫ configurationQuotientMap (equationIdeal p hp) n)
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp n ≫
      cubicConfigurationToBase p hp n) (k : Fin n) :
    let F := (cubicConfigurationBase p hp n).functionField
    let D := cubicConfigurationGenericFiniteSubscheme p hp n a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap p hp n a ha
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra F E := β.toAlgebra
    Function.Injective (cubicConfigurationOrderedFieldComponentAlgHom p hp n c β hβ a ha k) := by
  dsimp only
  let F := (cubicConfigurationBase p hp n).functionField
  let D := cubicConfigurationGenericFiniteSubscheme p hp n a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp n a ha
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra F E := β.toAlgebra
  letI : Field Γ(D.val.subscheme, ⊤) :=
    (cubicConfigurationGenericFiniteSubscheme_isField p hp n a ha k).toField
  exact (cubicConfigurationOrderedFieldComponentAlgHom p hp n c β hβ a ha k).toRingHom.injective

end PfaffianDescent
