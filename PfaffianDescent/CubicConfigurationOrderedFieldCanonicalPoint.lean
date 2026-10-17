import PfaffianDescent.CubicConfigurationOrderedFieldEvaluation
import AllCharacteristics.FiniteSubschemeRank

/-! The native canonical spectrum of the finite configuration has the
same actual marked points as its labeled component algebra maps. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicConfigurationOrderedFieldComponentAlgHom_canonicalPoint_actualMarkedPoint
    {K E : Type u} [Field K] [Field E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
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
    let P := p.map a.hom
    let hP := hp.map a.hom
    let D := cubicConfigurationGenericFiniteSubscheme p hp n a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap p hp n a ha
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra F E := β.toAlgebra
    let i := finiteSubschemeDatumSpecMap (hypersurfaceToBase P hP) D
    Spec.map (CommRingCat.ofHom
        (cubicConfigurationOrderedFieldComponentAlgHom p hp n c β hβ a ha k).toRingHom) ≫
      i ≫ hypersurfaceToAmbient P hP ≫ ambientCoefficientMap a.hom =
      ((c ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) n k).left) ≫
        hypersurfaceToAmbient p hp := by
  dsimp only
  simpa only [finiteSubschemeDatumSpecMap, cubicConfigurationCoefficientChangedAmbientMap,
    Category.assoc] using
    cubicConfigurationOrderedFieldComponentAlgHom_actualMarkedPoint p hp n c β hβ a ha k

end PfaffianDescent
