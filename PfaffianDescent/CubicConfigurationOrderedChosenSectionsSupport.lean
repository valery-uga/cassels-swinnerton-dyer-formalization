import PfaffianDescent.SerreActualChosenMarkedSectionsCompatibility
import PfaffianDescent.CubicConfigurationOrderedFieldCoefficientMarkedIdentification

/-! Ordered native support identification for a typed section record. Its
coefficient-base identity is derived internally from the record and parameter
maps, while the original-coordinate identity comes from the actual old seed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[irreducible]
def cubicConfigurationOrderedThreeChosenSections_identification
    {K E : Type u} [Field K] [CharZero K] [Field E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
    [IsIntegral (cubicConfigurationBase p hp 3)]
    (c : Spec (.of E) ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    (β : (cubicConfigurationBase p hp 3).functionField →+* E)
    (hβ : Spec.map (CommRingCat.ofHom β) ≫
      (cubicConfigurationBase p hp 3).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 3)) =
      c ≫ configurationQuotientMap (equationIdeal p hp) 3)
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 3).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫ cubicConfigurationToBase p hp 3) :=
  let F := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  letI : Algebra F E := β.toAlgebra
  let x := hypersurfaceToBase (p.map a.hom) (hp.map a.hom)
  let f := cubicPointTraceFieldBaseChangeCubicCoefficientMap a.hom p hp
  let identify := cubicConfigurationOrderedThreeFieldCoefficientMarked_identification
    p hp hp0 c β hβ a ha
  fun {P Q Z : Scheme.{u}}
    (pp : P ⟶ Spec (.of F)) (qp : Q ⟶ Spec (.of F))
    (zero : Z ⟶ pullback x pp)
    [IsClosedImmersion zero]
    (q : Spec (.of F) ⟶ Q) (hq : q ≫ qp = 𝟙 _)
    (v : Q ⟶ P) (hv : v ≫ pp = qp)
    (d : SerreActualChosenMarkedSections x pp zero
      ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v))
    (n : Fin 3)
    (hOriginal : serreActualChosenFibre_marked x pp zero
        ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v) d.δ n ≫ f =
      (c ≫ (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).left) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 n).left) =>
    identify (serreActualChosenFibre_marked x pp zero
      ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v) d.δ n)
      (serreActualChosenMarkedSections_marked_toFieldBase x pp qp zero q hq v hv d n)
      n hOriginal

end PfaffianDescent
