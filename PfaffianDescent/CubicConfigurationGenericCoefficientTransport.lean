import PfaffianDescent.CubicElevenPointNativeGenericInterpolation
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridAffineFieldValues

/-! Literal original-field coefficients agree with the actual generic
unordered configuration coefficients at any ordered field point over it. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicConfigurationGeneric_fieldPoint_coefficients
    {K E : Type u} [Field K] [Field E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp n ≫
      cubicConfigurationToBase p hp n)
    (c : Spec (.of E) ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left)
    (β : (cubicConfigurationBase p hp n).functionField →+* E)
    (hβ : Spec.map (CommRingCat.ofHom β) ≫
        (cubicConfigurationBase p hp n).fromSpecStalk
          (genericPoint (cubicConfigurationBase p hp n)) =
      c ≫ configurationQuotientMap (equationIdeal p hp) n) :
    β.comp a.hom =
      (Spec.preimage (c ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom)).hom := by
  have hbase : configurationQuotientMap (equationIdeal p hp) n ≫
      cubicConfigurationToBase p hp n =
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom :=
    configurationQuotientMap_toBase (equationIdeal p hp) n
  have hschemes : Spec.map (CommRingCat.ofHom (β.comp a.hom)) =
      c ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom := by
    change Spec.map (a ≫ CommRingCat.ofHom β) = _
    rw [Spec.map_comp, ha, ← Category.assoc, hβ, Category.assoc, hbase]
  have hpre := congrArg Spec.preimage hschemes
  rw [Spec.preimage_map] at hpre
  exact congrArg CommRingCat.Hom.hom hpre

theorem cubicConfigurationGeneric_affineFieldPoint_coefficients
    {K E : Type u} [Field K] [Field E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp n ≫
      cubicConfigurationToBase p hp n)
    {U : Scheme.{u}} [IsAffine U]
    (i : U ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left)
    (h : Γ(U, ⊤) →+* E) (b : K →+* Γ(U, ⊤))
    (hb : b = voisinDegreeTenSelectedAvoidance_affineBaseRingMap U
      (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom))
    (β : (cubicConfigurationBase p hp n).functionField →+* E)
    (hβ : Spec.map (CommRingCat.ofHom β) ≫
        (cubicConfigurationBase p hp n).fromSpecStalk
          (genericPoint (cubicConfigurationBase p hp n)) =
      (voisinDegreeTenSelectedAvoidance_affineFieldPoint h ≫ i) ≫
        configurationQuotientMap (equationIdeal p hp) n) :
    h.comp b = β.comp a.hom := by
  have hn := cubicConfigurationGeneric_fieldPoint_coefficients p hp n a ha
    (voisinDegreeTenSelectedAvoidance_affineFieldPoint h ≫ i) β hβ
  have hv := voisinDegreeTenSelectedAvoidance_affineFieldPoint_baseCoefficientHom
    h (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom) b hb
  rw [Category.assoc] at hn
  exact hv.trans hn.symm

end PfaffianDescent
