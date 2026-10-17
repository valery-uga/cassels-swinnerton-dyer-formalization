import PfaffianDescent.CubicConfigurationAffineFieldNormalizedComponents
import PfaffianDescent.CubicFieldPointElevenInterpolation
import PfaffianDescent.CubicConfigurationOrderedFieldInjective

/-! The literal canonical generic finite configuration supplies the field,
degree and component identities for the ground cubic restriction kernel. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

local instance {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [hO : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left] :
    IsIntegral (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 11).left := hO

theorem cubicConfigurationGenericFiniteSubscheme_finrank
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp n ≫
      cubicConfigurationToBase p hp n) :
    let D := cubicConfigurationGenericFiniteSubscheme p hp n a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap p hp n a ha
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    finrank (cubicConfigurationBase p hp n).functionField Γ(D.val.subscheme, ⊤) = n := by
  dsimp only
  let D := cubicConfigurationGenericFiniteSubscheme p hp n a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp n a ha
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  rw [finiteSchemeCoefficient_finrank pD]
  exact finiteSubschemeDatum_finiteSchemeRank (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) D

/-- Apply the checked abstract interpolation theorem to the literal native
configuration data. Inferring the proposition avoids repeated conversions
of the large projective scheme and its field structure. -/
abbrev cubicElevenPointCanonicalChart_exists_kernel
    {K E : Type u} [Field K] [Field E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left]
    [IsIntegral (cubicConfigurationBase p hp 11)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 11).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 11 ≫
      cubicConfigurationToBase p hp 11)
    (U : Scheme.{u}) [IsAffine U]
    (iU : U ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left)
    (c : Fin 4 → K)
    (t : Fin 11 → (U ⟶ Spec (.of (Away (grading (equationIdeal p hp))
      (cubicGroundChartClass p hp c)))))
    (ht : ∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp))
        (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c)
        (by decide : 0 < 1) =
      (iU ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 11)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 k).left)
    (b : K →+* Γ(U, ⊤))
    (hb : b = voisinDegreeTenSelectedAvoidance_affineBaseRingMap U
      (iU ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom))
    (x : Fin 11 → Fin 4 → Γ(U, ⊤))
    (hx : x = fun k r => pulledLinearChartCoordinate (equationIdeal p hp)
      (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c) U (t k) r)
    (h : Γ(U, ⊤) →+* E)
    (β : (cubicConfigurationBase p hp 11).functionField →+* E)
    (hβ : Spec.map (CommRingCat.ofHom β) ≫
        (cubicConfigurationBase p hp 11).fromSpecStalk
          (genericPoint (cubicConfigurationBase p hp 11)) =
      (voisinDegreeTenSelectedAvoidance_affineFieldPoint h ≫ iU) ≫
        configurationQuotientMap (equationIdeal p hp) 11)
    (j : Fin 4) (hxj : h (x 0 j) ≠ 0)
    (y : Fin 11 → Fin 4 → E) (scale : Fin 11 → E)
    (hy : ∀ k r, y k r = scale k * h (x k r))
    (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet E)
    (hresidue : ∀ k r, (J k r).fst = y (k.castAdd 8) r)
    (hfull : Function.Surjective (cubicElevenPointFullJetRestriction y J)) :=
  let F := (cubicConfigurationBase p hp 11).functionField
  let P := p.map a.hom
  let hP := hp.map a.hom
  let D := cubicConfigurationGenericFiniteSubscheme p hp 11 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp 11 a ha
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  let L := Γ(D.val.subscheme, ⊤)
  letI : Field L :=
    (cubicConfigurationGenericFiniteSubscheme_isField p hp 11 a ha (0 : Fin 11)).toField
  letI : Algebra F E := β.toAlgebra
  letI : Algebra K E := (h.comp b).toAlgebra
  letI : FiniteDimensional F L := finiteSchemeCoefficient_finite pD
  let i := finiteSubschemeDatumSpecMap (hypersurfaceToBase P hP) D
  let α : Fin 11 → (L →ₐ[F] E) := fun k =>
    cubicConfigurationOrderedFieldComponentAlgHom p hp 11
      (voisinDegreeTenSelectedAvoidance_affineFieldPoint h ≫ iU) β hβ a ha k
  let w : Fin 11 → Fin 4 → E := fun k r => h (x k r)
  have hi : i ≫ hypersurfaceToBase P hP =
      Spec.map (CommRingCat.ofHom (algebraMap F L)) :=
    finiteSubschemeDatumSpecMap_toBase (hypersurfaceToBase P hP) D
  have hL : finrank F L = 11 := cubicConfigurationGenericFiniteSubscheme_finrank p hp 11 a ha
  let hnormalized := cubicConfigurationAffineField_normalized_components
    p hp 11 a ha U iU c t ht b hb x hx h β hβ
  let he := Classical.choose hnormalized
  let hn := Classical.choose (Classical.choose_spec hnormalized)
  let hpoint := Classical.choose_spec (Classical.choose_spec hnormalized)
  cubicFieldPointElevenInterpolation_exists_chart_kernel a.hom p hp P hP i hi hL
    α w (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c) he hn hpoint
    j hxj y scale hy J hresidue hfull

end PfaffianDescent
