import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceFixedCurve
import PfaffianDescent.VoisinGenericCubicPoint

/-! # The genuine generic-sixteen fixed-curve dichotomy

A failed cubic avoidance condition gives an actual prime curve on the
coefficient-changed surface. The universal generic sixteen-point scheme is
one field point, so this curve misses it or contains the whole finite scheme.
No degree-ten completion is identified with the generic sixteen-point scheme.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- For the literal universal generic sixteen-point configuration, failed
selected cubic avoidance constructs its nonempty prime common curve and the
scheme-theoretic all-or-none alternative. -/
theorem voisinDegreeTenSelectedAvoidance_genericSixteen_fixedCurve_dichotomy
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₆ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 16)
    [Etale (D₁₆.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 16) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 16 D₁₆
    ∀ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 16).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 16 ≫ cubicConfigurationToBase p hp 16),
      let F := (cubicConfigurationBase p hp 16).functionField
      let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
      letI : IsFinite (D.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
      ∀ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (q : MvPolynomial (Fin 4) F),
        q.IsHomogeneous 3 → IsRelPrime (p.map a.hom) q →
        (¬ ∀ P ∈ associatedPrimes
            (MvPolynomial (Fin 4) F ⧸ Ideal.span ({p.map a.hom, q} : Set _))
            (MvPolynomial (Fin 4) F ⧸ Ideal.span ({p.map a.hom, q} : Set _)),
          ∃ r ∈ homogeneousVanishingPolynomialSubmodule
            (K := F) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 3,
            Ideal.Quotient.mk (Ideal.span ({p.map a.hom, q} : Set _)) r ∉ P) →
        ∃ (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
          (hCp : p.map a.hom ∈ C.toIdeal),
          C.toIdeal.IsPrime ∧ C.toIdeal.height = 2 ∧
          Ideal.span ({p.map a.hom, q} : Set (MvPolynomial (Fin 4) F)) ≤ C.toIdeal ∧
          homogeneousVanishingPolynomialSubmodule
              (K := F) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 3 ≤
            Submodule.restrictScalars F C.toIdeal ∧
          Nonempty (scheme C) ∧
          (IsEmpty (pullback
              (homogeneousFixedCurveToCubic (p.map a.hom) (hp.map a.hom) C hCp)
              D.val.subschemeι : Scheme.{u}) ∨
            ∃ h : D.val.subscheme ⟶ scheme C,
              h ≫ homogeneousFixedCurveToCubic (p.map a.hom) (hp.map a.hom) C hCp =
                D.val.subschemeι) := by
  letI : IsIntegral (cubicConfigurationBase p hp 16) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 16 D₁₆
  intro a ha
  dsimp only
  let F := (cubicConfigurationBase p hp 16).functionField
  let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
  letI : IsFinite (D.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫
    hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
  letI : FiniteDimensional F Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite (D.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
  letI : CharZero F := charZero_cubicConfigurationFunctionField_of_flat p hp 16
  letI : Infinite F := CharZero.infinite F
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 16 a
  letI : IsIntegral (orderedFamilyConfigurationOver
      (toBase (equationIdeal p hp)) 16).left :=
    isIntegral_orderedCubicConfiguration_of_smooth_of_finiteEtaleSubscheme
      p hp hp0 16 D₁₆
  intro x q hq hrel hfailure
  obtain ⟨C, hCp, hprime, -, hheight, hspan, hW, hnonempty, hclosed⟩ :=
    voisinDegreeTenSelectedAvoidance_exists_fixedCurve_of_failure
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationCoefficientChange_ne_zero p hp 16 a hp0) x q hq hrel hfailure
  letI : IsClosedImmersion
      (homogeneousFixedCurveToCubic (p.map a.hom) (hp.map a.hom) C hCp) := hclosed
  exact ⟨C, hCp, hprime, hheight, hspan, hW, hnonempty,
    cubicConfigurationGenericFiniteSubscheme_isEmpty_pullback_or_factors p hp 16 a ha
      0 (homogeneousFixedCurveToCubic (p.map a.hom) (hp.map a.hom) C hCp)⟩

end PfaffianDescent
