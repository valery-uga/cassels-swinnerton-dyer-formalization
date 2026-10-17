import PfaffianDescent.VoisinFixedCurveFlatEquationModel
import PfaffianDescent.ProjectiveQuotientRelativeGlobalIdealBaseChange
import PfaffianDescent.ProjectiveQuotientIdealSheafComap

/-!
# Ideal sheaf of a spread-out fixed curve

The flat projective model of a fixed generic curve is a closed subscheme of
the cubic family. Its ideal sheaf in that cubic commutes with arbitrary
coefficient change. In particular, after passing to the configuration
function field, the resulting ideal sheaf is the actual ideal sheaf of the
prescribed generic curve. This comparison alone does not descend the curve's
Picard class to the ground-field cubic.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Flatness of a projective curve family gives arbitrary coefficient base
change for its actual ideal sheaf inside a cubic family. -/
theorem homogeneousModelToCubic_isIso_idealBaseChange_of_flatToBase
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hpJ : p ∈ J.toIdeal) (hflat : Flat (toBase J)) :
    let I := equationIdeal p hp
    let cI := projectiveCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
      (coefficientChangedHomogeneousIdeal_toIdeal f I)
    let i := homogeneousModelToCubic p hp J hpJ
    IsIso (@closedImmersionIdealBaseChangeHom _ _ _ cI i
      (homogeneousModelToCubic_closedImmersion p hp J hpJ)) := by
  exact isIso_projectiveQuotient_globalIdealBaseChange_of_flatToBase
    f (equationIdeal p hp) J
    (by
      apply Ideal.span_le.mpr
      rintro q rfl
      exact hpJ) hflat

/-- For a contracted model over a principal open, its generic homogeneous
ideal is exactly the prescribed ideal, not merely a subideal. -/
theorem fixedCurve_model_genericIdeal_eq
    {A F : Type u} [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (e : A) (he : e ≠ 0)
    (φ : Localization.Away e →+* F)
    (hcomp : ∀ a : A, φ (algebraMap A (Localization.Away e) a) =
      algebraMap A F a)
    (J : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (Localization.Away e)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hJ : J.toIdeal = Ideal.comap (MvPolynomial.map φ) C.toIdeal) :
    Ideal.map (MvPolynomial.map φ) J.toIdeal = C.toIdeal := by
  letI : IsDomain (Localization.Away e) := Localization.Away.isDomain he
  letI : Algebra (Localization.Away e) F := φ.toAlgebra
  letI : IsScalarTower A (Localization.Away e) F :=
    IsScalarTower.of_algebraMap_eq fun a => (hcomp a).symm
  letI : IsFractionRing (Localization.Away e) F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers e) (Localization.Away e) F
  let M : Submonoid (MvPolynomial (Fin 4) (Localization.Away e)) :=
    (nonZeroDivisors (Localization.Away e)).map
      (MvPolynomial.C : Localization.Away e →+*
        MvPolynomial (Fin 4) (Localization.Away e))
  letI : IsLocalization M (MvPolynomial (Fin 4) F) := by
    dsimp [M]
    infer_instance
  rw [hJ]
  change Ideal.map (algebraMap
      (MvPolynomial (Fin 4) (Localization.Away e))
      (MvPolynomial (Fin 4) F))
    (C.toIdeal.under (MvPolynomial (Fin 4) (Localization.Away e))) = C.toIdeal
  exact IsLocalization.map_under M (MvPolynomial (Fin 4) F) C.toIdeal

/-- The generic ideal sheaf of a flat fixed-curve model is canonically the
ideal sheaf of the prescribed curve in the generic cubic. The canonical
ideal-module base-change map is an isomorphism, and the ideal sheaf data
agree after the actual Cartesian base change. -/
theorem fixedCurve_model_genericIdealSheaf_baseChange
    {A F : Type u} [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (e : A) (he : e ≠ 0)
    (φ : Localization.Away e →+* F)
    (hcomp : ∀ a : A, φ (algebraMap A (Localization.Away e) a) =
      algebraMap A F a)
    (p : MvPolynomial (Fin 4) (Localization.Away e))
    (hp : p.IsHomogeneous 3)
    (J : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (Localization.Away e)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hJ : J.toIdeal = Ideal.comap (MvPolynomial.map φ) C.toIdeal)
    (hpJ : p ∈ J.toIdeal) (hflat : Flat (toBase J)) :
    let cX := projectiveCoefficientMap φ
      (equationIdeal p hp)
      (equationIdeal (MvPolynomial.map φ p) (hp.map φ))
      (equationIdeal_map φ p hp)
    let i := homogeneousModelToCubic p hp J hpJ
    let hpC : MvPolynomial.map φ p ∈ C.toIdeal := by
      change p ∈ Ideal.comap (MvPolynomial.map φ) C.toIdeal
      exact hJ ▸ hpJ
    let iF := homogeneousModelToCubic
      (MvPolynomial.map φ p) (hp.map φ) C hpC
    IsIso (@closedImmersionIdealBaseChangeHom _ _ _ cX i
      (homogeneousModelToCubic_closedImmersion p hp J hpJ)) ∧
      iF.ker = i.ker.comap cX := by
  let hmap := fixedCurve_model_genericIdeal_eq e he φ hcomp J C hJ
  let hpC : MvPolynomial.map φ p ∈ C.toIdeal := by
    change p ∈ Ideal.comap (MvPolynomial.map φ) C.toIdeal
    exact hJ ▸ hpJ
  constructor
  · letI : IsDomain (Localization.Away e) := Localization.Away.isDomain he
    letI : Algebra (Localization.Away e) F := φ.toAlgebra
    letI : IsScalarTower A (Localization.Away e) F :=
      IsScalarTower.of_algebraMap_eq fun a => (hcomp a).symm
    letI : IsFractionRing (Localization.Away e) F :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
        (Submonoid.powers e) (Localization.Away e) F
    have hφFlat : φ.Flat := by
      change Module.Flat (Localization.Away e) F
      exact IsLocalization.flat F (nonZeroDivisors (Localization.Away e))
    haveI hSpecFlat : Flat (Spec.map (CommRingCat.ofHom φ)) :=
      (Flat.SpecMap_iff).2 hφFlat
    haveI hCubicFlat : Flat (projectiveCoefficientMap φ
        (equationIdeal p hp)
        (equationIdeal (MvPolynomial.map φ p) (hp.map φ))
        (equationIdeal_map φ p hp)) := by
      apply MorphismProperty.of_isPullback
        (isPullback_projectiveCoefficientMap φ
          (equationIdeal p hp)
          (equationIdeal (MvPolynomial.map φ p) (hp.map φ))
          (equationIdeal_map φ p hp)).flip
      exact hSpecFlat
    exact @isIso_flatClosedImmersionIdealBaseChangeHom_general _ _ _
      (projectiveCoefficientMap φ
        (equationIdeal p hp)
        (equationIdeal (MvPolynomial.map φ p) (hp.map φ))
        (equationIdeal_map φ p hp)) hCubicFlat
      (homogeneousModelToCubic p hp J hpJ)
      (homogeneousModelToCubic_closedImmersion p hp J hpJ)
  · exact homogeneousModelToCubic_baseChange_ker_eq_comap
      φ p hp J C hpJ hpC hmap

end PfaffianDescent
