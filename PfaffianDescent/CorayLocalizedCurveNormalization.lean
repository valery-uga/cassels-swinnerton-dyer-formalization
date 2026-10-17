import PfaffianDescent.CorayFiniteTypeNormalization
import PfaffianDescent.CorayGroundResidueCurveDefect
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Actual finite normalization at actual affine curve points

The actual normalization commutes with localization by the installed proof.
The actual finite-type characteristic-zero normalization theorem then gives
finite normalization at every actual prime localization. The literal local
normalization defect is consequently a finite module.

Finiteness here means actual Module.Finite over the local curve ring. It does
not assert finite composition length or identify a global genus correction.

STATUS: UNVERIFIED source only. Root owns compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray

open Algebra Module MvPolynomial
open scoped nonZeroDivisors

/-- Actual finite normalization at a prime localization of an actual
finite-type characteristic-zero domain. No finite-normalization certificate
is a premise; both finiteness and localization are constructed internally. -/
theorem finiteNormalization_pointLocalization_of_finiteType_charZero
    (K A : Type*) [Field K] [CharZero K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A]
    (P : Ideal A) [P.IsPrime] :
    Module.Finite (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))) := by
  let L := Localization.AtPrime P
  let F := FractionRing A
  let D := integralClosure A F
  let E := integralClosure L F
  letI : Module.Finite A D := finiteNormalization_of_finiteType_charZero K A
  letI : IsLocalization (Algebra.algebraMapSubmonoid F P.primeCompl) F := by
    apply IsLocalization.of_le_isUnit
    rintro f ⟨a, ha, rfl⟩
    apply isUnit_iff_ne_zero.mpr
    apply (map_ne_zero_iff _ (IsFractionRing.injective A F)).mpr
    exact mem_nonZeroDivisors_iff_ne_zero.mp (P.primeCompl_le_nonZeroDivisors ha)
  let i : D →ₐ[A] E := (integralClosure A F).val.codRestrict
    (E.restrictScalars A) (fun y => y.property.tower_top)
  letI : Algebra D E := i.toRingHom.toAlgebra
  letI : IsScalarTower A D E :=
    IsScalarTower.of_algebraMap_eq (fun a => (i.commutes a).symm)
  letI : IsScalarTower D E F := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsLocalization (Algebra.algebraMapSubmonoid D P.primeCompl) E :=
    IsLocalization.integralClosure (R := A) (S := F) (Rf := L) (Sf := F) P.primeCompl
  letI : Module.Finite L E := Module.Finite.of_isLocalization A D P.primeCompl
  exact Module.Finite.equiv
    ((FractionRing.algEquiv (A := L) F).symm.mapIntegralClosure.toLinearEquiv)

/-- Actual finite normalization of the literal integral affine intersection
ring in characteristic zero. The finite-type hypothesis is intrinsic to
its actual three-variable polynomial quotient. -/
theorem affineCurve_finiteNormalization_charZero
    {M : Type*} [Field M] [CharZero M]
    (p q : MvPolynomial (Fin 3) M) [hcurve : (affineCurveIdeal p q).IsPrime] :
    Module.Finite (affineCurveRing p q)
      (integralClosure (affineCurveRing p q) (FractionRing (affineCurveRing p q))) :=
  finiteNormalization_of_finiteType_charZero M (affineCurveRing p q)

/-- Every actual prime localization of that literal integral curve has
actual finite normalization, internally obtained from its polynomial ring. -/
theorem affineCurve_point_finiteNormalization_charZero
    {M : Type*} [Field M] [CharZero M]
    (p q : MvPolynomial (Fin 3) M) [hcurve : (affineCurveIdeal p q).IsPrime]
    (P : Ideal (affineCurveRing p q)) [P.IsPrime] :
    Module.Finite (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))) :=
  finiteNormalization_pointLocalization_of_finiteType_charZero M (affineCurveRing p q) P

/-- The literal normalization defect at an actual integral curve point is
an actual finite module. Finite composition length is a further theorem. -/
theorem affineCurve_point_normalizationDefect_finite_charZero
    {M : Type*} [Field M] [CharZero M]
    (p q : MvPolynomial (Fin 3) M) [hcurve : (affineCurveIdeal p q).IsPrime]
    (P : Ideal (affineCurveRing p q)) [P.IsPrime] :
    Module.Finite (Localization.AtPrime P)
      (localNormalizationDefect (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))) := by
  letI := affineCurve_point_finiteNormalization_charZero p q P
  infer_instance

/-- Actual finite normalization at residue-field points of the selected
GROUND curve. Characteristic zero of the residue extension is derived from
its actual field inclusion, not supplied separately. -/
theorem groundCurve_actualResiduePoint_normalizationDefect_finite_charZero
    {K M : Type*} [Field K] [CharZero K] [Field M] [Algebra K M]
    (p q : MvPolynomial (Fin 4) K) (anchor : Fin 4)
    [hcurve : (affineCurveIdeal
      (normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) p))
      (normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) q))).IsPrime]
    (P : Ideal (affineCurveRing
      (normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) p))
      (normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) q)))) [P.IsPrime] :
    Module.Finite (Localization.AtPrime P)
      (localNormalizationDefect (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))) := by
  letI : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  exact affineCurve_point_normalizationDefect_finite_charZero _ _ P

end PfaffianDescent.Coray
