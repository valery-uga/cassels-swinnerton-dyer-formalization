import PfaffianDescent.VoisinSelectedOrderedGenericField
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! The determinant-open chart and its original affine chart share a fraction field. -/

namespace PfaffianDescent

open AlgebraicGeometry

universe u

/-- Localizing an integral domain at a nonzero element does not change its
fraction field. -/
noncomputable def fractionRingAwayEquiv
    {R : Type u} [CommRing R] [IsDomain R]
    (s : R) (hs : s ≠ 0) :
    FractionRing (Localization.Away s) ≃+* FractionRing R := by
  let S := Localization.Away s
  have hsunit : IsUnit (algebraMap R (FractionRing R) s) :=
    isUnit_iff_ne_zero.mpr (by
      simpa only [map_zero] using
        ((IsFractionRing.injective R (FractionRing R)).ne_iff.mpr hs))
  let f : S →+* FractionRing R :=
    IsLocalization.Away.lift s hsunit
  letI : Algebra S (FractionRing R) := f.toAlgebra
  haveI : IsScalarTower R S (FractionRing R) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext r
    exact (IsLocalization.Away.lift_eq (S := S) s hsunit r).symm
  letI : IsFractionRing S (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers s) S (FractionRing R)
  exact (FractionRing.algEquiv S (FractionRing R)).toRingEquiv

/-- The fraction-field equivalence preserves the original chart's regular
functions through the localization map. -/
theorem fractionRingAwayEquiv_algebraMap
    {R : Type u} [CommRing R] [IsDomain R]
    (s : R) (hs : s ≠ 0) (r : R) :
    fractionRingAwayEquiv s hs
      (algebraMap (Localization.Away s)
        (FractionRing (Localization.Away s))
        (algebraMap R (Localization.Away s) r)) =
      algebraMap R (FractionRing R) r := by
  let S := Localization.Away s
  have hsunit : IsUnit (algebraMap R (FractionRing R) s) :=
    isUnit_iff_ne_zero.mpr (by
      simpa only [map_zero] using
        ((IsFractionRing.injective R (FractionRing R)).ne_iff.mpr hs))
  let f : S →+* FractionRing R := IsLocalization.Away.lift s hsunit
  letI : Algebra S (FractionRing R) := f.toAlgebra
  haveI : IsScalarTower R S (FractionRing R) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    exact (IsLocalization.Away.lift_eq (S := S) s hsunit a).symm
  letI : IsFractionRing S (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers s) S (FractionRing R)
  change (FractionRing.algEquiv S (FractionRing R))
    (algebraMap S (FractionRing S) (algebraMap R S r)) =
      algebraMap R (FractionRing R) r
  rw [AlgEquiv.commutes]
  exact IsLocalization.Away.lift_eq (S := S) s hsunit r

/-- The selected determinant-open chart's fraction field is the residue
field of its image generic point in the ordered configuration scheme. -/
noncomputable def affineOpenImmersion_localizedFractionEquivGenericImageResidueField
    {U O : Scheme.{u}} [IsAffine U] [IsIntegral U] [IsIntegral O]
    (i : U ⟶ O) [IsOpenImmersion i]
    (s : Γ(U, ⊤)) (hs : s ≠ 0) :
    FractionRing (Localization.Away s) ≃+*
      O.residueField (i (genericPoint U)) :=
  (fractionRingAwayEquiv s hs).trans
    (affineOpenImmersion_fractionEquivGenericImageResidueField i)

/-- Under the localized-field equivalence, an original chart function is
evaluated at the same generic chart point. -/
theorem affineOpenImmersion_localizedFractionEquivGenericImageResidueField_algebraMap
    {U O : Scheme.{u}} [IsAffine U] [IsIntegral U] [IsIntegral O]
    (i : U ⟶ O) [IsOpenImmersion i]
    (s : Γ(U, ⊤)) (hs : s ≠ 0) (r : Γ(U, ⊤)) :
    (i.residueFieldMap (genericPoint U)).hom
      (affineOpenImmersion_localizedFractionEquivGenericImageResidueField i s hs
        (algebraMap (Localization.Away s)
          (FractionRing (Localization.Away s))
          (algebraMap Γ(U, ⊤) (Localization.Away s) r))) =
      U.Γevaluation (genericPoint U) r := by
  rw [affineOpenImmersion_localizedFractionEquivGenericImageResidueField,
    RingEquiv.trans_apply, fractionRingAwayEquiv_algebraMap]
  exact affineOpenImmersion_fractionEquivGenericImageResidueField_algebraMap i r

end PfaffianDescent
