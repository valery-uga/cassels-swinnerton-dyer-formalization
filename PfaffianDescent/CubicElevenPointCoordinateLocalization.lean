import PfaffianDescent.CubicPolynomialJetMinorTransport
import Mathlib.RingTheory.Localization.Away.Basic

/-!
Literal localization of the actual common-chart coordinates at the
chosen standard-chart denominators, with exact field specialization.
-/

noncomputable section
namespace PfaffianDescent

universe u v
set_option backward.isDefEq.respectTransparency false

def cubicCoordinateDenominator
    {R : Type u} [CommRing R] (x : Fin 11 → Fin 4 → R) (anchor : Fin 11 → Fin 4) : R :=
  ∏ i, x i (anchor i)

theorem cubicCoordinateDenominator_isUnit_each
    {R : Type u} [CommRing R] (x : Fin 11 → Fin 4 → R) (anchor : Fin 11 → Fin 4)
    (i : Fin 11) :
    IsUnit (algebraMap R (Localization.Away (cubicCoordinateDenominator x anchor))
      (x i (anchor i))) := by
  apply IsLocalization.Away.isUnit_of_dvd (cubicCoordinateDenominator x anchor)
  exact Finset.dvd_prod_of_mem (fun i => x i (anchor i)) (Finset.mem_univ i)

def cubicCoordinateLocalizedVector
    {R : Type u} [CommRing R] (x : Fin 11 → Fin 4 → R) (anchor : Fin 11 → Fin 4) :
    Fin 11 → Fin 4 → Localization.Away (cubicCoordinateDenominator x anchor) :=
  fun i j => (↑(cubicCoordinateDenominator_isUnit_each x anchor i).unit⁻¹ :
    Localization.Away (cubicCoordinateDenominator x anchor)) *
      algebraMap R (Localization.Away (cubicCoordinateDenominator x anchor)) (x i j)

@[simp] theorem cubicCoordinateLocalizedVector_anchor
    {R : Type u} [CommRing R] (x : Fin 11 → Fin 4 → R) (anchor : Fin 11 → Fin 4)
    (i : Fin 11) : cubicCoordinateLocalizedVector x anchor i (anchor i) = 1 :=
  (cubicCoordinateDenominator_isUnit_each x anchor i).val_inv_mul

theorem cubicCoordinateDenominator_specialization_ne_zero
    {R : Type u} [CommRing R] {F : Type v} [Field F]
    (x : Fin 11 → Fin 4 → R) (anchor : Fin 11 → Fin 4) (f : R →+* F)
    (hf : ∀ i, f (x i (anchor i)) ≠ 0) : f (cubicCoordinateDenominator x anchor) ≠ 0 := by
  rw [cubicCoordinateDenominator, map_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hf i)

def cubicCoordinateSpecializationLift
    {R : Type u} [CommRing R] {F : Type v} [Field F]
    (x : Fin 11 → Fin 4 → R) (anchor : Fin 11 → Fin 4) (f : R →+* F)
    (hf : ∀ i, f (x i (anchor i)) ≠ 0) :
    Localization.Away (cubicCoordinateDenominator x anchor) →+* F :=
  IsLocalization.Away.lift (cubicCoordinateDenominator x anchor)
    (isUnit_iff_ne_zero.mpr (cubicCoordinateDenominator_specialization_ne_zero x anchor f hf))

@[simp] theorem cubicCoordinateSpecializationLift_algebraMap
    {R : Type u} [CommRing R] {F : Type v} [Field F]
    (x : Fin 11 → Fin 4 → R) (anchor : Fin 11 → Fin 4) (f : R →+* F)
    (hf : ∀ i, f (x i (anchor i)) ≠ 0) (r : R) :
    cubicCoordinateSpecializationLift x anchor f hf
      (algebraMap R (Localization.Away (cubicCoordinateDenominator x anchor)) r) = f r := by
  exact IsLocalization.Away.lift_eq _ _ r

theorem cubicCoordinateSpecializationLift_vector
    {R : Type u} [CommRing R] {F : Type v} [Field F]
    (x : Fin 11 → Fin 4 → R) (anchor : Fin 11 → Fin 4) (f : R →+* F)
    (hf : ∀ i, f (x i (anchor i)) ≠ 0) (i : Fin 11) (j : Fin 4) :
    cubicCoordinateSpecializationLift x anchor f hf (cubicCoordinateLocalizedVector x anchor i j) =
      (f (x i (anchor i)))⁻¹ * f (x i j) := by
  let g := cubicCoordinateSpecializationLift x anchor f hf
  have hmul := congrArg g (cubicCoordinateDenominator_isUnit_each x anchor i).val_inv_mul
  rw [map_mul, map_one, cubicCoordinateSpecializationLift_algebraMap] at hmul
  have hinv : g (↑(cubicCoordinateDenominator_isUnit_each x anchor i).unit⁻¹) =
      (f (x i (anchor i)))⁻¹ := (mul_eq_one_iff_eq_inv₀ (hf i)).mp hmul
  change g (_ * _) = _
  rw [map_mul, hinv, cubicCoordinateSpecializationLift_algebraMap]

theorem cubicCoordinateFieldMap_vector
    {R : Type u} [CommRing R] {F : Type v} [Field F]
    (x : Fin 11 → Fin 4 → R) (anchor : Fin 11 → Fin 4)
    (g : Localization.Away (cubicCoordinateDenominator x anchor) →+* F)
    (i : Fin 11) (j : Fin 4) :
    g (cubicCoordinateLocalizedVector x anchor i j) =
      (g (algebraMap R (Localization.Away (cubicCoordinateDenominator x anchor))
        (x i (anchor i))))⁻¹ *
      g (algebraMap R (Localization.Away (cubicCoordinateDenominator x anchor)) (x i j)) := by
  have hf := (cubicCoordinateDenominator_isUnit_each x anchor i).map g
  have hmul := congrArg g (cubicCoordinateDenominator_isUnit_each x anchor i).val_inv_mul
  rw [map_mul, map_one] at hmul
  have hinv := (mul_eq_one_iff_eq_inv₀ hf.ne_zero).mp hmul
  change g (_ * _) = _
  rw [map_mul, hinv]

end PfaffianDescent
