import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Algebra.CharP.Algebra

/-! # Characteristic zero along flat maps

Faithful flatness makes the map on local rings injective.  This lets
characteristic-zero hypotheses pass from a domain base to every stalk of a
flat family, and then to the function field of an integral total space.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u

lemma injective_stalkMap_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (x : X) :
    Function.Injective (f.stalkMap x).hom := by
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact (show RingHom.FaithfullyFlat (f.stalkMap x).hom from this).injective

lemma charZero_stalk_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (x : X)
    [CharZero (Y.presheaf.stalk (f x))] : CharZero (X.presheaf.stalk x) := by
  constructor
  intro m n h
  apply Nat.cast_injective (R := Y.presheaf.stalk (f x))
  apply injective_stalkMap_of_flat f x
  simpa only [map_natCast] using h

lemma charZero_spec_stalk (R : Type u) [CommRing R] [IsDomain R] [CharZero R]
    (x : Spec (.of R)) : CharZero ((Spec (.of R)).presheaf.stalk x) := by
  have : x.asIdeal.IsPrime := x.isPrime
  let e := (Spec.stalkIso (.of R) x).commRingCatIsoToRingEquiv
  have hi : Function.Injective (algebraMap R (Localization.AtPrime x.asIdeal)) :=
    IsLocalization.injective (Localization.AtPrime x.asIdeal) x.asIdeal.primeCompl_le_nonZeroDivisors
  have : CharZero (Localization.AtPrime x.asIdeal) := (RingHom.charZero_iff hi).mp inferInstance
  constructor
  intro m n h
  apply Nat.cast_injective (R := Localization.AtPrime x.asIdeal)
  simpa only [map_natCast] using congrArg e h

lemma charZero_stalk_of_flat_over_domain
    (R : Type u) [CommRing R] [IsDomain R] [CharZero R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Flat f] (x : X) :
    CharZero (X.presheaf.stalk x) := by
  have := charZero_spec_stalk R (f x)
  exact charZero_stalk_of_flat f x

lemma charZero_functionField_of_flat_over_domain
    (R : Type u) [CommRing R] [IsDomain R] [CharZero R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Flat f] [IsIntegral X] :
    CharZero X.functionField := by
  let x := genericPoint X
  letI : CharZero (X.presheaf.stalk x) :=
    charZero_stalk_of_flat_over_domain R f x
  letI : IsFractionRing (X.presheaf.stalk x) X.functionField := inferInstance
  exact IsFractionRing.charZero_of_isFractionRing (X.presheaf.stalk x)

end AllCharacteristics
