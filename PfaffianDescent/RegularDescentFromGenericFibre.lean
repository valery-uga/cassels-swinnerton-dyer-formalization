import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Descending regularity from a generic base change

A flat algebra over a base ring embeds into its tensor product with a
faithful coefficient extension. A regular element after that extension
is therefore regular before extension. The intended application is the
generic field of a domain-valued Voisin parameter chart.
-/

namespace PfaffianDescent

open TensorProduct
open CategoryTheory
open scoped nonZeroDivisors

universe u v w

theorem isRegular_of_injective_ringHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) (x : A)
    (hx : IsRegular (f x)) : IsRegular x := by
  apply isRegular_iff_mem_nonZeroDivisors.mpr
  exact mem_nonZeroDivisors_of_injective hf
    (isRegular_iff_mem_nonZeroDivisors.mp hx)

theorem isRegular_of_isRegular_tensor_of_flat
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [FaithfulSMul R S]
    [Module.Flat R A] (x : A)
    (hx : IsRegular (1 ⊗ₜ[R] x : S ⊗[R] A)) : IsRegular x := by
  let f : A →+* S ⊗[R] A := Algebra.TensorProduct.includeRight.toRingHom
  have hf : Function.Injective f :=
    Algebra.TensorProduct.includeRight_injective
      (FaithfulSMul.algebraMap_injective R S)
  apply isRegular_of_injective_ringHom f hf x
  change IsRegular (1 ⊗ₜ[R] x : S ⊗[R] A)
  exact hx

/-- A regular element on the generic fraction-field fibre of a flat
algebra over a domain is regular on the total algebra. -/
theorem isRegular_of_isRegular_fractionField_of_flat
    {R : Type u} {F : Type v} {A : Type w}
    [CommRing R] [IsDomain R] [Field F] [CommRing A]
    [Algebra R F] [IsFractionRing R F] [Algebra R A]
    [Module.Flat R A] (x : A)
    (hx : IsRegular (1 ⊗ₜ[R] x : F ⊗[R] A)) : IsRegular x :=
  isRegular_of_isRegular_tensor_of_flat x hx

/-- In a pushout along a faithful coefficient extension, the map from a
flat source algebra to the changed algebra is injective. -/
theorem injective_of_flat_pushout
    {R S A B : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Module.Flat R A]
    (h : A →+* B) (k : S →+* B)
    (H : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom h) (CommRingCat.ofHom k))
    (hf : Function.Injective (algebraMap R S)) : Function.Injective h := by
  let e := ((CommRingCat.isPushout_tensorProduct R S A).flip.isoIsPushout _ _ H).commRingCatIsoToRingEquiv
  have he : e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom = h := by
    apply RingHom.ext
    intro x
    exact congrArg (fun m : CommRingCat.of A ⟶ CommRingCat.of B => m x)
      ((CommRingCat.isPushout_tensorProduct R S A).flip.inl_isoIsPushout_hom _ _ H)
  rw [← he]
  exact e.injective.comp
    (Algebra.TensorProduct.includeRight_injective hf)

/-- Regularity descends along a flat pushout with injective coefficient map. -/
theorem isRegular_of_isRegular_flat_pushout
    {R S A B : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Module.Flat R A]
    (h : A →+* B) (k : S →+* B)
    (H : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom h) (CommRingCat.ofHom k))
    (hf : Function.Injective (algebraMap R S))
    (x : A) (hx : IsRegular (h x)) : IsRegular x :=
  isRegular_of_injective_ringHom h
    (injective_of_flat_pushout h k H hf) x hx

end PfaffianDescent
