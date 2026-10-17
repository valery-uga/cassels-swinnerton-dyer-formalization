import PfaffianDescent.RegularDescentFromGenericFibre
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Regularity in a base-ideal quotient from an actual pushout fibre

The quotient of an algebra by the extension of a coefficient ideal is the
tensor product with the coefficient quotient. An actual ring pushout thus
identifies that quotient with the changed algebra and transfers regularity
of the changed equation to the precise quotient used by the flatness test.
-/

namespace PfaffianDescent

open CategoryTheory

universe u

/-- A regular element on an actual base-ideal pushout fibre gives a
regular element in the quotient by the extended base ideal. -/
theorem isRegular_baseIdealQuotient_of_pushout
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] (I : Ideal R)
    (h : A →+* B) (k : (R ⧸ I) →+* B)
    (H : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R (R ⧸ I)))
      (CommRingCat.ofHom h) (CommRingCat.ofHom k))
    (x : A) (hx : IsRegular (h x)) :
    IsRegular (Ideal.Quotient.mk (I.map (algebraMap R A)) x) := by
  let e := ((CommRingCat.isPushout_tensorProduct R (R ⧸ I) A).flip.isoIsPushout
    _ _ H).commRingCatIsoToRingEquiv
  let q := (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I).toRingEquiv
  have he : e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom = h := by
    apply RingHom.ext
    intro a
    exact congrArg (fun m : CommRingCat.of A ⟶ CommRingCat.of B => m a)
      ((CommRingCat.isPushout_tensorProduct R (R ⧸ I) A).flip.inl_isoIsPushout_hom
        _ _ H)
  have hxq : IsRegular (e (q (Ideal.Quotient.mk (I.map (algebraMap R A)) x))) := by
    change IsRegular (e (1 ⊗ₜ[R] x))
    change IsRegular ((e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) x)
    rw [he]
    exact hx
  exact isRegular_of_injective_ringHom q.toRingHom q.injective _
    (isRegular_of_injective_ringHom e.toRingHom e.injective _ hxq)

end PfaffianDescent
