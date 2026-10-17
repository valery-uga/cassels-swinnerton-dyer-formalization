import AllCharacteristics.RegularPairSquareZeroFiniteFlat
import AllCharacteristics.ResidueSpecialFiber
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! SOURCE ONLY / UNVERIFIED174. Canonical affine fiber reduction. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct nonZeroDivisors
universe u

/-- The actual coefficient reduction on an affine coordinate ring. -/
def affineTensorFiberReduction174
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] : A →ₐ[R] S ⊗[R] A :=
  Algebra.TensorProduct.includeRight

lemma affineTensorFiberReduction174_surjective
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A]
    (hRS : Function.Surjective (algebraMap R S)) :
    Function.Surjective (affineTensorFiberReduction174 (R := R) (S := S) (A := A)) :=
  Algebra.TensorProduct.includeRight_surjective A hRS

/-- The entire reduction kernel is derived, not assumed. -/
lemma affineTensorFiberReduction174_kernel
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A]
    (hRS : Function.Surjective (algebraMap R S)) :
    RingHom.ker (affineTensorFiberReduction174 (R := R) (S := S) (A := A)).toRingHom =
      (RingHom.ker (algebraMap R S)).map (algebraMap R A) := by
  let I := RingHom.ker (algebraMap R S)
  let eCoef : (R ⧸ I) ≃ₐ[R] S :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hRS
  let e : (A ⧸ I.map (algebraMap R A)) ≃+* S ⊗[R] A :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I).toRingEquiv.trans
      (Algebra.TensorProduct.congr eCoef (AlgEquiv.refl : A ≃ₐ[R] A)).toRingEquiv
  have he (a : A) : e (Ideal.Quotient.mk (I.map (algebraMap R A)) a) =
      affineTensorFiberReduction174 (R := R) (S := S) a := by
    dsimp only [e, RingEquiv.trans_apply]
    change (Algebra.TensorProduct.congr eCoef (AlgEquiv.refl : A ≃ₐ[R] A))
      ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I)
        (Ideal.Quotient.mk (I.map (algebraMap R A)) a)) =
      affineTensorFiberReduction174 (R := R) (S := S) a
    rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
    change eCoef (1 : R ⧸ I) ⊗ₜ[R] a = 1 ⊗ₜ[R] a
    rw [map_one]
  ext a
  change affineTensorFiberReduction174 (R := R) (S := S) a = 0 ↔
    a ∈ I.map (algebraMap R A)
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← he]
  exact e.map_eq_zero_iff

/-- This is the actual ambient fiber square, with both canonical projections. -/
lemma affineTensorFiberReduction174_isPullback
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (affineTensorFiberReduction174 (R := R) (S := S) (A := A)).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R S A).flip

end PfaffianDescent
