import Mathlib.RingTheory.Smooth.Kaehler
import Mathlib.RingTheory.Etale.Field

/- SOURCE ONLY / UNVERIFIED. The actual conormal-to-Kaehler-fiber map is
bijective at a separable residue field. Both directions are derived, not
assumed. No smoothness or coordinate/frame certificate is required here. -/
noncomputable section
namespace PfaffianDescent
open TensorProduct KaehlerDifferential
open scoped TensorProduct
universe u
variable {k R L : Type u} [Field k] [CommRing R] [Field L]
  [Algebra k R] [Algebra k L] [Algebra.IsSeparable k L]

/-- At a separable residue field, the actual residue conormal is the
actual fiber of the Kaehler module of the fixed ambient affine ring. -/
theorem separableResidue_kerCotangentToTensor_bijective
    (rho : R →ₐ[k] L) (hrho : Function.Surjective rho) :
    letI : Algebra R L := rho.toRingHom.toAlgebra
    letI : IsScalarTower k R L := IsScalarTower.of_algebraMap_eq
      (fun c => (rho.commutes c).symm)
    Function.Bijective (KaehlerDifferential.kerCotangentToTensor k R L) := by
  letI : Algebra R L := rho.toRingHom.toAlgebra
  letI : IsScalarTower k R L := IsScalarTower.of_algebraMap_eq
    (fun c => (rho.commutes c).symm)
  letI : Algebra.FormallyEtale k L := Algebra.FormallyEtale.of_isSeparable k L
  let f : R →ₐ[k] L := IsScalarTower.toAlgHom k R L
  have hf : Function.Surjective (algebraMap R L) := hrho
  have hfsquare : Function.Surjective f.kerSquareLift := by
    intro c
    obtain ⟨r, hr⟩ := hrho c
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    exact hr
  have hnil : IsNilpotent (RingHom.ker f.kerSquareLift.toRingHom) := by
    refine ⟨2, ?_⟩
    rw [AlgHom.ker_kerSquareLift]
    exact Ideal.cotangentIdeal_square _
  let s := Algebra.FormallySmooth.liftOfSurjective
    (AlgHom.id k L) f.kerSquareLift hfsquare hnil
  have hs : f.kerSquareLift.comp s = AlgHom.id k L :=
    Algebra.FormallySmooth.comp_liftOfSurjective
      (AlgHom.id k L) f.kerSquareLift hfsquare hnil
  let retraction :=
    (retractionKerCotangentToTensorEquivSection
      (R := k) (P := R) (S := L) hf).symm ⟨s, hs⟩
  constructor
  · intro x y hxy
    have hx : retraction.val (kerCotangentToTensor k R L x) = x :=
      LinearMap.congr_fun retraction.property x
    have hy : retraction.val (kerCotangentToTensor k R L y) = y :=
      LinearMap.congr_fun retraction.property y
    exact hx.symm.trans ((congrArg retraction.val hxy).trans hy)
  · intro y
    have hy : y ∈ LinearMap.range (kerCotangentToTensor k R L) := by
      rw [KaehlerDifferential.range_kerCotangentToTensor k R L hf]
      change KaehlerDifferential.mapBaseChange k R L y = 0
      exact Subsingleton.elim _ _
    exact hy

/-- The actual equivalence has the canonical conormal-to-Kaehler map as
its forward map; it is not an arbitrary existential coordinate choice. -/
def separableResidue_cotangentKaehlerFiberEquiv
    (rho : R →ₐ[k] L) (hrho : Function.Surjective rho) :
    letI : Algebra R L := rho.toRingHom.toAlgebra
    letI : IsScalarTower k R L := IsScalarTower.of_algebraMap_eq
      (fun c => (rho.commutes c).symm)
    (RingHom.ker rho.toRingHom).Cotangent ≃ₗ[R]
      L ⊗[R] KaehlerDifferential k R := by
  letI : Algebra R L := rho.toRingHom.toAlgebra
  letI : IsScalarTower k R L := IsScalarTower.of_algebraMap_eq
    (fun c => (rho.commutes c).symm)
  exact LinearEquiv.ofBijective (KaehlerDifferential.kerCotangentToTensor k R L)
    (separableResidue_kerCotangentToTensor_bijective rho hrho)

end PfaffianDescent
