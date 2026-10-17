import PfaffianDescent.PrincipalPresentationKaehlerKernel
import PfaffianDescent.TensorSingletonSpanRange

/- SOURCE ONLY / UNVERIFIED. Tensoring the actual principal conormal
presentation preserves its actual relation, without a flatness hypothesis. -/
noncomputable section
namespace PfaffianDescent
open TensorProduct KaehlerDifferential
open scoped TensorProduct
universe u v w z
variable {k : Type u} {R : Type v} {A : Type w} {L : Type z} [CommRing k] [CommRing R] [CommRing A] [CommRing L]
  [Algebra k R] [Algebra k A] [Algebra R A] [IsScalarTower k R A]
  [Algebra A L]

def principalPresentationKaehlerFiberQuotientEquiv
    (h : Function.Surjective (algebraMap R A)) (F : R)
    (hker : RingHom.ker (algebraMap R A) = Ideal.span ({F} : Set R)) :
    L ⊗[A] Ω[A⁄k] ≃ₗ[L]
      (L ⊗[A] (A ⊗[R] Ω[R⁄k])) ⧸
        Submodule.span L ({(1 : L) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] D k R F)} :
          Set (L ⊗[A] (A ⊗[R] Ω[R⁄k]))) :=
  (AlgebraTensorModule.congr (LinearEquiv.refl L L)
    (principalPresentationKaehlerQuotientEquiv (k := k) h F hker).symm) ≪≫ₗ
  (AlgebraTensorModule.tensorQuotientEquiv L A L
    (Submodule.span A ({(1 : A) ⊗ₜ[R] D k R F} : Set (A ⊗[R] Ω[R⁄k])))) ≪≫ₗ
  (Submodule.quotEquivOfEq _ _
    (tensorSingletonSpanRange (L := L) ((1 : A) ⊗ₜ[R] D k R F)))

end PfaffianDescent
