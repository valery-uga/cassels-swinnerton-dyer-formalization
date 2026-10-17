import PfaffianDescent.ActualClosedPointConormalNativeTensorFiber
import PfaffianDescent.SurjectiveResidueTensorConormal

/-! SAME quotient-ring-linear native conormal and its actual affine sheaf.
SOURCE ONLY / UNVERIFIED; no adjunction, RR or Hodge conclusion. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u

/-- Native tensor/Ideal.Cotangent comparison is linear for the CANONICAL
quotient action. Both module actions exist before this equivalence. -/
def quotientTensorNativeConormalLinearEquiv
    {A : Type u} [CommRing A] (I : Ideal A) :
    ((A ⧸ I) ⊗[A] I) ≃ₗ[A ⧸ I] I.Cotangent := by
  let e := TensorProduct.quotTensorEquivQuotSMul I I
  refine { toAddEquiv := e.toAddEquiv, map_smul' := ?_ }
  intro b t
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  change e ((algebraMap A (A ⧸ I) a) • t) =
    (algebraMap A (A ⧸ I) a) • e t
  simpa only [algebraMap_smul] using e.map_smul a t

/-- The forward map keeps the literal native class of the same x. -/
theorem quotientTensorNativeConormalLinearEquiv_one_tmul
    {A : Type u} [CommRing A] (I : Ideal A) (x : I) :
    quotientTensorNativeConormalLinearEquiv I ((1 : A ⧸ I) ⊗ₜ[A] x) =
      I.toCotangent x := by
  exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul I x

/-- The genuine conormal sheaf of the quotient immersion is tilde of
its SAME native I/I² over the SAME quotient ring. No sheaf Iso is an input. -/
def affineQuotientNativeConormalTildeIso
    {A : Type u} [CommRing A] (I : Ideal A) :
    actualClosedImmersionConormalModule
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≅
    (tilde.functor (CommRingCat.of (A ⧸ I))).obj
      (ModuleCat.of (A ⧸ I) I.Cotangent) := by
  let rho := Ideal.Quotient.mk I
  let j := Spec.map (CommRingCat.ofHom rho)
  let P := Scheme.Modules.pullback j
  let eI := affineQuotientIdealTildeClosedImmersionModuleIso I
  let eT := affineIdealTildePullbackIso rho I
  let eC := quotientTensorNativeConormalLinearEquiv I
  exact P.mapIso eI.symm ≪≫ eT ≪≫
    (tilde.functor (CommRingCat.of (A ⧸ I))).mapIso eC.toModuleIso

end PfaffianDescent
