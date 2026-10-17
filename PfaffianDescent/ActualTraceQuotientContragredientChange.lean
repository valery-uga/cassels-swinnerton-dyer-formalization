import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Basic

/- SOURCE ONLY / UNVERIFIED. Coordinate change transports BOTH the quotient
and evaluation map. Arbitrary residue scaling is NOT claimed to preserve a
fixed trace-zero functional. This is a method helper, not the cubic Phi provider. -/
noncomputable section
namespace PfaffianDescent
universe u v w

section
variable {K L : Type u} [Field K] [Field L] [Algebra K L]
    {E : Type v} [AddCommGroup E] [Module L E] [Module K E] [IsScalarTower K L E]
    {E' : Type v} [AddCommGroup E'] [Module L E'] [Module K E'] [IsScalarTower K L E']
    {V : Type w} [AddCommGroup V] [Module K V]

lemma actualTraceQuotient_change_composite
    (e : E ≃ₗ[L] E') (ell : E →ₗ[L] L) (phi : V →ₗ[K] E) :
    (((ell.comp e.symm.toLinearMap).restrictScalars K).comp
      ((e.toLinearMap.restrictScalars K).comp phi)) =
        (ell.restrictScalars K).comp phi := by
  ext v
  exact congrArg ell (e.symm_apply_apply (phi v))

lemma actualTraceQuotient_change_trace
    (e : E ≃ₗ[L] E') (ell : E →ₗ[L] L) (phi : V →ₗ[K] E) :
    (Algebra.trace K L).comp (((ell.comp e.symm.toLinearMap).restrictScalars K).comp
      ((e.toLinearMap.restrictScalars K).comp phi)) =
        (Algebra.trace K L).comp ((ell.restrictScalars K).comp phi) := by
  rw [actualTraceQuotient_change_composite]

lemma actualTraceQuotient_change_kernel
    (e : E ≃ₗ[L] E') (ell : E →ₗ[L] L) (phi : V →ₗ[K] E) :
    LinearMap.ker (((ell.comp e.symm.toLinearMap).restrictScalars K).comp
      ((e.toLinearMap.restrictScalars K).comp phi)) =
        LinearMap.ker ((ell.restrictScalars K).comp phi) := by
  rw [actualTraceQuotient_change_composite]

end
end PfaffianDescent
