import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free

/-! # A three-coordinate frame for the actual rank-six evaluation kernel -/
noncomputable section
namespace PfaffianDescent
universe u v w
open Module
variable {F : Type u} [Field F]
variable {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {W : Type w} [AddCommGroup W] [Module F W]

/-- The nine-section space and actual evaluation rank six give kernel rank three. -/
theorem serreIncidenceEvaluationKernel_finrank (ev : V →ₗ[F] W)
    (hV : finrank F V = 9) (hev : finrank F (LinearMap.range ev) = 6) :
    finrank F (LinearMap.ker ev) = 3 := by
  have h := ev.finrank_range_add_finrank_ker
  rw [hV, hev] at h
  omega

/-- This frame consists of actual kernel members, rather than independent
sections assumed to vanish at the marked points. -/
def serreIncidenceEvaluationKernelFrame (ev : V →ₗ[F] W)
    (hV : finrank F V = 9) (hev : finrank F (LinearMap.range ev) = 6) :
    Basis (Fin 3) F (LinearMap.ker ev) :=
  Module.finBasisOfFinrankEq F (LinearMap.ker ev)
    (serreIncidenceEvaluationKernel_finrank ev hV hev)

/-- Every actual section vanishing under evaluation has unique three scalar
coordinates in the kernel frame, including the canonical Serre section. -/
def serreIncidenceEvaluationKernelCoordinates (ev : V →ₗ[F] W)
    (hV : finrank F V = 9) (hev : finrank F (LinearMap.range ev) = 6) :
    LinearMap.ker ev ≃ₗ[F] (Fin 3 → F) :=
  (serreIncidenceEvaluationKernelFrame ev hV hev).equivFun

theorem serreIncidenceEvaluationKernelCoordinates_ne_zero (ev : V →ₗ[F] W)
    (hV : finrank F V = 9) (hev : finrank F (LinearMap.range ev) = 6)
    (s : LinearMap.ker ev) (hs : s ≠ 0) :
    serreIncidenceEvaluationKernelCoordinates ev hV hev s ≠ 0 := by
  intro hz
  apply hs
  apply (serreIncidenceEvaluationKernelCoordinates ev hV hev).injective
  simpa only [map_zero] using hz

end PfaffianDescent
