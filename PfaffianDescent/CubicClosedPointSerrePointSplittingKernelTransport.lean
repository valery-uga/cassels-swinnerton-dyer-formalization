import PfaffianDescent.CubicClosedPointSerrePointSplittingKernelTensor

noncomputable section
namespace PfaffianDescent
universe u

/-- Exact kernel transport for a commuting evaluation square with actual
isomorphisms on both targets; the source vector remains literally the same. -/
def pointSplittingKernelEquivOfSquare
    {E U V W Z : Type u} [Field E]
    [AddCommGroup U] [Module E U] [AddCommGroup V] [Module E V]
    [AddCommGroup W] [Module E W] [AddCommGroup Z] [Module E Z]
    (R : U →ₗ[E] V) (T : U →ₗ[E] W)
    (A : V ≃ₗ[E] Z) (B : W ≃ₗ[E] Z)
    (h : A.toLinearMap.comp R = B.toLinearMap.comp T) :
    LinearMap.ker R ≃ₗ[E] LinearMap.ker T := by
  apply LinearEquiv.ofEq
  ext x
  change R x = 0 ↔ T x = 0
  have hx : A (R x) = B (T x) := DFunLike.congr_fun h x
  constructor
  · intro hr
    apply B.injective
    rw [← hx, hr, A.map_zero, B.map_zero]
  · intro ht
    apply A.injective
    rw [hx, ht, B.map_zero, A.map_zero]

theorem pointSplittingKernelEquivOfSquare_coe
    {E U V W Z : Type u} [Field E]
    [AddCommGroup U] [Module E U] [AddCommGroup V] [Module E V]
    [AddCommGroup W] [Module E W] [AddCommGroup Z] [Module E Z]
    (R : U →ₗ[E] V) (T : U →ₗ[E] W)
    (A : V ≃ₗ[E] Z) (B : W ≃ₗ[E] Z)
    (h : A.toLinearMap.comp R = B.toLinearMap.comp T) (x : R.ker) :
    (pointSplittingKernelEquivOfSquare R T A B h x : U) = x := rfl

end PfaffianDescent
