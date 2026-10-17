import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_fieldPoint_pullback_finite
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (ep : Spec (.of K) ⟶ Y) [Mono ep]
    (hf : (f ⁻¹' {ep (IsLocalRing.closedPoint K)}).Finite) :
    Finite ↥(pullback f ep) := by
  have hr : Set.range ep = {ep (IsLocalRing.closedPoint K)} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact Set.mem_singleton_iff.mpr (congrArg ep (Subsingleton.elim z (IsLocalRing.closedPoint K)))
    · intro hy
      exact ⟨IsLocalRing.closedPoint K, (Set.mem_singleton_iff.mp hy).symm⟩
  have h : (Set.range (pullback.fst f ep)).Finite := by
    rw [Scheme.Pullback.range_fst, hr]
    exact hf
  have hu : (Set.univ : Set ↥(pullback f ep)).Finite := by
    simpa using h.preimage (pullback.fst f ep).injective.injOn
  exact Set.finite_univ_iff.mp hu

end PfaffianDescent
