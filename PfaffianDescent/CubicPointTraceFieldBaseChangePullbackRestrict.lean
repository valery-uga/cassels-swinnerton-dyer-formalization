import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Restrict

/-! # Actual pullback restricted to an inverse-image open -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Restricting actual pullback to an inverse-image open is pulling back the
actual restriction to the original open. -/
def cubicPointTraceFieldBaseChangePullbackRestrictNatIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι) ≪≫
    Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f ≪≫
    Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm ≪≫
    (Scheme.Modules.pullbackComp (f ∣_ U) U.ι).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
      (Scheme.Modules.pullback (f ∣_ U))

/-- An actual morphism invertible on an open remains invertible after
pullback and restriction to the inverse-image open. -/
theorem cubicPointTraceFieldBaseChangePullbackRestrict_map_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    {M N : Y.Modules} (φ : M ⟶ N)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ)] :
    IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map
      ((Scheme.Modules.pullback f).map φ)) := by
  exact (NatIso.isIso_map_iff (cubicPointTraceFieldBaseChangePullbackRestrictNatIso f U) φ).mpr
    (inferInstanceAs (IsIso ((Scheme.Modules.pullback (f ∣_ U)).map
      ((Scheme.Modules.restrictFunctor U.ι).map φ))))

end PfaffianDescent
