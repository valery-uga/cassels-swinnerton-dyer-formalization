import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPrincipalLocalization
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u

theorem cubicClosedPointSerreFiniteZeroResidual_basicParameter_sections_principal
    {R : Type u} [CommRing R] [IsPrincipalIdealRing R] (t : R) :
    IsPrincipalIdealRing Γ(Spec (.of (Localization.Away t)), ⊤) := by
  letI : IsPrincipalIdealRing (Localization.Away t) :=
    cubicClosedPointSerreFiniteZeroResidual_principalIdealRing_localization (Submonoid.powers t)
  let e := (Scheme.ΓSpecIso (.of (Localization.Away t))).commRingCatIsoToRingEquiv
  exact IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective

theorem cubicClosedPointSerreFiniteZeroResidual_basicParameter_sections_domain
    {R : Type u} [CommRing R] [IsDomain R] (t : R) (ht : t ≠ 0) :
    IsDomain Γ(Spec (.of (Localization.Away t)), ⊤) := by
  letI : IsDomain (Localization.Away t) := Localization.Away.isDomain ht
  let e := (Scheme.ΓSpecIso (.of (Localization.Away t))).commRingCatIsoToRingEquiv
  exact e.toMulEquiv.isDomain

end PfaffianDescent
