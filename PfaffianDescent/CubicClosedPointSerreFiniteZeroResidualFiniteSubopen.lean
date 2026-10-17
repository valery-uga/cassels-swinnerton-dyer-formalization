import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGoodOpen

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_finite_subopen
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (U : Y.Opens)
    (hU : U ≤ cubicClosedPointSerreFiniteZeroResidual_goodOpen f) : IsFinite (f ∣_ U) := by
  suffices LocallyQuasiFinite (f ∣_ U) from .of_isProper_of_locallyQuasiFinite _
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  ext x
  have h : f.QuasiFiniteAt ((f ⁻¹ᵁ U).ι x) := (hU x.2) _ rfl
  rw [← Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion, ← morphismRestrict_ι,
    Scheme.Hom.quasiFiniteAt_comp_iff] at h
  simpa using h

end PfaffianDescent
