import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGoodOpen

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_goodOpen_pullback_finite
    {Z B E : Scheme.{u}} (f : Z ⟶ B) [IsProper f]
    (h : E ⟶ B) [IsOpenImmersion h]
    (hr : Set.range h ⊆ cubicClosedPointSerreFiniteZeroResidual_goodOpen f) :
    IsFinite (pullback.snd f h) := by
  let V := h.opensRange
  have hV : V ≤ cubicClosedPointSerreFiniteZeroResidual_goodOpen f := hr
  letI : LocallyQuasiFinite (f ∣_ V) := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
    ext x
    have hy : f ((f ⁻¹ᵁ V).ι x) ∈ cubicClosedPointSerreFiniteZeroResidual_goodOpen f := hV x.2
    have hx : f.QuasiFiniteAt ((f ⁻¹ᵁ V).ι x) := hy _ rfl
    rw [← Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion, ← morphismRestrict_ι,
      Scheme.Hom.quasiFiniteAt_comp_iff] at hx
    simpa using hx
  letI : LocallyQuasiFinite (pullback.snd f h) :=
    (MorphismProperty.arrow_mk_iso_iff @LocallyQuasiFinite (morphismRestrictOpensRange f h)).mp inferInstance
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end PfaffianDescent
