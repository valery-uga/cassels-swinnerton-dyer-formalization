import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOpenStalkFlat

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u

theorem cubicClosedPointSerreFiniteZeroResidual_restrict_stalk_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (x : (f ⁻¹ᵁ V : Scheme.{u}))
    (hx : (f.stalkMap x.1).hom.Flat) : ((f ∣_ V).stalkMap x).hom.Flat := by
  exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff (morphismRestrictStalkMap f V x)).mpr hx

end PfaffianDescent
