import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualLocalFlatSurface
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeStalkQuotient

/-! # Flatness transferred to the literal closed source stalk -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u v
set_option backward.isDefEq.respectTransparency false

/-- A flat quotient algebra gives flatness of the literal surjective ring map
with that kernel; the quotient-ring equivalence is constructed here. -/
theorem cubicClosedPointSerreFiniteZeroResidual_flat_comp_of_flat_quotient
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (q : A →+* B) (hq : Function.Surjective q)
    (I : Ideal A) (hI : RingHom.ker q = I)
    (hflat : ((Ideal.Quotient.mk I).comp f).Flat) : (q.comp f).Flat := by
  let e : (A ⧸ I) ≃+* B :=
    (Ideal.quotEquivOfEq hI.symm).trans (q.quotientKerEquivOfSurjective hq)
  have he : e.toRingHom.comp (Ideal.Quotient.mk I) = q := by
    ext a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hq a
  rw [← he, RingHom.comp_assoc]
  exact hflat.comp (RingHom.Flat.of_bijective e.bijective)

/-- Flatness of the actual closed stalk follows from flatness of the actual
ambient quotient by germ-localized ideal sections. -/
theorem cubicClosedPointSerreFiniteZeroResidual_closed_stalk_flat_of_affine_quotient
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (z : Z) (hz : i z ∈ U.1)
    {R : Type v} [CommRing R] (f : R →+* X.presheaf.stalk (i z))
    (hflat : ((Ideal.Quotient.mk
      ((i.ker.ideal U).map (X.presheaf.germ U.1 (i z) hz).hom)).comp f).Flat) :
    ((i.stalkMap z).hom.comp f).Flat := by
  exact cubicClosedPointSerreFiniteZeroResidual_flat_comp_of_flat_quotient
    f (i.stalkMap z).hom (i.stalkMap_surjective z) _
    (cubicClosedPointSerreFiniteZeroResidual_affineIdeal_germ_eq_stalkMap_kernel
      i U z hz).symm hflat

end PfaffianDescent
