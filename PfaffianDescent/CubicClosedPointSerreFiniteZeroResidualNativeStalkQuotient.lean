import PfaffianDescent.CubicClosedPointSerreZeroIdealStalk
import PfaffianDescent.VoisinHypersurfaceCokernel

/-! # Literal stalk rings of actual affine closed kernels -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_affineIdeal_germ_eq_stalkMap_kernel
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (z : Z) (hz : i z ∈ U.1) :
    (i.ker.ideal U).map (X.presheaf.germ U.1 (i z) hz).hom =
      RingHom.ker (i.stalkMap z).hom := by
  have h := cubicClosedPointSerreZeroIdealStalk_map_eq_ker i U (i z) hz
  rw [h]
  ext r
  change closedImmersionPushforwardStalkFromRingLinearMap i (i z) r = 0 ↔
    i.stalkMap z r = 0
  exact closedImmersionPushforwardStalkFromRingLinearMap_eq_zero_iff
    i i.isClosedEmbedding.isInducing z r

/-- The actual closed source stalk is the quotient by the actual germ-localized
kernel ideal; neither a stalk-ring identification nor a kernel certificate is supplied. -/
def cubicClosedPointSerreFiniteZeroResidual_affineIdeal_quotientStalkRingEquiv
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (z : Z) (hz : i z ∈ U.1) :
    (X.presheaf.stalk (i z) ⧸
      (i.ker.ideal U).map (X.presheaf.germ U.1 (i z) hz).hom) ≃+*
        Z.presheaf.stalk z :=
  (Ideal.quotEquivOfEq
    (cubicClosedPointSerreFiniteZeroResidual_affineIdeal_germ_eq_stalkMap_kernel i U z hz)).trans
      ((i.stalkMap z).hom.quotientKerEquivOfSurjective (i.stalkMap_surjective z))

@[simp]
theorem cubicClosedPointSerreFiniteZeroResidual_affineIdeal_quotientStalkRingEquiv_mk
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (z : Z) (hz : i z ∈ U.1) (r : X.presheaf.stalk (i z)) :
    cubicClosedPointSerreFiniteZeroResidual_affineIdeal_quotientStalkRingEquiv i U z hz
      (Ideal.Quotient.mk _ r) = i.stalkMap z r := by
  simp only [cubicClosedPointSerreFiniteZeroResidual_affineIdeal_quotientStalkRingEquiv,
    RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk _ r

end PfaffianDescent
