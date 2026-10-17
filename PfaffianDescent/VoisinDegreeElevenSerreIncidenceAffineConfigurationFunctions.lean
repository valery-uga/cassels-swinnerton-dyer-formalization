import PfaffianDescent.SchemeAffineFunctions

/-! # Actual affine configuration sections under the literal canonical Spec chart -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceAffineConfiguration_isoSpec_inv_appTop
    (B : Scheme.{u}) [IsAffine B] :
    B.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(B, ⊤)).inv := by
  have hh : B.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(B, ⊤)).hom :=
    Scheme.toSpecΓ_appTop B
  have hc := congrArg Scheme.Hom.appTop B.isoSpec.inv_hom_id
  simp only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, hh] at hc
  rw [← cancel_epi (Scheme.ΓSpecIso Γ(B, ⊤)).hom]
  exact hc.trans (Scheme.ΓSpecIso Γ(B, ⊤)).hom_inv_id.symm

end PfaffianDescent
