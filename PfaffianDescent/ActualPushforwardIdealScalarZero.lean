import PfaffianDescent.IdealSheafModule

/- SOURCE ONLY / UNVERIFIED. A scalar killed by the ACTUAL pushed-forward
unit map annihilates EVERY actual pushed-forward module section. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma actualPushforwardScalarZero
    {X Z : Scheme.{u}} (q : Z ⟶ X) (N : Z.Modules) (U : X.Opens)
    (a : Γ(X, U))
    (ha : (closedImmersionUnitToPushforwardUnit q).val.app (op U) a = 0)
    (y : ((Scheme.Modules.pushforward q).obj N).val.obj (op U)) :
    letI : Module Γ(X, U) (((Scheme.Modules.pushforward q).obj N).val.obj (op U)) :=
      (((Scheme.Modules.pushforward q).obj N).val.obj (op U)).isModule
    a • y = 0 := by
  letI : Module Γ(X, U) (((Scheme.Modules.pushforward q).obj N).val.obj (op U)) :=
    (((Scheme.Modules.pushforward q).obj N).val.obj (op U)).isModule
  letI : Module Γ(Z, q ⁻¹ᵁ U)
      (((Scheme.Modules.pushforward q).obj N).val.obj (op U)) :=
    (N.val.obj (op (q ⁻¹ᵁ U))).isModule
  have ha' : q.app U a = 0 := ha
  change (q.app U a) • y = 0
  rw [ha', zero_smul]

end PfaffianDescent
