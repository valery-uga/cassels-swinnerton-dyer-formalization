import PfaffianDescent.ActualPointTwistUntwistRatio
import PfaffianDescent.ActualFieldGammaSectionLinearEquiv

/- SOURCE ONLY / UNVERIFIED. Unit-ratio scalar acts on EVERY actual Gamma
fiber section. No desired fiber-map comparison hypothesis is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

theorem actualPointTwistUntwist_ratio_gamma_scalar
    {L : Type u} [Field L] (M T : (Spec (.of L)).Modules)
    (e0 e1 : T ≅ SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (w : (moduleSpecΓFunctor (R := .of L)).obj M) :
    (moduleSpecΓFunctor (R := .of L)).map
      ((actualPointTwistUntwistIso M T e0).inv ≫
        (actualPointTwistUntwistIso M T e1).hom) w =
      actualPointTwistTrivializationScalar e0 e1 • w := by
  let E := actualFieldGammaSectionLinearEquiv M
  obtain ⟨s, rfl⟩ := E.surjective w
  have h := congrArg E (actualPointTwistUntwist_ratio_section_scalar M T e0 e1 s)
  simpa only [E, actualFieldGammaSectionLinearEquiv_comp, LinearEquiv.map_smul, Functor.map_comp, ConcreteCategory.comp_apply] using h

end PfaffianDescent
