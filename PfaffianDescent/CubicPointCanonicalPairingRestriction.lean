import PfaffianDescent.CubicPointQuadraticRestriction
import PfaffianDescent.CubicPointCompatibleNegativeThreeResidueEquiv

/-! # Actual point pairing and actual quadratic restriction

Both point coordinates are internally constructed additive equivalences.
The coefficient is the constructed canonical trace coefficient, whose
nonvanishing remains a separate global geometric question.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
/-- The actual canonical point pairing is field trace of the actual Ext
coordinate times the actual restricted quadratic section. No trace identity,
restriction square, coordinate compatibility, or nonzero coefficient is input. -/
theorem cubicPointCanonical_pairing_eq_fieldTrace_actual_restriction
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hDomain : IsDomain (CoordinateRing (equationIdeal p hp))]
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (i : Spec (.of L) ⟶ Proj (grading (equationIdeal p hp))) [hClosed : IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [hExtAmbient : HasExt.{u} (Proj PS).Modules]
    [hExt : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    [hExtStalk : HasExt.{u + 1}
      (ModuleCat ((Proj (grading (equationIdeal p hp))).presheaf.stalk (i default)))]
    (z : Ext.{u} (C := (Proj (grading (equationIdeal p hp))).Modules)
      (closedImmersionIdealTwistSequence i
        (SheafOfModules.unit (Proj (grading (equationIdeal p hp))).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 3) 2)
    (q : MvPolynomial.homogeneousSubmodule (Fin 4) K 2) :
    cubicIntrinsicNegativeThreeCohomologyTwoEquivDualQuadratic K p hp hp0
      ((Ext.mk₀.{u} (C := (Proj (grading (equationIdeal p hp))).Modules)
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
          (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)).comp z (zero_add 2)) q =
    Algebra.trace K L (cubicCanonicalPointResidueTraceCoefficient K p hp hp0 i hi *
      (@cubicPointCompatibleNegativeThreeResidueEquiv K _ p hp hp0 hSmooth L _ i
        hClosed hExt hExtStalk z) *
      (@cubicPointQuadraticRestrictionPointFiberAddEquiv K _ p hp hp0 hSmooth L _ i
        hClosed hExt hExtStalk
        (cubicPointQuadraticRestrictionActualSection K p hp i
          (positiveGlobalSectionOfHomogeneous (grading (equationIdeal p hp)) 2
            (cubicQuadraticRestriction K p hp q))))) := by
  have h := @cubicPointCompatible_pairing_eq_fieldTrace
    K _ p hp hp0 hDomain hSmooth L _ _ _ _ i hClosed hi hExtAmbient hExt hExtStalk z q
  rw [@cubicPointQuadraticRestrictionScalar_eq_actual_restriction K _ p hp hp0
    hSmooth L _ i hClosed hExt hExtStalk q] at h
  exact h

end PfaffianDescent.ProjectiveNegativeTwist
