import PfaffianDescent.CubicCanonicalPointFieldTraceCoefficient
import PfaffianDescent.CubicIntrinsicQuadraticTrace

/-! # Field-trace evaluation of actual canonical point classes

These formulas hold for every point Ext class. The coefficient is constructed
from the geometric trace; its nonvanishing is not assumed or asserted here.
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
/-- The actual closed-point pullback trace is the separable field trace in the
constructed residue coordinate, with its actual geometric coefficient. -/
theorem cubicCanonicalPointTrace_eq_fieldTrace_coordinate
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hDomain : IsDomain (CoordinateRing (equationIdeal p hp))]
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (i : Spec (.of L) ⟶ Proj (grading (equationIdeal p hp))) [hClosed : IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [hExtAmbient : HasExt.{u} (Proj PS).Modules]
    [hExt : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((Proj (grading (equationIdeal p hp))).presheaf.stalk (i default)))]
    (z : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit (Proj (grading (equationIdeal p hp))).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 1) 2) :
    cubicCanonicalPointTraceAddHom K p hp hp0 i z =
      Algebra.trace K L (cubicCanonicalPointResidueTraceCoefficient K p hp hp0 i hi *
        @cubicCanonicalPointExtTwoCoordinate K _ p hp hp0 hSmooth L _ i hClosed
          hExt hExtStalk z) := by
  letI : HasExt.{u} (hypersurface p hp).Modules := hExt
  have heval := @cubicCanonicalPointResidueTrace_evaluate_class K _ p hp hp0
    hDomain hSmooth L _ i hClosed hExtAmbient hExt hExtStalk z
  exact heval.symm.trans
    (cubicCanonicalPointResidueTrace_eq_fieldTrace K p hp hp0 i hi
      (@cubicCanonicalPointExtTwoCoordinate K _ p hp hp0 hSmooth L _ i hClosed
        hExt hExtStalk z))

set_option backward.isDefEq.respectTransparency false in
/-- The actual quadratic pairing of every point class has a field-trace
formula after actual coefficient multiplication. No supplied Koszul
representative or assumed trace-naturality equality is required. -/
theorem cubicCanonicalPoint_pairing_eq_fieldTrace_multiplied_coordinate
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hDomain : IsDomain (CoordinateRing (equationIdeal p hp))]
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (i : Spec (.of L) ⟶ Proj (grading (equationIdeal p hp))) [hClosed : IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [hExtAmbient : HasExt.{u} (Proj PS).Modules]
    [hExt : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((Proj (grading (equationIdeal p hp))).presheaf.stalk (i default)))]
    (z : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit (Proj (grading (equationIdeal p hp))).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 3) 2)
    (q : MvPolynomial.homogeneousSubmodule (Fin 4) K 2) :
    cubicIntrinsicNegativeThreeCohomologyTwoEquivDualQuadratic K p hp hp0
      ((Ext.mk₀ (C := (Proj (grading (equationIdeal p hp))).Modules)
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
          (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)).comp z (zero_add 2)) q =
      Algebra.trace K L (cubicCanonicalPointResidueTraceCoefficient K p hp hp0 i hi *
        @cubicCanonicalPointExtTwoCoordinate K _ p hp hp0 hSmooth L _ i hClosed
          hExt hExtStalk
          (z.comp (Ext.mk₀ (C := (Proj (grading (equationIdeal p hp))).Modules)
            (mulHomogeneous (grading (equationIdeal p hp))
              (cubicQuadraticRestriction K p hp q) 1)) (add_zero 2))) := by
  letI : HasExt.{u} (SheafOfModules.{u}
    (Proj (grading (equationIdeal p hp))).ringCatSheaf) := hExt
  let g := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
    (closedImmersionIdealTwistSequenceUnitTargetIso i).inv
  let phi := mulHomogeneous (grading (equationIdeal p hp))
    (cubicQuadraticRestriction K p hp q) 1
  have hpull := extPullback_postcomp.{u + 1, u, u}
    (C := (Proj (grading (equationIdeal p hp))).Modules) g z phi
  have hpair := cubicIntrinsicNegativeThree_pairing_eq_canonical_trace_multiplication
    K p hp hp0 ((Ext.mk₀ (C := (Proj (grading (equationIdeal p hp))).Modules) g).comp z
      (zero_add 2)) q
  exact hpair.trans
    ((congrArg (cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0) hpull).trans
      (cubicCanonicalPointTrace_eq_fieldTrace_coordinate K p hp hp0 i hi
        (z.comp (Ext.mk₀ (C := (Proj (grading (equationIdeal p hp))).Modules) phi)
          (add_zero 2))))

end PfaffianDescent.ProjectiveNegativeTwist
