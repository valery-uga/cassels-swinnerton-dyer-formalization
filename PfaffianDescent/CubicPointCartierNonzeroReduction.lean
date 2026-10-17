import PfaffianDescent.PointGlobalTraceCartierNonzeroReduction
import PfaffianDescent.CubicCanonicalPointTraceAddHom
import PfaffianDescent.ClosedImmersionPushforwardExact

/-! # A native Cartier criterion for nonvanishing of the actual cubic point trace

The criterion uses the actual surface-to-ambient pushforward, actual point
restriction and actual cubic Cartier extension. Ambient augmentation
injectivity and nonvanishing of that boundary remain explicit inputs here.
No comparison between the Cech trace and a new trace is required.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
/-- The original intrinsic trace is nonzero whenever the actual ambient
augmentation detects the nonzero actual Cartier boundary. -/
theorem cubicPointCartier_trace_ne_zero_of_ambient_boundary
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hDomain : IsDomain (CoordinateRing (equationIdeal p hp))]
    {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ Proj (grading (equationIdeal p hp))) [IsClosedImmersion i]
    [hExtAmbient : HasExt.{u} (Proj PS).Modules]
    [hExtSurface : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    (z : Ext.{u} (C := (Proj (grading (equationIdeal p hp))).Modules)
      (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit (Proj (grading (equationIdeal p hp))).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 1) 2)
    (hinj : Function.Injective
      ((Ext.mk₀.{u} (C := (Proj PS).Modules)
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
          (hypersurfaceToAmbient p hp) ≫
          (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).map
            (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
              (closedImmersionIdealTwistSequenceUnitTargetIso i).inv))).precomp
        (sheafOfModules PS 4) (zero_add 3)))
    (hboundary :
      letI : HasExt.{u} (hypersurface p hp).Modules := hExtSurface
      letI : HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf) := hExtAmbient
      (z.mapExactFunctor
      (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp))).comp
      (hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 1).extClass rfl ≠ 0) :
    cubicCanonicalPointTraceAddHom K p hp hp0 i z ≠ 0 := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf) := hExtAmbient
  letI : HasExt.{u} (SheafOfModules.{u}
    (Proj (grading (equationIdeal p hp))).ringCatSheaf) := hExtSurface
  letI : HasExt.{u} (hypersurface p hp).Modules := hExtSurface
  let F := Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)
  letI : PreservesFiniteLimits F := by
    change PreservesFiniteLimits (SheafOfModules.pushforward _)
    exact SheafOfModules.pushforward_preservesFiniteLimits _
  have hunit := pointGlobalTraceCartier_unit_precomp_ne_zero.{u + 1, u, u, u + 1, u, u}
    (C := (Proj (grading (equationIdeal p hp))).Modules) (D := (Proj PS).Modules) F
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
      (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (hypersurfaceToAmbient p hp))
    _ rfl z (hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 1).extClass
    hinj hboundary
  intro htrace
  apply hunit
  apply (cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0).injective
  exact htrace.trans (map_zero
    (cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0)).symm

end PfaffianDescent.ProjectiveNegativeTwist
