import PfaffianDescent.PointCartierNativeStalkSmoothPointBoundary
import PfaffianDescent.CubicRationalPointAmbientAugmentationInjective
import PfaffianDescent.VoisinCubicSurfaceVanishing

/-! SOURCE ONLY221. The rationality hypothesis is explicit and essential.
A rational smooth supported class is detected by actual second-Cartier and
ambient augmentation maps. No arbitrary finite-point unit injectivity. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- Original smooth cubic and actual rational-point geometry construct both
nonvanishing upgrades. The supplied nonzero class is the supported Ext class,
never its unit restriction, second boundary, or trace. -/
theorem smoothCubic_rationalSupportedPoint_unitPrecomp_ne_zero221
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (i : Spec (.of K) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = 𝟙 (Spec (.of K)))
    [hExtAmbient : HasExt.{u} (Proj PS).Modules]
    [hExtSurface : HasExt.{u} (hypersurface p hp).Modules]
    [HasExt.{u + 1} (ModuleCat.{u} ((Proj PS).presheaf.stalk
      (hypersurfaceAmbientPoint p hp (i default))))]
    [HasExt.{u + 1} (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (i default)))]
    (z : Ext.{u} (C := (hypersurface p hp).Modules)
      (closedImmersionIdealTwistSequence i
        (show (hypersurface p hp).Modules from
          SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 1) 2) (hz : z ≠ 0) :
    (Ext.mk₀.{u} (C := (hypersurface p hp).Modules)
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
        (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)).comp z (zero_add 2) ≠ 0 := by
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) :=
    smoothCubic_coordinateRing_isDomain K p hp hp0
  have hBoundary := pointCartierNativeStalkSmoothPoint_boundary_ne_zero K p hp hp0 i z hz
  have hInjection := cubicRationalPointAmbientAugmentation_precomp_injective K p hp i hi
  let F := Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)
  letI : PreservesFiniteLimits F := by
    change PreservesFiniteLimits (SheafOfModules.pushforward _)
    exact SheafOfModules.pushforward_preservesFiniteLimits _
  letI : F.Additive := Functor.additive_of_preserves_binary_products F
  exact pointGlobalTraceCartier_unit_precomp_ne_zero.{u + 1, u, u, u + 1, u, u}
    (C := (hypersurface p hp).Modules) (D := (Proj PS).Modules) F
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
      (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (hypersurfaceToAmbient p hp))
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (hypersurfaceToAmbient p hp) ≫
      F.map (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
        (closedImmersionIdealTwistSequenceUnitTargetIso i).inv))
    rfl z (hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 1).extClass
    hInjection hBoundary

end PfaffianDescent.ProjectiveNegativeTwist
