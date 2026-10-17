import PfaffianDescent.CubicDiagonalCoefficientGeometry223
import PfaffianDescent.SchemeIsoPointExtTransport223
import PfaffianDescent.SmoothRationalSupportedPointUnitNonzero221

/-! Literal coefficient-cubic support and negative twist feed the existing
actual rational-point criterion. The generic input is a supported class,
not its unit image or a boundary/injectivity certificate. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 250000 in
/-- A nonzero actual diagonal point class is detected by its actual unit
image. All coefficient support, twist and rationality maps are derived. The
original factory below derives the nonzero class internally from222. -/
theorem cubicDiagonalClass_unitPrecomp_ne_zero223
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    let YL := schemeBaseChangeToField (L := L) (hypersurface p hp) (hypersurfaceToBase p hp)
    let pL := p.map (algebraMap K L)
    let hpL := hp.map (algebraMap K L)
    let iDiag := cubicPointTraceFieldBaseChangeRationalPoint K L (hypersurfaceToBase p hp) i hi
    let iCoeff := cubicDiagonalCoefficientPoint223 K L p hp i hi
    ∀ (hExtYL : HasExt.{u} YL.Modules)
      (hExtCoeff : HasExt.{u} (hypersurface pL hpL).Modules)
      (hExtAmbient : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) L)).Modules)
      (hExtLocalAmbient : HasExt.{u + 1} (ModuleCat.{u}
        ((Proj (MvPolynomial.homogeneousSubmodule (Fin 4) L)).presheaf.stalk
          (hypersurfaceAmbientPoint pL hpL (iCoeff default)))))
      (hExtLocalCoeff : HasExt.{u + 1} (ModuleCat.{u}
        ((hypersurface pL hpL).presheaf.stalk (iCoeff default)))),
    letI := hExtYL
    letI := hExtCoeff
    letI := hExtAmbient
    letI := hExtLocalAmbient
    letI := hExtLocalCoeff
    ∀ z : Ext.{u} (C := YL.Modules)
      ((Scheme.Modules.pushforward iDiag).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
      ((Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeProjection K L
        (hypersurfaceToBase p hp))).obj (sheafOfModules (grading (equationIdeal p hp)) 1)) 2,
      z ≠ 0 → (Ext.mk₀.{u} (C := YL.Modules)
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit iDiag)).comp z
        (zero_add 2) ≠ 0 := by
  dsimp only
  intro hExtYL hExtCoeff hExtAmbient hExtLocalAmbient hExtLocalCoeff
  letI := hExtYL
  letI := hExtCoeff
  letI := hExtAmbient
  letI := hExtLocalAmbient
  letI := hExtLocalCoeff
  intro z hz
  let e := hypersurfaceBaseChangeIso (algebraMap K L) p hp
  let iDiag := cubicPointTraceFieldBaseChangeRationalPoint K L (hypersurfaceToBase p hp) i hi
  let iCoeff := cubicDiagonalCoefficientPoint223 K L p hp i hi
  let pL := p.map (algebraMap K L)
  let hpL := hp.map (algebraMap K L)
  let N := (Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeProjection K L
    (hypersurfaceToBase p hp))).obj (sheafOfModules (grading (equationIdeal p hp)) 1)
  letI : EnoughInjectives (schemeBaseChangeToField (L := L) (hypersurface p hp)
      (hypersurfaceToBase p hp)).Modules :=
    sheafOfModules_enoughInjectives _
  letI : IsClosedImmersion iCoeff :=
    cubicDiagonalCoefficientPoint_isClosedImmersion223 K L p hp i hi
  let B := cubicDiagonalCoefficientNegativeTwistIso223 K L p hp 1
  let zPoint := schemeIsoClosedPointExtTransport223 e iDiag N
    (sheafOfModules (grading (equationIdeal pL hpL)) 1) B 2 z
  have hPoint : zPoint ≠ 0 := by
    intro hzero
    exact hz ((schemeIsoClosedPointExtTransport_eq_zero_iff223 e iDiag N _ B 2 z).mp hzero)
  let c := closedImmersionIdealTwistSequenceUnitTargetIso iCoeff
  let zSupported := extPrecompIsoOfIso c.symm zPoint
  have hSupported : zSupported ≠ 0 := by
    intro hzero
    apply hPoint
    apply (extPrecompIsoOfIso c.symm).injective
    simpa only [map_zero] using hzero
  have hpL0 : pL ≠ 0 := by
    intro hzero
    apply hp0
    apply MvPolynomial.map_injective (algebraMap K L) (algebraMap K L).injective
    simpa only [pL, map_zero] using hzero
  letI : Smooth (hypersurfaceToBase pL hpL) :=
    smooth_hypersurfaceToBase_map (algebraMap K L) p hp
  have hUnit := @smoothCubic_rationalSupportedPoint_unitPrecomp_ne_zero221.{u}
    L inferInstance pL hpL hpL0 inferInstance iCoeff inferInstance
    (cubicDiagonalCoefficientPoint_rational223 K L p hp i hi)
    hExtAmbient hExtCoeff hExtLocalAmbient hExtLocalCoeff zSupported hSupported
  intro hzero
  have hPointUnit := schemeIsoClosedPointExtTransport_unit_eq_zero223 e iDiag N _ B 2 z hzero
  apply hUnit
  change (Ext.mk₀.{u} (C := (hypersurface pL hpL).Modules)
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit iCoeff ≫ c.inv)).comp
    ((Ext.mk₀.{u} (C := (hypersurface pL hpL).Modules) c.hom).comp
      zPoint (zero_add 2)) (zero_add 2) = 0
  rw [Ext.mk₀_comp_mk₀_assoc]
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    iCoeff, cubicDiagonalCoefficientPoint223, zPoint] using hPointUnit

end PfaffianDescent.ProjectiveNegativeTwist
