import PfaffianDescent.CorayProperGeometricallyIntegralUnitSectionsRankOne
import PfaffianDescent.SchemeModuleSupportedFiberGroundDimension
import PfaffianDescent.CorayEntireModelIncidenceCycle
import Mathlib.LinearAlgebra.Dimension.Free

/-! Independently defined structural K/M section actions are compared through
literal Spec composition. Proper/GI of SAME D derives h0_M=1, and its literal
coefficient-component pushforward has original-K H0 rank [M:K]. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AllCharacteristics.HomogeneousProjective
universe u
variable {K M : Type u} [Field K] [Field M] [Algebra K M]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Literal Spec composition restricts the independent structural section
coefficients to the original field on every open. -/
theorem schemeOpenBaseRingHom_fieldRestriction
    {Y : Scheme.{u}} (piM : Y ⟶ Spec (CommRingCat.of M))
    (U : Y.Opens) (c : K) :
    schemeOpenBaseRingHom
        (piM ≫ Spec.map (CommRingCat.ofHom (algebraMap K M))) U c =
      schemeOpenBaseRingHom piM U (algebraMap K M c) := by
  unfold schemeOpenBaseRingHom
  rw [affineFunctionHom_comp_Spec]
  rfl

/-- The original K action and own M action on the SAME section carrier form
a scalar tower; neither action is defined by transport from the other. -/
theorem schemeModuleOpenSections_fieldRestriction_isScalarTower
    {Y : Scheme.{u}} (piM : Y ⟶ Spec (CommRingCat.of M))
    (T : Y.Modules) (U : Y.Opens) :
    let V := SchemeModuleOpenSectionsOver
      (piM ≫ Spec.map (CommRingCat.ofHom (algebraMap K M))) T U
    letI : Module M V :=
      inferInstanceAs (Module M (SchemeModuleOpenSectionsOver piM T U))
    IsScalarTower K M V := by
  dsimp only
  let V := SchemeModuleOpenSectionsOver
    (piM ≫ Spec.map (CommRingCat.ofHom (algebraMap K M))) T U
  letI : Module M V :=
    inferInstanceAs (Module M (SchemeModuleOpenSectionsOver piM T U))
  letI : Module Γ(Y, U) V := (T.val.obj (op U)).isModule
  refine ⟨?_⟩
  intro c m s
  change schemeOpenBaseRingHom piM U (c • m) • s =
    schemeOpenBaseRingHom
      (piM ≫ Spec.map (CommRingCat.ofHom (algebraMap K M))) U c •
      (schemeOpenBaseRingHom piM U m • s)
  rw [Algebra.smul_def, map_mul, schemeOpenBaseRingHom_fieldRestriction]
  exact mul_smul _ _ _

/-- Own finite sections become finite for the original structural K action,
with the actual scalar-tower rank multiplication. No rank equality is supplied. -/
theorem schemeModuleOpenSections_fieldRestriction_finite_and_finrank
    [Module.Finite K M] {Y : Scheme.{u}}
    (piM : Y ⟶ Spec (CommRingCat.of M)) (T : Y.Modules) (U : Y.Opens)
    (hFinite : Module.Finite M (SchemeModuleOpenSectionsOver piM T U)) :
    let rho := piM ≫ Spec.map (CommRingCat.ofHom (algebraMap K M))
    Module.Finite K (SchemeModuleOpenSectionsOver rho T U) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver rho T U) =
        Module.finrank K M * Module.finrank M (SchemeModuleOpenSectionsOver piM T U) := by
  let rho := piM ≫ Spec.map (CommRingCat.ofHom (algebraMap K M))
  let V := SchemeModuleOpenSectionsOver rho T U
  letI : Module M V :=
    inferInstanceAs (Module M (SchemeModuleOpenSectionsOver piM T U))
  letI : IsScalarTower K M V :=
    schemeModuleOpenSections_fieldRestriction_isScalarTower (K := K) (M := M) piM T U
  letI : Module.Finite M V := hFinite
  letI : Module.Finite K V := Module.Finite.trans (R := K) M V
  exact ⟨inferInstance, (Module.finrank_mul_finrank K M V).symm⟩

/-- Proper geometric integrality derives finite original-K unit sections of
rank [M:K] on the SAME scheme viewed over K. No constants-rank premise occurs. -/
theorem properGeometricallyIntegral_unitTopSections_fieldRestriction_finite_and_finrank
    [Module.Finite K M] {Y : Scheme.{u}}
    (piM : Y ⟶ Spec (CommRingCat.of M)) [IsProper piM]
    [GeometricallyIntegral piM] :
    let rho := piM ≫ Spec.map (CommRingCat.ofHom (algebraMap K M))
    Module.Finite K (SchemeModuleOpenSectionsOver rho
      (SheafOfModules.unit Y.ringCatSheaf) ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver rho
        (SheafOfModules.unit Y.ringCatSheaf) ⊤) = Module.finrank K M := by
  letI : IsIntegral Y := GeometricallyIntegral.isIntegral_of_subsingleton piM
  have hOwn := integralProperGeometricallyIntegral_unitTopSections_finite_and_finrank_one (K := M) piM
  have hGround := schemeModuleOpenSections_fieldRestriction_finite_and_finrank
    (K := K) piM (SheafOfModules.unit Y.ringCatSheaf) ⊤ hOwn.1
  refine ⟨hGround.1, ?_⟩
  rw [hGround.2, hOwn.2, mul_one]

/-- The actual coefficient-component pushforward's top sections have finite
original-K rank r=[M:K]. Its actual base-composition equality and native
pushforward linear equivalence are proved APIs, not comparison hypotheses. -/
theorem coefficientComponentToOriginal_pushforwardUnit_topSections_finite_finrank
    [Module.Finite K M]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal)
    [GeometricallyIntegral (toBase D)] :
    let f := coefficientComponentToOriginal I D hID
    let B := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit (scheme D).ringCatSheaf)
    Module.Finite K (SchemeModuleOpenSectionsOver (toBase I) B ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver (toBase I) B ⊤) = Module.finrank K M := by
  let f := coefficientComponentToOriginal I D hID
  let OD : (scheme D).Modules := SheafOfModules.unit (scheme D).ringCatSheaf
  let result : ((scheme D) ⟶ Spec (CommRingCat.of K)) → Prop := fun rho =>
    Module.Finite K (SchemeModuleOpenSectionsOver rho OD ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver rho OD ⊤) = Module.finrank K M
  have hGround : result (toBase D ≫ Spec.map (CommRingCat.ofHom (algebraMap K M))) :=
    properGeometricallyIntegral_unitTopSections_fieldRestriction_finite_and_finrank (K := K) (M := M) (toBase D)
  have hBase : f ≫ toBase I =
      toBase D ≫ Spec.map (CommRingCat.ofHom (algebraMap K M)) :=
    (coefficientComponentToOriginal_finite_and_toBase I D hID).2
  have hActual : result (f ≫ toBase I) :=
    Eq.mpr (congrArg result hBase) hGround
  let E := schemeModulePushforward_topSectionsLinearEquiv (toBase I) f OD
  letI : Module.Finite K (SchemeModuleOpenSectionsOver (f ≫ toBase I) OD ⊤) := hActual.1
  exact ⟨Module.Finite.of_injective E.toLinearMap E.injective,
    E.finrank_eq.trans hActual.2⟩

end PfaffianDescent.Coray
