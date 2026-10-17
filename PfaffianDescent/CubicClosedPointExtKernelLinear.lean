import PfaffianDescent.CubicPointCompatibleNegativeThreeResidueEquiv
import PfaffianDescent.VoisinSectionRestriction
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # The actual closed-point Ext restriction as a linear map

The negative-three point residue is an actual additive equivalence with the
residue field. Composing its inverse with the original unit restriction and
the intrinsic quadratic duality gives a linear map over the ground field.
Linearity follows from the proved field-trace pairing formula and does not
require its geometric coefficient to be nonzero.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- In the unchanged actual point residue coordinate, unit restriction pairs
with a quadratic by the original geometric field-trace formula. -/
theorem cubicClosedPointExtKernel_pairing
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hDomain : IsDomain (CoordinateRing (equationIdeal p hp))]
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [hClosed : IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [hExtAmbient : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))]
    (a : L) (q : MvPolynomial.homogeneousSubmodule (Fin 4) K 2) :
    (@cubicIntrinsicNegativeThreeCohomologyTwoEquivDualQuadratic K _ p hp hp0
        hDomain hExtAmbient hExt)
      ((Ext.mk₀.{u} (C := (hypersurface p hp).Modules)
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
          (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)).comp
        (((@cubicPointCompatibleNegativeThreeResidueEquiv K _ p hp hp0 hSmooth
          L _ i hClosed hExt hExtStalk)).symm a)
        (zero_add 2)) q =
    Algebra.trace K L ((@cubicCanonicalPointResidueTraceCoefficient K _ p hp hp0 hDomain hSmooth
        L _ _ _ _ i hClosed hi hExtAmbient hExt hExtStalk) * a *
      (@cubicPointCompatibleQuadraticRestrictionScalar K _ p hp hp0 hSmooth
        L _ i hClosed hExt hExtStalk q)) := by
  simpa only [← cubicPointCompatibleNegativeThreeResidueEquiv_apply,
    AddEquiv.apply_symm_apply] using
    @cubicPointCompatible_pairing_eq_fieldTrace K _ p hp hp0 hDomain hSmooth
      L _ _ _ _ i hClosed hi hExtAmbient hExt hExtStalk
      ((@cubicPointCompatibleNegativeThreeResidueEquiv K _ p hp hp0 hSmooth
        L _ i hClosed hExt hExtStalk).symm a) q

set_option backward.isDefEq.respectTransparency false in
/-- The original actual point restriction, in residue and quadratic-dual
coordinates. Its construction permits a zero geometric trace coefficient. -/
def cubicClosedPointExtKernelMap
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hDomain : IsDomain (CoordinateRing (equationIdeal p hp))]
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [hClosed : IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [hExtAmbient : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))] :
    L →ₗ[K] Module.Dual K (MvPolynomial.homogeneousSubmodule (Fin 4) K 2) where
  toFun a := (@cubicIntrinsicNegativeThreeCohomologyTwoEquivDualQuadratic K _ p hp hp0
        hDomain hExtAmbient hExt)
    ((Ext.mk₀.{u} (C := (hypersurface p hp).Modules)
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
        (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)).comp
      (((@cubicPointCompatibleNegativeThreeResidueEquiv K _ p hp hp0 hSmooth
          L _ i hClosed hExt hExtStalk)).symm a)
      (zero_add 2))
  map_add' a b := by
    ext q
    rw [(@cubicClosedPointExtKernel_pairing K _ p hp hp0 hDomain hSmooth
        L _ _ _ _ i hClosed hi hExtAmbient hExt hExtStalk),
      LinearMap.add_apply,
      (@cubicClosedPointExtKernel_pairing K _ p hp hp0 hDomain hSmooth
        L _ _ _ _ i hClosed hi hExtAmbient hExt hExtStalk),
      (@cubicClosedPointExtKernel_pairing K _ p hp hp0 hDomain hSmooth
        L _ _ _ _ i hClosed hi hExtAmbient hExt hExtStalk)]
    rw [mul_add, add_mul, map_add]
  map_smul' r a := by
    ext q
    rw [(@cubicClosedPointExtKernel_pairing K _ p hp hp0 hDomain hSmooth
        L _ _ _ _ i hClosed hi hExtAmbient hExt hExtStalk),
      LinearMap.smul_apply,
      (@cubicClosedPointExtKernel_pairing K _ p hp hp0 hDomain hSmooth
        L _ _ _ _ i hClosed hi hExtAmbient hExt hExtStalk)]
    rw [mul_smul_comm, smul_mul_assoc, map_smul]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The forward map retains exactly the original unit-restriction Ext class. -/
@[simp] theorem cubicClosedPointExtKernelMap_apply
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hDomain : IsDomain (CoordinateRing (equationIdeal p hp))]
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [hClosed : IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [hExtAmbient : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))]
    (a : L) :
    cubicClosedPointExtKernelMap K p hp hp0 i hi a =
      (@cubicIntrinsicNegativeThreeCohomologyTwoEquivDualQuadratic K _ p hp hp0
        hDomain hExtAmbient hExt)
        ((Ext.mk₀.{u} (C := (hypersurface p hp).Modules)
          (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
            (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)).comp
          (((@cubicPointCompatibleNegativeThreeResidueEquiv K _ p hp hp0 hSmooth
          L _ i hClosed hExt hExtStalk)).symm a)
          (zero_add 2)) := rfl

end PfaffianDescent.ProjectiveNegativeTwist
