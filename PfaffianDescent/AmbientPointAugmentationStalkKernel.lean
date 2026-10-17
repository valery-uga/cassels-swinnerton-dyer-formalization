import PfaffianDescent.AmbientPointKoszulUnitStalk
import PfaffianDescent.CubicPointQuadraticRestrictionPointFiber

/-! # The kernel of the actual standard-point augmentation

The actual structure-sheaf restriction has the maximal ideal as its stalk
kernel. The comparison uses the native structure-ring stalk isomorphism,
so it is compatible with the coefficients of the actual Koszul differential.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

local instance pointIdeal_prime (x : Proj PS) :
    (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x

set_option backward.isDefEq.respectTransparency false in
/-- The actual augmentation vanishes precisely on the native homogeneous
maximal ideal, without a supplied restriction compatibility square. -/
theorem ambientPointAugmentation_stalk_eq_zero_iff
    (k : Spec (.of K))
    (z : (schemeModuleStalkFunctor (Proj PS) (ambientPointKoszul_point K k)).obj
      (SheafOfModules.unit (Proj PS).ringCatSheaf)) :
    (schemeModuleStalkFunctor (Proj PS) (ambientPointKoszul_point K k)).map
        (ambientPointKoszul_augmentation K) z = 0 ↔
      ambientPointKoszul_unitStalkCoordinate K (ambientPointKoszul_point K k) z ∈
        IsLocalRing.maximalIdeal (AtPrime PS
          (pointIdeal PS (ambientPointKoszul_point K k))) := by
  let x := ambientPointKoszul_point K k
  letI : IsLocalRing ((Proj PS).presheaf.stalk x) := inferInstance
  letI : IsLocalRing ((ProjectiveSpectrum.Proj.structureSheaf PS).presheaf.stalk x) :=
    show IsLocalRing ((Proj PS).presheaf.stalk x) from inferInstance
  let e := cubicPointQuadraticRestrictionPushforwardResidueIso
    (ambientPointKoszul_point K) k
  have hres := cubicPointQuadraticRestrictionPushforwardResidueIso_unit
    (ambientPointKoszul_point K) k z
  have hzero : (schemeModuleStalkFunctor (Proj PS) x).map
        (ambientPointKoszul_augmentation K) z = 0 ↔
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal ((Proj PS).presheaf.stalk x))
        ((schemeModuleUnitStalkIso (Proj PS) x).hom z) = 0 := by
    constructor
    · intro h
      rw [← hres]
      change e.hom ((schemeModuleStalkFunctor (Proj PS) x).map
        (ambientPointKoszul_augmentation K) z) = 0
      rw [h, map_zero]
    · intro h
      apply (ConcreteCategory.bijective_of_isIso e.hom).1
      change e.hom ((schemeModuleStalkFunctor (Proj PS) x).map
        (ambientPointKoszul_augmentation K) z) = e.hom 0
      rw [map_zero]
      exact hres.trans h
  rw [Ideal.Quotient.eq_zero_iff_mem] at hzero
  have hmem : Proj.stalkIso' PS x ((schemeModuleUnitStalkIso (Proj PS) x).hom z) ∈
      IsLocalRing.maximalIdeal (AtPrime PS (pointIdeal PS x)) ↔
      (schemeModuleUnitStalkIso (Proj PS) x).hom z ∈
        IsLocalRing.maximalIdeal ((Proj PS).presheaf.stalk x) := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal (Proj.stalkIso' PS x)]
    exact Ideal.apply_mem_of_equiv_iff
  exact hzero.trans hmem.symm

end PfaffianDescent.ProjectiveNegativeTwist
