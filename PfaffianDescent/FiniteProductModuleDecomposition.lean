import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# The regular module of a finite product ring

For a finite product `R = ∏ i, R i`, the regular `R`-module is the finite
biproduct of the coordinate modules obtained by restriction of scalars along
the evaluation maps.  This is the module-theoretic decomposition underlying
the split finite-support calculation in Voisin's argument.
-/

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits

universe u

variable {J : Type u} [Finite J] (R : J → Type u) [∀ i, CommRing (R i)]

/-- The `i`th factor, regarded as a module over the product ring through
coordinate evaluation. -/
noncomputable def productCoordinateModule (i : J) :
    ModuleCat.{u} (∀ j, R j) :=
  (ModuleCat.restrictScalars
    (Pi.evalRingHom R i)).obj
      (ModuleCat.of (R i) (R i))

/-- The regular module of a product ring is linearly equivalent to the
product of its coordinate modules. -/
noncomputable def productRingLinearEquivCoordinatePi :
    (∀ i, R i) ≃ₗ[(∀ i, R i)] (∀ i, productCoordinateModule R i) where
  toFun x i := x i
  invFun x i := x i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    ext i
    rfl

/-- Categorical form of the coordinate decomposition: the finite biproduct
of the coordinate modules is isomorphic to the regular module. -/
noncomputable def productCoordinateBiproductIsoRegular :
    (⨁ fun i ↦ productCoordinateModule R i) ≅
      ModuleCat.of (∀ i, R i) (∀ i, R i) := by
  let ePi : (⨁ fun i ↦ productCoordinateModule R i) ≅
      ModuleCat.of (∀ i, R i) (∀ i, productCoordinateModule R i) :=
    IsLimit.conePointUniqueUpToIso
      (biproduct.isLimit (fun i ↦ productCoordinateModule R i))
      (ModuleCat.HasLimit.productLimitCone
        (fun i ↦ productCoordinateModule R i)).isLimit
  exact ePi ≪≫
    LinearEquiv.toModuleIso (productRingLinearEquivCoordinatePi R).symm

end PfaffianDescent
