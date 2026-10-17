import PfaffianDescent.ThreePositiveZeroNegativeUnitPairing

/-! SOURCE ONLY / UNVERIFIED. Exact native entry formulas after the SAME
O(3) mixed pairing identifications, including the tensor-unit normalization. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
universe u
-- Observed actual functor-object/map and grading/category alias mismatches.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem nativeTwistedEntryOfSquare
    {D : Type*} [Category D] {A B A' B' : D}
    (eA : A ≅ A') (eB : B ≅ B') (m : A ⟶ B) (n : A' ⟶ B')
    (h : m ≫ eB.hom = eA.hom ≫ n) : eA.inv ≫ m ≫ eB.hom = n := by
  calc
    _ = eA.inv ≫ (eA.hom ≫ n) := congrArg (fun f => eA.inv ≫ f) h
    _ = _ := eA.inv_hom_id_assoc _

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K
local notation "T3" => schemeModuleTensorRight (positiveSheafOfModules PS 3)

/-- Native tensor transport of one entry O(-6)→O(-4) is its SAME
quadric multiplication O(-3)→O(-1). -/
theorem p3OThreeTensor_six_four_quadric_entry (q : PS 2) :
    (p3OThreeTensorNegativeSixIso K).inv ≫ (T3).map (mulHomogeneous PS q 4) ≫
      (p3OThreeTensorNegativeFourIso K).hom = mulHomogeneous PS q 1 := by
  have hsquare : schemeModuleTensorMap (mulHomogeneous PS q 4)
      (𝟙 (positiveSheafOfModules PS 3)) ≫
      (schemeModuleTensorSymmetry (sheafOfModules PS 4)
        (positiveSheafOfModules PS 3)).hom ≫
      positiveNegativeDifferencePairing PS 3 4 (by decide) =
    (schemeModuleTensorSymmetry (sheafOfModules PS 6)
        (positiveSheafOfModules PS 3)).hom ≫
      positiveNegativeDifferencePairing PS 3 6 (by decide) ≫ mulHomogeneous PS q 1 := by
    rw [← Category.assoc, schemeModuleTensorSymmetry_naturality]
    simpa only [Category.assoc] using congrArg
      (fun t => (schemeModuleTensorSymmetry (sheafOfModules PS 6)
        (positiveSheafOfModules PS 3)).hom ≫ t)
      (threeQuadricPairing_six_four_naturality PS q)
  have hnative : schemeModuleTensorMap (mulHomogeneous PS q 4)
      (𝟙 (positiveSheafOfModules PS 3)) ≫
      (p3OThreeTensorNegativeFourIso K).hom =
      (p3OThreeTensorNegativeSixIso K).hom ≫ mulHomogeneous PS q 1 := by
    simpa only [p3OThreeTensorNegativeSixIso, p3OThreeTensorNegativeFourIso,
      Iso.trans_hom, asIso_hom, Category.assoc] using hsquare
  simpa only [schemeModuleTensorRight] using
    (nativeTwistedEntryOfSquare (D := (Proj PS).Modules)
      (p3OThreeTensorNegativeSixIso K) (p3OThreeTensorNegativeFourIso K)
      (schemeModuleTensorMap (mulHomogeneous PS q 4) (𝟙 (positiveSheafOfModules PS 3)))
      (mulHomogeneous PS q 1) hnative)

/-- Native tensor transport of one entry O(-4)→O(-2) is its SAME
crossing quadric multiplication O(-1)→O(1). -/
theorem p3OThreeTensor_four_two_quadric_entry (q : PS 2) :
    (p3OThreeTensorNegativeFourIso K).inv ≫ (T3).map (mulHomogeneous PS q 2) ≫
      (p3OThreeTensorNegativeTwoIso K).hom =
        negativeToPositiveMulHomogeneous PS q 1 (by decide) := by
  have hsquare : schemeModuleTensorMap (mulHomogeneous PS q 2)
      (𝟙 (positiveSheafOfModules PS 3)) ≫
      (schemeModuleTensorSymmetry (sheafOfModules PS 2)
        (positiveSheafOfModules PS 3)).hom ≫
      positiveNegativePositiveDifferencePairing PS 3 2 (by decide) =
    (schemeModuleTensorSymmetry (sheafOfModules PS 4)
        (positiveSheafOfModules PS 3)).hom ≫
      positiveNegativeDifferencePairing PS 3 4 (by decide) ≫ negativeToPositiveMulHomogeneous PS q 1 (by decide) := by
    rw [← Category.assoc, schemeModuleTensorSymmetry_naturality]
    simpa only [Category.assoc] using congrArg
      (fun t => (schemeModuleTensorSymmetry (sheafOfModules PS 4)
        (positiveSheafOfModules PS 3)).hom ≫ t)
      (threeQuadricPairing_four_two_naturality PS q)
  have hnative : schemeModuleTensorMap (mulHomogeneous PS q 2)
      (𝟙 (positiveSheafOfModules PS 3)) ≫
      (p3OThreeTensorNegativeTwoIso K).hom =
      (p3OThreeTensorNegativeFourIso K).hom ≫ negativeToPositiveMulHomogeneous PS q 1 (by decide) := by
    simpa only [p3OThreeTensorNegativeFourIso, p3OThreeTensorNegativeTwoIso,
      Iso.trans_hom, asIso_hom, Category.assoc] using hsquare
  simpa only [schemeModuleTensorRight] using
    (nativeTwistedEntryOfSquare (D := (Proj PS).Modules)
      (p3OThreeTensorNegativeFourIso K) (p3OThreeTensorNegativeTwoIso K)
      (schemeModuleTensorMap (mulHomogeneous PS q 2) (𝟙 (positiveSheafOfModules PS 3)))
      (negativeToPositiveMulHomogeneous PS q 1 (by decide)) hnative)

/-- Native tensor transport of the SAME last quadric, including the actual
O(0)→O and tensor-unit maps, is literal positive multiplication O(1)→O(3). -/
theorem p3OThreeTensor_two_unit_quadric_entry (q : PS 2) :
    (p3OThreeTensorNegativeTwoIso K).inv ≫
      (T3).map (show sheafOfModules PS 2 ⟶ SheafOfModules.unit (Proj PS).ringCatSheaf from
        mulHomogeneousToUnit PS (d := 2) q) ≫
      (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 3)).hom =
        positiveMulHomogeneous PS q 1 := by
  have hmap : schemeModuleTensorMap (mulHomogeneousToUnit PS q)
      (𝟙 (positiveSheafOfModules PS 3)) =
      schemeModuleTensorMap (mulHomogeneous PS q 0) (𝟙 (positiveSheafOfModules PS 3)) ≫
        schemeModuleTensorMap (unitIsoZeroTwist PS).inv
          (𝟙 (positiveSheafOfModules PS 3)) := by
    rw [schemeModuleTensorMap_comp]
    simp [mulHomogeneousToUnit]
  have hsquare : schemeModuleTensorMap (mulHomogeneousToUnit PS q)
      (𝟙 (positiveSheafOfModules PS 3)) ≫
      (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 3)).hom =
    (schemeModuleTensorSymmetry (sheafOfModules PS 2)
      (positiveSheafOfModules PS 3)).hom ≫
      positiveNegativePositiveDifferencePairing PS 3 2 (by decide) ≫
      positiveMulHomogeneous PS q 1 := by
    rw [hmap, Category.assoc, ← threePositiveZeroNegativePairing_eq_unit]
    rw [← Category.assoc, schemeModuleTensorSymmetry_naturality]
    simpa only [Category.assoc] using congrArg
      (fun t => (schemeModuleTensorSymmetry (sheafOfModules PS 2)
        (positiveSheafOfModules PS 3)).hom ≫ t)
      (threeQuadricPairing_two_zero_naturality PS q)
  have hnative : schemeModuleTensorMap (mulHomogeneousToUnit PS q)
      (𝟙 (positiveSheafOfModules PS 3)) ≫
      (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 3)).hom =
      (p3OThreeTensorNegativeTwoIso K).hom ≫ positiveMulHomogeneous PS q 1 := by
    simpa only [p3OThreeTensorNegativeTwoIso, Iso.trans_hom, asIso_hom,
      Category.assoc] using hsquare
  -- The native square already fixes the actual unit-side source and target.
  -- Compose that square directly; do not reinfer its rich unit domain as eB.
  have hcancel := congrArg
    (fun t => (p3OThreeTensorNegativeTwoIso K).inv ≫ t) hnative
  simpa only [schemeModuleTensorRight] using
    hcancel.trans ((p3OThreeTensorNegativeTwoIso K).inv_hom_id_assoc
      (positiveMulHomogeneous PS q 1))

end PfaffianDescent.ProjectiveNegativeTwist
