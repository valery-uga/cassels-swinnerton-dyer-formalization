import PfaffianDescent.TwoPositiveZeroNegativeUnitPairing
import PfaffianDescent.ThreeQuadricOTwoTensorTerms

/-! SOURCE ONLY / UNVERIFIED. Fraction naturality for the actual O(2)
last entry; its source is the actual unit module after canonical pairing. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open scoped DirectSum Pointwise TensorProduct
open DirectSum SetLike Localization
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
universe u
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem threeQuadricOTwoPairingPresheaf_two_zero_naturality (q : 𝒜 2) :
    PresheafOfModules.Monoidal.tensorHom (𝟙 (positiveModulePresheaf 𝒜 2))
      (mulHomogeneous 𝒜 q 0).val ≫
        positiveNegativePositiveDifferencePairingPresheaf 𝒜 2 0 (by decide) =
      positiveNegativePositiveDifferencePairingPresheaf 𝒜 2 2 (by decide) ≫
        (positiveMulHomogeneous 𝒜 q 0).val := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p z
  apply Subtype.ext
  funext x
  change p.1 x * (algebraMap A (PositiveFiber 𝒜 x.1) (q : A) * z.1 x) =
    algebraMap A (PositiveFiber 𝒜 x.1) (q : A) * (p.1 x * z.1 x)
  ring

theorem threeQuadricOTwoPairing_two_zero_naturality (q : 𝒜 2) :
    schemeModuleTensorMap (𝟙 (positiveSheafOfModules 𝒜 2))
      (mulHomogeneous 𝒜 q 0) ≫
        positiveNegativePositiveDifferencePairing 𝒜 2 0 (by decide) =
      positiveNegativePositiveDifferencePairing 𝒜 2 2 (by decide) ≫
        positiveMulHomogeneous 𝒜 q 0 := by
  rw [schemeModuleTensorMap_eq_sheafification]
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  have hsrc : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 2).val
        (sheafOfModules 𝒜 2).val)
      (positiveSheafOfModules 𝒜 0)
      (positiveNegativePositiveDifferencePairing 𝒜 2 2 (by decide)) =
      positiveNegativePositiveDifferencePairingPresheaf 𝒜 2 2 (by decide) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  have htgt : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 2).val
        (sheafOfModules 𝒜 0).val)
      (positiveSheafOfModules 𝒜 2)
      (positiveNegativePositiveDifferencePairing 𝒜 2 0 (by decide)) =
      positiveNegativePositiveDifferencePairingPresheaf 𝒜 2 0 (by decide) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  rw [htgt]
  erw [adj.homEquiv_naturality_right]
  rw [hsrc]
  exact threeQuadricOTwoPairingPresheaf_two_zero_naturality 𝒜 q

/-- Infer the genuine native tensor entry before specializing the grading.
Its map is exactly the map of the existing right-tensor functor. -/
private def threeQuadricOTwoNativeTensorUnitEntry (q : 𝒜 2) :=
  schemeModuleTensorMap (mulHomogeneousToUnit 𝒜 q)
    (𝟙 (positiveSheafOfModules 𝒜 2))

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K
local notation "T2" => schemeModuleTensorRight (positiveSheafOfModules PS 2)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual transported last entry is multiplication by q from O,
using the internally constructed unit/positive-zero identification. -/
theorem p3OTwoTensor_two_unit_quadric_entry (q : PS 2) :
    (p3OTwoTensorNegativeTwoIso K).inv ≫ threeQuadricOTwoNativeTensorUnitEntry PS q ≫
      (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 2)).hom =
    (p3OTwoUnitPositiveZeroIso K).hom ≫ positiveMulHomogeneous PS q 0 := by
  have hmap : schemeModuleTensorMap (mulHomogeneousToUnit PS q)
      (𝟙 (positiveSheafOfModules PS 2)) =
      schemeModuleTensorMap (mulHomogeneous PS q 0) (𝟙 (positiveSheafOfModules PS 2)) ≫
        schemeModuleTensorMap (unitIsoZeroTwist PS).inv
          (𝟙 (positiveSheafOfModules PS 2)) := by
    rw [schemeModuleTensorMap_comp]
    simp [mulHomogeneousToUnit]
  have hsquare : schemeModuleTensorMap (mulHomogeneousToUnit PS q)
      (𝟙 (positiveSheafOfModules PS 2)) ≫
      (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 2)).hom =
    (schemeModuleTensorSymmetry (sheafOfModules PS 2)
      (positiveSheafOfModules PS 2)).hom ≫
      positiveNegativePositiveDifferencePairing PS 2 2 (by decide) ≫
      positiveMulHomogeneous PS q 0 := by
    rw [hmap, Category.assoc, ← twoPositiveZeroNegativePairing_eq_unit]
    rw [← Category.assoc, schemeModuleTensorSymmetry_naturality]
    simpa only [Category.assoc] using congrArg
      (fun t => (schemeModuleTensorSymmetry (sheafOfModules PS 2)
        (positiveSheafOfModules PS 2)).hom ≫ t)
      (threeQuadricOTwoPairing_two_zero_naturality PS q)
  have hnative : threeQuadricOTwoNativeTensorUnitEntry PS q ≫
      (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 2)).hom =
      (p3OTwoTensorNegativeTwoIso K).hom ≫
        (p3OTwoUnitPositiveZeroIso K).hom ≫ positiveMulHomogeneous PS q 0 := by
    simpa only [threeQuadricOTwoNativeTensorUnitEntry, p3OTwoTensorNegativeTwoIso,
      Iso.trans_hom, Iso.symm_hom,
      asIso_hom, Category.assoc, Iso.inv_hom_id_assoc] using hsquare
  apply (cancel_epi (p3OTwoTensorNegativeTwoIso K).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hnative

end PfaffianDescent.ProjectiveNegativeTwist
