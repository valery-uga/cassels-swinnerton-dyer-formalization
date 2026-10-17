import PfaffianDescent.ThreeQuadricOThreeTensorTerms
import PfaffianDescent.ProjectiveCrossingTwist

/-! SOURCE ONLY / UNVERIFIED. Actual quadric-entry naturality for all three
transitions in the native O(3) twist, including the negative-to-positive
crossing. No map identity or geometric certificate is an input. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open scoped DirectSum Pointwise TensorProduct
open DirectSum SetLike Localization
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
universe u
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem threeQuadricPairingPresheaf_six_four_naturality (q : 𝒜 2) :
    PresheafOfModules.Monoidal.tensorHom (𝟙 (positiveModulePresheaf 𝒜 3))
      (mulHomogeneous 𝒜 q 4).val ≫
        positiveNegativeDifferencePairingPresheaf 𝒜 3 4 (by decide) =
      positiveNegativeDifferencePairingPresheaf 𝒜 3 6 (by decide) ≫
        (mulHomogeneous 𝒜 q 1).val := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p z
  apply Subtype.ext
  funext x
  change p.1 x * (algebraMap A (PositiveFiber 𝒜 x.1) (q : A) * z.1 x) =
    algebraMap A (PositiveFiber 𝒜 x.1) (q : A) * (p.1 x * z.1 x)
  ring

theorem threeQuadricPairing_six_four_naturality (q : 𝒜 2) :
    schemeModuleTensorMap (𝟙 (positiveSheafOfModules 𝒜 3))
      (mulHomogeneous 𝒜 q 4) ≫
        positiveNegativeDifferencePairing 𝒜 3 4 (by decide) =
      positiveNegativeDifferencePairing 𝒜 3 6 (by decide) ≫
        mulHomogeneous 𝒜 q 1 := by
  rw [schemeModuleTensorMap_eq_sheafification]
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  have hsrc : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 3).val
        (sheafOfModules 𝒜 6).val)
      (sheafOfModules 𝒜 3)
      (positiveNegativeDifferencePairing 𝒜 3 6 (by decide)) =
      positiveNegativeDifferencePairingPresheaf 𝒜 3 6 (by decide) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  have htgt : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 3).val
        (sheafOfModules 𝒜 4).val)
      (sheafOfModules 𝒜 1)
      (positiveNegativeDifferencePairing 𝒜 3 4 (by decide)) =
      positiveNegativeDifferencePairingPresheaf 𝒜 3 4 (by decide) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  rw [htgt]
  erw [adj.homEquiv_naturality_right]
  rw [hsrc]
  exact threeQuadricPairingPresheaf_six_four_naturality 𝒜 q

theorem threeQuadricPairingPresheaf_four_two_naturality (q : 𝒜 2) :
    PresheafOfModules.Monoidal.tensorHom (𝟙 (positiveModulePresheaf 𝒜 3))
      (mulHomogeneous 𝒜 q 2).val ≫
        positiveNegativePositiveDifferencePairingPresheaf 𝒜 3 2 (by decide) =
      positiveNegativeDifferencePairingPresheaf 𝒜 3 4 (by decide) ≫
        (negativeToPositiveMulHomogeneous 𝒜 q 1 (by decide)).val := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p z
  apply Subtype.ext
  funext x
  change p.1 x * (algebraMap A (PositiveFiber 𝒜 x.1) (q : A) * z.1 x) =
    algebraMap A (PositiveFiber 𝒜 x.1) (q : A) * (p.1 x * z.1 x)
  ring

theorem threeQuadricPairing_four_two_naturality (q : 𝒜 2) :
    schemeModuleTensorMap (𝟙 (positiveSheafOfModules 𝒜 3))
      (mulHomogeneous 𝒜 q 2) ≫
        positiveNegativePositiveDifferencePairing 𝒜 3 2 (by decide) =
      positiveNegativeDifferencePairing 𝒜 3 4 (by decide) ≫
        negativeToPositiveMulHomogeneous 𝒜 q 1 (by decide) := by
  rw [schemeModuleTensorMap_eq_sheafification]
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  have hsrc : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 3).val
        (sheafOfModules 𝒜 4).val)
      (sheafOfModules 𝒜 1)
      (positiveNegativeDifferencePairing 𝒜 3 4 (by decide)) =
      positiveNegativeDifferencePairingPresheaf 𝒜 3 4 (by decide) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  have htgt : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 3).val
        (sheafOfModules 𝒜 2).val)
      (positiveSheafOfModules 𝒜 1)
      (positiveNegativePositiveDifferencePairing 𝒜 3 2 (by decide)) =
      positiveNegativePositiveDifferencePairingPresheaf 𝒜 3 2 (by decide) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  rw [htgt]
  erw [adj.homEquiv_naturality_right]
  rw [hsrc]
  exact threeQuadricPairingPresheaf_four_two_naturality 𝒜 q

theorem threeQuadricPairingPresheaf_two_zero_naturality (q : 𝒜 2) :
    PresheafOfModules.Monoidal.tensorHom (𝟙 (positiveModulePresheaf 𝒜 3))
      (mulHomogeneous 𝒜 q 0).val ≫
        positiveNegativePositiveDifferencePairingPresheaf 𝒜 3 0 (by decide) =
      positiveNegativePositiveDifferencePairingPresheaf 𝒜 3 2 (by decide) ≫
        (positiveMulHomogeneous 𝒜 q 1).val := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p z
  apply Subtype.ext
  funext x
  change p.1 x * (algebraMap A (PositiveFiber 𝒜 x.1) (q : A) * z.1 x) =
    algebraMap A (PositiveFiber 𝒜 x.1) (q : A) * (p.1 x * z.1 x)
  ring

theorem threeQuadricPairing_two_zero_naturality (q : 𝒜 2) :
    schemeModuleTensorMap (𝟙 (positiveSheafOfModules 𝒜 3))
      (mulHomogeneous 𝒜 q 0) ≫
        positiveNegativePositiveDifferencePairing 𝒜 3 0 (by decide) =
      positiveNegativePositiveDifferencePairing 𝒜 3 2 (by decide) ≫
        positiveMulHomogeneous 𝒜 q 1 := by
  rw [schemeModuleTensorMap_eq_sheafification]
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  have hsrc : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 3).val
        (sheafOfModules 𝒜 2).val)
      (positiveSheafOfModules 𝒜 1)
      (positiveNegativePositiveDifferencePairing 𝒜 3 2 (by decide)) =
      positiveNegativePositiveDifferencePairingPresheaf 𝒜 3 2 (by decide) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  have htgt : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 3).val
        (sheafOfModules 𝒜 0).val)
      (positiveSheafOfModules 𝒜 3)
      (positiveNegativePositiveDifferencePairing 𝒜 3 0 (by decide)) =
      positiveNegativePositiveDifferencePairingPresheaf 𝒜 3 0 (by decide) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  rw [htgt]
  erw [adj.homEquiv_naturality_right]
  rw [hsrc]
  exact threeQuadricPairingPresheaf_two_zero_naturality 𝒜 q

end PfaffianDescent.ProjectiveNegativeTwist
