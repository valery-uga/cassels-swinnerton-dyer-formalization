import PfaffianDescent.ProjectiveMixedTwistPairing
import PfaffianDescent.ProjectivePositiveDifferencePairing
import PfaffianDescent.P3TwistTensorEquivalence

/-! SOURCE ONLY / UNVERIFIED. Actual mixed pairing naturality for the
O(2)-twisted quadric Koszul terms. Proofs compute the genuine presheaf
fraction multiplication and use the genuine sheafification adjunction.
No externally supplied tensor comparison or coordinate certificate. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open scoped DirectSum Pointwise TensorProduct
open DirectSum SetLike Localization
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
universe u
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem positiveNegativeDifferencePairingPresheaf_two_four_mul_naturality
    (s : 𝒜 2) :
    PresheafOfModules.Monoidal.tensorHom (positiveMulHomogeneous 𝒜 s 2).val
      (𝟙 (modulePresheaf 𝒜 4)) ≫
        positiveNegativePairingPresheaf 𝒜 4 =
      positiveNegativeDifferencePairingPresheaf 𝒜 2 4 (by omega) ≫
        (mulHomogeneous 𝒜 s 0).val := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  apply Subtype.ext
  funext x
  change (algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * p.1 x) * q.1 x =
    algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * (p.1 x * q.1 x)
  ring

theorem positiveNegativeDifferencePairing_two_four_mul_naturality
    (s : 𝒜 2) :
    schemeModuleTensorMap (positiveMulHomogeneous 𝒜 s 2)
      (𝟙 (sheafOfModules 𝒜 4)) ≫ positiveNegativePairing 𝒜 4 =
      positiveNegativeDifferencePairing 𝒜 2 4 (by omega) ≫
        mulHomogeneous 𝒜 s 0 := by
  rw [schemeModuleTensorMap_eq_sheafification]
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  have hpair :
      adj.homEquiv
        (PresheafOfModules.Monoidal.tensorObj
          (positiveSheafOfModules 𝒜 4).val (sheafOfModules 𝒜 4).val)
        (sheafOfModules 𝒜 0) (positiveNegativePairing 𝒜 4) =
      positiveNegativePairingPresheaf 𝒜 4 := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  have hdiff :
      adj.homEquiv
        (PresheafOfModules.Monoidal.tensorObj
          (positiveSheafOfModules 𝒜 2).val (sheafOfModules 𝒜 4).val)
        (sheafOfModules 𝒜 2)
        (positiveNegativeDifferencePairing 𝒜 2 4 (by omega)) =
      positiveNegativeDifferencePairingPresheaf 𝒜 2 4 (by omega) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  rw [hpair]
  erw [adj.homEquiv_naturality_right]
  rw [hdiff]
  exact positiveNegativeDifferencePairingPresheaf_two_four_mul_naturality 𝒜 s

theorem positiveNegativeDifferencePairingPresheaf_two_six_mul_naturality
    (s : 𝒜 4) :
    PresheafOfModules.Monoidal.tensorHom (positiveMulHomogeneous 𝒜 s 2).val
      (𝟙 (modulePresheaf 𝒜 6)) ≫
        positiveNegativePairingPresheaf 𝒜 6 =
      positiveNegativeDifferencePairingPresheaf 𝒜 2 6 (by omega) ≫
        (mulHomogeneous 𝒜 s 0).val := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  apply Subtype.ext
  funext x
  change (algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * p.1 x) * q.1 x =
    algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * (p.1 x * q.1 x)
  ring

theorem positiveNegativeDifferencePairing_two_six_mul_naturality
    (s : 𝒜 4) :
    schemeModuleTensorMap (positiveMulHomogeneous 𝒜 s 2)
      (𝟙 (sheafOfModules 𝒜 6)) ≫ positiveNegativePairing 𝒜 6 =
      positiveNegativeDifferencePairing 𝒜 2 6 (by omega) ≫
        mulHomogeneous 𝒜 s 0 := by
  rw [schemeModuleTensorMap_eq_sheafification]
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  have hpair :
      adj.homEquiv
        (PresheafOfModules.Monoidal.tensorObj
          (positiveSheafOfModules 𝒜 6).val (sheafOfModules 𝒜 6).val)
        (sheafOfModules 𝒜 0) (positiveNegativePairing 𝒜 6) =
      positiveNegativePairingPresheaf 𝒜 6 := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  have hdiff :
      adj.homEquiv
        (PresheafOfModules.Monoidal.tensorObj
          (positiveSheafOfModules 𝒜 2).val (sheafOfModules 𝒜 6).val)
        (sheafOfModules 𝒜 4)
        (positiveNegativeDifferencePairing 𝒜 2 6 (by omega)) =
      positiveNegativeDifferencePairingPresheaf 𝒜 2 6 (by omega) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  rw [hpair]
  erw [adj.homEquiv_naturality_right]
  rw [hdiff]
  exact positiveNegativeDifferencePairingPresheaf_two_six_mul_naturality 𝒜 s

theorem positiveNegativePositiveDifferencePairing_two_two_factorization :
    positiveNegativePositiveDifferencePairing 𝒜 2 2 (by omega) ≫
      positiveZeroToZeroTwist 𝒜 =
    positiveNegativePairing 𝒜 2 := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_right]
  have hdiff : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 2).val
        (sheafOfModules 𝒜 2).val) (positiveSheafOfModules 𝒜 0)
      (positiveNegativePositiveDifferencePairing 𝒜 2 2 (by omega)) =
      positiveNegativePositiveDifferencePairingPresheaf 𝒜 2 2 (by omega) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  rw [hdiff]
  have hpair : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 2).val
        (sheafOfModules 𝒜 2).val) (sheafOfModules 𝒜 0)
      (positiveNegativePairing 𝒜 2) =
      positiveNegativePairingPresheaf 𝒜 2 := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  rw [hpair]
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  apply Subtype.ext
  funext x
  rfl


end PfaffianDescent.ProjectiveNegativeTwist
