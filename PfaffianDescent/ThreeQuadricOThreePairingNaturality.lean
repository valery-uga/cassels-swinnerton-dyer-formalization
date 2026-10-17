import PfaffianDescent.ProjectiveMixedTwistPairing
import PfaffianDescent.ProjectivePositiveDifferencePairing
import PfaffianDescent.P3TwistTensorEquivalence

/-! SOURCE ONLY / UNVERIFIED. Actual mixed pairing naturality for the
O(3)-twisted quadric Koszul terms. Proofs compute the genuine presheaf
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

theorem positiveNegativeDifferencePairingPresheaf_three_four_mul_naturality
    (s : 𝒜 1) :
    PresheafOfModules.Monoidal.tensorHom (positiveMulHomogeneous 𝒜 s 3).val
      (𝟙 (modulePresheaf 𝒜 4)) ≫
        positiveNegativePairingPresheaf 𝒜 4 =
      positiveNegativeDifferencePairingPresheaf 𝒜 3 4 (by omega) ≫
        (mulHomogeneous 𝒜 s 0).val := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  apply Subtype.ext
  funext x
  change (algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * p.1 x) * q.1 x =
    algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * (p.1 x * q.1 x)
  ring

theorem positiveNegativeDifferencePairing_three_four_mul_naturality
    (s : 𝒜 1) :
    schemeModuleTensorMap (positiveMulHomogeneous 𝒜 s 3)
      (𝟙 (sheafOfModules 𝒜 4)) ≫ positiveNegativePairing 𝒜 4 =
      positiveNegativeDifferencePairing 𝒜 3 4 (by omega) ≫
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
          (positiveSheafOfModules 𝒜 3).val (sheafOfModules 𝒜 4).val)
        (sheafOfModules 𝒜 1)
        (positiveNegativeDifferencePairing 𝒜 3 4 (by omega)) =
      positiveNegativeDifferencePairingPresheaf 𝒜 3 4 (by omega) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  rw [hpair]
  erw [adj.homEquiv_naturality_right]
  rw [hdiff]
  exact positiveNegativeDifferencePairingPresheaf_three_four_mul_naturality 𝒜 s

theorem positiveNegativeDifferencePairingPresheaf_three_six_mul_naturality
    (s : 𝒜 3) :
    PresheafOfModules.Monoidal.tensorHom (positiveMulHomogeneous 𝒜 s 3).val
      (𝟙 (modulePresheaf 𝒜 6)) ≫
        positiveNegativePairingPresheaf 𝒜 6 =
      positiveNegativeDifferencePairingPresheaf 𝒜 3 6 (by omega) ≫
        (mulHomogeneous 𝒜 s 0).val := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  apply Subtype.ext
  funext x
  change (algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * p.1 x) * q.1 x =
    algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * (p.1 x * q.1 x)
  ring

theorem positiveNegativeDifferencePairing_three_six_mul_naturality
    (s : 𝒜 3) :
    schemeModuleTensorMap (positiveMulHomogeneous 𝒜 s 3)
      (𝟙 (sheafOfModules 𝒜 6)) ≫ positiveNegativePairing 𝒜 6 =
      positiveNegativeDifferencePairing 𝒜 3 6 (by omega) ≫
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
          (positiveSheafOfModules 𝒜 3).val (sheafOfModules 𝒜 6).val)
        (sheafOfModules 𝒜 3)
        (positiveNegativeDifferencePairing 𝒜 3 6 (by omega)) =
      positiveNegativeDifferencePairingPresheaf 𝒜 3 6 (by omega) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  rw [hpair]
  erw [adj.homEquiv_naturality_right]
  rw [hdiff]
  exact positiveNegativeDifferencePairingPresheaf_three_six_mul_naturality 𝒜 s

theorem positiveNegativePositiveDifferencePairing_three_three_factorization :
    positiveNegativePositiveDifferencePairing 𝒜 3 3 (by omega) ≫
      positiveZeroToZeroTwist 𝒜 =
    positiveNegativePairing 𝒜 3 := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_right]
  have hdiff : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 3).val
        (sheafOfModules 𝒜 3).val) (positiveSheafOfModules 𝒜 0)
      (positiveNegativePositiveDifferencePairing 𝒜 3 3 (by omega)) =
      positiveNegativePositiveDifferencePairingPresheaf 𝒜 3 3 (by omega) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  rw [hdiff]
  have hpair : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 3).val
        (sheafOfModules 𝒜 3).val) (sheafOfModules 𝒜 0)
      (positiveNegativePairing 𝒜 3) =
      positiveNegativePairingPresheaf 𝒜 3 := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  rw [hpair]
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  apply Subtype.ext
  funext x
  rfl

theorem positiveNegativePositiveDifferencePairingPresheaf_three_two_mul_naturality
    (s : 𝒜 1) :
    PresheafOfModules.Monoidal.tensorHom
      (𝟙 (positiveModulePresheaf 𝒜 3)) (mulHomogeneous 𝒜 s 2).val ≫
        positiveNegativePositiveDifferencePairingPresheaf 𝒜 3 2 (by omega) =
      positiveNegativePositiveDifferencePairingPresheaf 𝒜 3 3 (by omega) ≫
        (positiveMulHomogeneous 𝒜 s 0).val := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  apply Subtype.ext
  funext x
  change p.1 x * (algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * q.1 x) =
    algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * (p.1 x * q.1 x)
  ring

theorem positiveNegativePositiveDifferencePairing_three_two_mul_naturality
    (s : 𝒜 1) :
    schemeModuleTensorMap (𝟙 (positiveSheafOfModules 𝒜 3))
      (mulHomogeneous 𝒜 s 2) ≫
        positiveNegativePositiveDifferencePairing 𝒜 3 2 (by omega) =
      positiveNegativePositiveDifferencePairing 𝒜 3 3 (by omega) ≫
        positiveMulHomogeneous 𝒜 s 0 := by
  rw [schemeModuleTensorMap_eq_sheafification]
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  have hfour : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 3).val
        (sheafOfModules 𝒜 2).val) (positiveSheafOfModules 𝒜 1)
      (positiveNegativePositiveDifferencePairing 𝒜 3 2 (by omega)) =
      positiveNegativePositiveDifferencePairingPresheaf 𝒜 3 2 (by omega) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  have hfive : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 3).val
        (sheafOfModules 𝒜 3).val) (positiveSheafOfModules 𝒜 0)
      (positiveNegativePositiveDifferencePairing 𝒜 3 3 (by omega)) =
      positiveNegativePositiveDifferencePairingPresheaf 𝒜 3 3 (by omega) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  rw [hfour]
  erw [adj.homEquiv_naturality_right]
  rw [hfive]
  exact positiveNegativePositiveDifferencePairingPresheaf_three_two_mul_naturality 𝒜 s

end PfaffianDescent.ProjectiveNegativeTwist
