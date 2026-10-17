import AllCharacteristics.ProjectiveConfigurationIncidencePullback
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # The finite étale subscheme over unordered configurations

The original incidence is finite étale of rank exactly n. Étaleness descends through the proved Cartesian configuration cover. The finite surjective marked source proves universal closedness and finite fibers; separatedness and Zariski's Main Theorem give finiteness. Rank is computed on the original ordered cover.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S] (f : Proj 𝒜 ⟶ S) (n : ℕ)

instance etale_projectiveConfigurationIncidenceToBase : Etale (projectiveConfigurationIncidenceToBase 𝒜 f n) := by
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale.{u})
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (isPullback_projectiveConfigurationIncidenceToBase 𝒜 f n).flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ (etale_constantCoverToBase _ _)

lemma projectiveConfigurationMarkedToIncidence_toBase :
    projectiveConfigurationMarkedToIncidence 𝒜 f n ≫ projectiveConfigurationIncidenceToBase 𝒜 f n =
      constantCoverToBase (ULift.{u} (Fin n)) (orderedFamilyConfigurationOver f n).left ≫
        projectiveConfigurationQuotientMap 𝒜 f n :=
  (isPullback_projectiveConfigurationIncidenceToBase 𝒜 f n).w

instance universallyClosed_projectiveConfigurationIncidenceToBase :
    UniversallyClosed (projectiveConfigurationIncidenceToBase 𝒜 f n) := by
  have : UniversallyClosed (projectiveConfigurationMarkedToIncidence 𝒜 f n ≫
      projectiveConfigurationIncidenceToBase 𝒜 f n) := by
    rw [projectiveConfigurationMarkedToIncidence_toBase]
    let c : orderedConfigurationMarkedSource f n ⟶ (orderedFamilyConfigurationOver f n).left :=
      constantCoverToBase (ULift.{u} (Fin n)) (orderedFamilyConfigurationOver f n).left
    have : IsFinite c := isFinite_constantCoverToBase _ _
    change UniversallyClosed (c ≫ projectiveConfigurationQuotientMap 𝒜 f n)
    infer_instance
  exact UniversallyClosed.of_comp_surjective (projectiveConfigurationMarkedToIncidence 𝒜 f n)
    (projectiveConfigurationIncidenceToBase 𝒜 f n)

instance isSeparated_projectiveConfigurationIncidenceToBase :
    IsSeparated (projectiveConfigurationIncidenceToBase 𝒜 f n) := by
  let i : projectiveConfigurationIncidence 𝒜 f n ⟶
      pullback f (projectiveConfigurationQuotientToBase 𝒜 f n) := projectiveConfigurationIncidenceι 𝒜 f n
  have : IsClosedImmersion i := isClosedImmersion_projectiveConfigurationIncidenceι 𝒜 f n
  have : IsSeparated f := inferInstance
  change IsSeparated (i ≫ pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
  infer_instance

instance isProper_projectiveConfigurationIncidenceToBase :
    IsProper (projectiveConfigurationIncidenceToBase 𝒜 f n) where

instance isFinite_projectiveConfigurationIncidenceToBase :
    IsFinite (projectiveConfigurationIncidenceToBase 𝒜 f n) := by
  let r := projectiveConfigurationMarkedToIncidence 𝒜 f n
  let p := projectiveConfigurationIncidenceToBase 𝒜 f n
  have : IsFinite (r ≫ p) := by
    change IsFinite (projectiveConfigurationMarkedToIncidence 𝒜 f n ≫ projectiveConfigurationIncidenceToBase 𝒜 f n)
    rw [projectiveConfigurationMarkedToIncidence_toBase]
    let c : orderedConfigurationMarkedSource f n ⟶ (orderedFamilyConfigurationOver f n).left :=
      constantCoverToBase (ULift.{u} (Fin n)) (orderedFamilyConfigurationOver f n).left
    have : IsFinite c := isFinite_constantCoverToBase _ _
    change IsFinite (c ≫ projectiveConfigurationQuotientMap 𝒜 f n)
    infer_instance
  have : LocallyQuasiFinite p := LocallyQuasiFinite.of_finite_preimage_singleton p fun x => by
    have he : p ⁻¹' {x} = r '' ((r ≫ p) ⁻¹' {x}) := by
      ext y
      constructor
      · intro hy
        obtain ⟨z, rfl⟩ := r.surjective y
        exact ⟨z, hy, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact hz
    rw [he]
    exact ((r ≫ p).finite_preimage_singleton x).image r
  exact IsFinite.of_isProper_of_locallyQuasiFinite p

lemma finrank_projectiveConfigurationIncidenceToBase
    (x : (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) :
    (projectiveConfigurationIncidenceToBase 𝒜 f n).finrank x = n := by
  obtain ⟨y, rfl⟩ := (projectiveConfigurationQuotientMap 𝒜 f n).surjective x
  have h := Scheme.Hom.finrank_of_isPullback _ _ _ _
    (isPullback_projectiveConfigurationIncidenceToBase 𝒜 f n) y
  exact h.symm.trans ((finrank_constantCoverToBase (ULift.{u} (Fin n))
    (orderedFamilyConfigurationOver f n).left y).trans (by simp))

noncomputable def projectiveConfigurationFiniteSubscheme :
    FiniteSubschemeDatum (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n)) n :=
  ⟨projectiveConfigurationIncidenceIdeal 𝒜 f n,
    isFinite_projectiveConfigurationIncidenceToBase 𝒜 f n,
    inferInstanceAs (Flat (projectiveConfigurationIncidenceToBase 𝒜 f n)),
    inferInstanceAs (LocallyOfFinitePresentation (projectiveConfigurationIncidenceToBase 𝒜 f n)),
    finrank_projectiveConfigurationIncidenceToBase 𝒜 f n⟩

lemma projectiveConfigurationFiniteSubscheme_ideal :
    (projectiveConfigurationFiniteSubscheme 𝒜 f n).val = projectiveConfigurationIncidenceIdeal 𝒜 f n := rfl

/-- Pulling back the actual unordered finite subscheme recovers the original ordered datum. -/
lemma projectiveConfigurationFiniteSubscheme_baseChange :
    FiniteSubschemeDatum.baseChange (projectiveConfigurationFamilyMap 𝒜 f n)
      (projectiveConfigurationQuotientMap 𝒜 f n) (isPullback_projectiveConfigurationFamilyMap 𝒜 f n)
      (projectiveConfigurationFiniteSubscheme 𝒜 f n) = orderedConfigurationFiniteSubscheme f n :=
  Subtype.ext (projectiveConfigurationIncidenceIdeal_comap 𝒜 f n)

end AllCharacteristics
