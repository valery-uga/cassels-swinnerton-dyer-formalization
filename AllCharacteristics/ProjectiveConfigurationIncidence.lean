import AllCharacteristics.BaseChangedFamilyMap
import AllCharacteristics.OrderedConfigurationSubscheme
import AllCharacteristics.ProjectiveConfigurationFiniteEtale
import AllCharacteristics.ProjectiveConfigurationQuotientAction

/-! # The incidence image over unordered projective configurations

The actual marked ordered configuration maps finitely into the family over
the unordered quotient. Its scheme-theoretic image defines a closed incidence
subscheme, and the marked source maps finitely and surjectively to that image.
The source is finite étale over the unordered base. Flatness and rank of the
image over that base are separate statements not assumed in this construction.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S] (f : Proj 𝒜 ⟶ S) (n : ℕ)

/-- The original projective family pulled back to its unordered distinct configurations. -/
noncomputable def projectiveConfigurationFamily : Scheme.{u} :=
  pullback f (projectiveConfigurationQuotientToBase 𝒜 f n)

/-- The actual map of families induced by the ordered-to-unordered quotient. -/
noncomputable def projectiveConfigurationFamilyMap :
    pullback f (orderedFamilyConfigurationOver f n).hom ⟶ projectiveConfigurationFamily 𝒜 f n :=
  baseChangedFamilyMap f (orderedFamilyConfigurationOver f n).hom
    (projectiveConfigurationQuotientToBase 𝒜 f n) (projectiveConfigurationQuotientMap 𝒜 f n)
    (projectiveConfigurationQuotientMap_toBase 𝒜 f n)

/-- The induced family map retains the original quotient on configuration bases. -/
lemma projectiveConfigurationFamilyMap_toBase :
    projectiveConfigurationFamilyMap 𝒜 f n ≫
      pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n) =
        pullback.snd f (orderedFamilyConfigurationOver f n).hom ≫
          projectiveConfigurationQuotientMap 𝒜 f n :=
  baseChangedFamilyMap_snd _ _ _ _ _

/-- The induced map of families is the actual base change of the quotient cover. -/
lemma isPullback_projectiveConfigurationFamilyMap :
    IsPullback (projectiveConfigurationFamilyMap 𝒜 f n)
      (pullback.snd f (orderedFamilyConfigurationOver f n).hom)
      (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
      (projectiveConfigurationQuotientMap 𝒜 f n) :=
  isPullback_baseChangedFamilyMap _ _ _ _ _

/-- The ordered-to-unordered map of families is finite. -/
instance isFinite_projectiveConfigurationFamilyMap : IsFinite (projectiveConfigurationFamilyMap 𝒜 f n) :=
  isFinite_baseChangedFamilyMap _ _ _ _ _

/-- The ordered-to-unordered map of families is étale in every characteristic. -/
instance etale_projectiveConfigurationFamilyMap : Etale (projectiveConfigurationFamilyMap 𝒜 f n) :=
  etale_baseChangedFamilyMap _ _ _ _ _

/-- The ordered-to-unordered map of families is surjective. -/
instance surjective_projectiveConfigurationFamilyMap : Surjective (projectiveConfigurationFamilyMap 𝒜 f n) :=
  surjective_baseChangedFamilyMap _ _ _ _ _

/-- Marked ordered configurations map to the family over their actual unordered quotient. -/
noncomputable def projectiveConfigurationMarkedMap :
    orderedConfigurationMarkedSource f n ⟶ projectiveConfigurationFamily 𝒜 f n :=
  orderedConfigurationUnionMap f n ≫ projectiveConfigurationFamilyMap 𝒜 f n

/-- The marked structure map is the original constant cover followed by the quotient. -/
lemma projectiveConfigurationMarkedMap_toBase :
    projectiveConfigurationMarkedMap 𝒜 f n ≫
      pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n) =
        constantCoverToBase (ULift.{u} (Fin n)) (orderedFamilyConfigurationOver f n).left ≫
          projectiveConfigurationQuotientMap 𝒜 f n := by
  let r : pullback f (orderedFamilyConfigurationOver f n).hom ⟶
      pullback f (projectiveConfigurationQuotientToBase 𝒜 f n) := projectiveConfigurationFamilyMap 𝒜 f n
  have hr : r ≫ pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n) =
      pullback.snd f (orderedFamilyConfigurationOver f n).hom ≫
        projectiveConfigurationQuotientMap 𝒜 f n := projectiveConfigurationFamilyMap_toBase 𝒜 f n
  change (orderedConfigurationUnionMap f n ≫ r) ≫
    pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n) = _
  rw [Category.assoc, hr, ← Category.assoc, orderedConfigurationUnionMap_toBase]
  rfl

/-- The marked incidence morphism into the unordered family is finite. -/
instance isFinite_projectiveConfigurationMarkedMap : IsFinite (projectiveConfigurationMarkedMap 𝒜 f n) := by
  change IsFinite (orderedConfigurationUnionMap f n ≫ projectiveConfigurationFamilyMap 𝒜 f n)
  infer_instance

/-- Marked configurations are finite over the unordered configuration base. -/
instance isFinite_projectiveConfigurationMarkedToBase :
    IsFinite (projectiveConfigurationMarkedMap 𝒜 f n ≫
      pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n)) := by
  let c : orderedConfigurationMarkedSource f n ⟶ (orderedFamilyConfigurationOver f n).left :=
    constantCoverToBase (ULift.{u} (Fin n)) (orderedFamilyConfigurationOver f n).left
  have : IsFinite c := isFinite_constantCoverToBase _ _
  rw [projectiveConfigurationMarkedMap_toBase]
  change IsFinite (c ≫ projectiveConfigurationQuotientMap 𝒜 f n)
  infer_instance

/-- Marked configurations are étale over the unordered configuration base. -/
instance etale_projectiveConfigurationMarkedToBase :
    Etale (projectiveConfigurationMarkedMap 𝒜 f n ≫
      pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n)) := by
  let c : orderedConfigurationMarkedSource f n ⟶ (orderedFamilyConfigurationOver f n).left :=
    constantCoverToBase (ULift.{u} (Fin n)) (orderedFamilyConfigurationOver f n).left
  have : Etale c := etale_constantCoverToBase _ _
  rw [projectiveConfigurationMarkedMap_toBase]
  change Etale (c ≫ projectiveConfigurationQuotientMap 𝒜 f n)
  exact Etale.etale_comp c (projectiveConfigurationQuotientMap 𝒜 f n)

/-- The actual kernel ideal defining the image of the marked incidence morphism. -/
noncomputable def projectiveConfigurationIncidenceIdeal :
    (projectiveConfigurationFamily 𝒜 f n).IdealSheafData := (projectiveConfigurationMarkedMap 𝒜 f n).ker

/-- The actual scheme-theoretic incidence image in the unordered family. -/
noncomputable def projectiveConfigurationIncidence : Scheme.{u} :=
  (projectiveConfigurationIncidenceIdeal 𝒜 f n).subscheme

/-- The incidence image retains its closed embedding in the unordered family. -/
noncomputable def projectiveConfigurationIncidenceι :
    projectiveConfigurationIncidence 𝒜 f n ⟶ projectiveConfigurationFamily 𝒜 f n :=
  (projectiveConfigurationIncidenceIdeal 𝒜 f n).subschemeι

/-- The incidence embedding is an actual closed immersion. -/
instance isClosedImmersion_projectiveConfigurationIncidenceι :
    IsClosedImmersion (projectiveConfigurationIncidenceι 𝒜 f n) :=
  inferInstanceAs (IsClosedImmersion (projectiveConfigurationIncidenceIdeal 𝒜 f n).subschemeι)

/-- The incidence image retains its structure map to unordered configurations. -/
noncomputable def projectiveConfigurationIncidenceToBase :
    projectiveConfigurationIncidence 𝒜 f n ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme :=
  projectiveConfigurationIncidenceι 𝒜 f n ≫
    pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n)

/-- The original marked configurations map to their actual scheme-theoretic image. -/
noncomputable def projectiveConfigurationMarkedToIncidence :
    orderedConfigurationMarkedSource f n ⟶ projectiveConfigurationIncidence 𝒜 f n :=
  (projectiveConfigurationMarkedMap 𝒜 f n).toImage

/-- The factorization through the image recovers the original incidence morphism. -/
lemma projectiveConfigurationMarkedToIncidence_ι :
    projectiveConfigurationMarkedToIncidence 𝒜 f n ≫ projectiveConfigurationIncidenceι 𝒜 f n =
      projectiveConfigurationMarkedMap 𝒜 f n :=
  (projectiveConfigurationMarkedMap 𝒜 f n).toImage_imageι

/-- The marked source maps finitely to the incidence image. -/
instance isFinite_projectiveConfigurationMarkedToIncidence :
    IsFinite (projectiveConfigurationMarkedToIncidence 𝒜 f n) := by
  have : IsFinite (projectiveConfigurationMarkedToIncidence 𝒜 f n ≫
      projectiveConfigurationIncidenceι 𝒜 f n) := by
    rw [projectiveConfigurationMarkedToIncidence_ι]
    infer_instance
  exact IsFinite.of_comp _ (projectiveConfigurationIncidenceι 𝒜 f n)

/-- Every point of the incidence image has a marked point above it. -/
instance surjective_projectiveConfigurationMarkedToIncidence :
    Surjective (projectiveConfigurationMarkedToIncidence 𝒜 f n) := by
  have : IsDominant (projectiveConfigurationMarkedToIncidence 𝒜 f n) :=
    inferInstanceAs (IsDominant (projectiveConfigurationMarkedMap 𝒜 f n).toImage)
  infer_instance

end AllCharacteristics
