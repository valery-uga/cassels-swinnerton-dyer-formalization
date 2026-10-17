import AllCharacteristics.ProjectiveConfigurationKernelPair
import AllCharacteristics.OrderedConfigurationMarkedAction
import AllCharacteristics.ProjectiveConfigurationIncidence
import AllCharacteristics.InvariantImage

/-! # Pulling the unordered incidence back to ordered configurations

The actual incidence ideal pulls back to the kernel of the original union immersion. This identifies the marked source with the Cartesian pullback of the incidence, including the embeddings and the configuration structure maps.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S] (f : Proj 𝒜 ⟶ S) (n : ℕ)

lemma projectiveConfigurationFamilyMap_invariant (g : Equiv.Perm (Fin n)) :
    orderedConfigurationFamilyRightAction f n g ≫ projectiveConfigurationFamilyMap 𝒜 f n =
      projectiveConfigurationFamilyMap 𝒜 f n := by
  let C := (orderedFamilyConfigurationOver f n).left
  let a : C ⟶ S := (orderedFamilyConfigurationOver f n).hom
  let b := projectiveConfigurationQuotientToBase 𝒜 f n
  let q := projectiveConfigurationQuotientMap 𝒜 f n
  let r : pullback f a ⟶ pullback f b := projectiveConfigurationFamilyMap 𝒜 f n
  have hr₁ : r ≫ pullback.fst f b = pullback.fst f a := baseChangedFamilyMap_fst _ _ _ _ _
  have hr₂ : r ≫ pullback.snd f b = pullback.snd f a ≫ q := projectiveConfigurationFamilyMap_toBase 𝒜 f n
  change orderedConfigurationFamilyRightAction f n g ≫ r = r
  apply pullback.hom_ext
  · rw [Category.assoc, hr₁]
    exact orderedConfigurationFamilyRightAction_fst f n g
  · rw [Category.assoc, hr₂, ← Category.assoc]
    rw [show orderedConfigurationFamilyRightAction f n g ≫ pullback.snd f a =
      pullback.snd f a ≫ configurationRightAction f n g from orderedConfigurationFamilyRightAction_snd f n g]
    rw [Category.assoc, projectiveConfigurationQuotientMap_invariant]

instance isIso_projectiveConfigurationFamilyKernelPairMap :
    IsIso (schemeActionKernelPairMap (Equiv.Perm (Fin n)) (orderedConfigurationFamilyRightAction f n)
      (projectiveConfigurationFamilyMap 𝒜 f n) (projectiveConfigurationFamilyMap_invariant 𝒜 f n)) := by
  have h := isPullback_schemeActionKernelPairMap_baseChange (Equiv.Perm (Fin n))
    (orderedConfigurationFamilyRightAction f n) (configurationRightAction f n)
    (isPullback_projectiveConfigurationFamilyMap 𝒜 f n).flip
    (projectiveConfigurationFamilyMap_invariant 𝒜 f n) (projectiveConfigurationQuotientMap_invariant 𝒜 f n)
    (orderedConfigurationFamilyRightAction_snd f n)
  exact h.isIso_snd_of_isIso

lemma projectiveConfigurationIncidenceIdeal_comap :
    (projectiveConfigurationIncidenceIdeal 𝒜 f n).comap (projectiveConfigurationFamilyMap 𝒜 f n) =
      (orderedConfigurationUnionMap f n).ker :=
  kernel_comp_comap_of_actionKernelPair (Equiv.Perm (Fin n))
    (orderedConfigurationFamilyRightAction f n) (projectiveConfigurationFamilyMap 𝒜 f n)
    (projectiveConfigurationFamilyMap_invariant 𝒜 f n) (orderedConfigurationUnionMap f n)
    (orderedConfigurationMarkedRightAction f n) (orderedConfigurationMarkedRightAction_union f n)
    1 (orderedConfigurationMarkedRightAction_one f n)

lemma isPullback_projectiveConfigurationIncidence :
    IsPullback (orderedConfigurationUnionMap f n) (projectiveConfigurationMarkedToIncidence 𝒜 f n)
      (projectiveConfigurationFamilyMap 𝒜 f n) (projectiveConfigurationIncidenceι 𝒜 f n) := by
  apply isPullback_of_isClosedImmersion
  · exact (projectiveConfigurationMarkedToIncidence_ι 𝒜 f n).symm
  · change (projectiveConfigurationIncidenceIdeal 𝒜 f n).subschemeι.ker.comap
      (projectiveConfigurationFamilyMap 𝒜 f n) = _
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact projectiveConfigurationIncidenceIdeal_comap 𝒜 f n

lemma isPullback_projectiveConfigurationIncidenceToBase :
    IsPullback (projectiveConfigurationMarkedToIncidence 𝒜 f n)
      (constantCoverToBase (ULift.{u} (Fin n)) (orderedFamilyConfigurationOver f n).left)
      (projectiveConfigurationIncidenceToBase 𝒜 f n) (projectiveConfigurationQuotientMap 𝒜 f n) := by
  have h := (isPullback_projectiveConfigurationIncidence 𝒜 f n).flip.paste_vert
    (isPullback_projectiveConfigurationFamilyMap 𝒜 f n)
  rw [orderedConfigurationUnionMap_toBase] at h
  exact h

/-- Pulling the unordered incidence family back along any ordered
configuration point splits it as the constant cover by its labels.  This is
the explicit scheme-level bridge from an ordered lift to the split finite
configuration over the lift's coefficient ring. -/
noncomputable def projectiveConfigurationIncidenceFiberIsoConstantCover
    {R : Type u} [CommRing R]
    (r : Spec (.of R) ⟶ (orderedFamilyConfigurationOver f n).left) :
    (∐ fun _ : ULift.{u} (Fin n) ↦ Spec (.of R)) ≅
      pullback (projectiveConfigurationIncidenceToBase 𝒜 f n)
        (r ≫ projectiveConfigurationQuotientMap 𝒜 f n) :=
  ((isPullback_constantCoverToBase (ULift.{u} (Fin n)) r).paste_horiz
    (isPullback_projectiveConfigurationIncidenceToBase 𝒜 f n)).isoPullback

/-- Under the splitting isomorphism, the map to the incidence scheme is the
base-changed marked-point map. -/
@[reassoc]
lemma projectiveConfigurationIncidenceFiberIsoConstantCover_hom_fst
    {R : Type u} [CommRing R]
    (r : Spec (.of R) ⟶ (orderedFamilyConfigurationOver f n).left) :
    (projectiveConfigurationIncidenceFiberIsoConstantCover 𝒜 f n r).hom ≫
        pullback.fst (projectiveConfigurationIncidenceToBase 𝒜 f n)
          (r ≫ projectiveConfigurationQuotientMap 𝒜 f n) =
      CategoryTheory.Limits.Sigma.map
          (f := fun _ : ULift.{u} (Fin n) ↦ Spec (.of R))
          (g := fun _ : ULift.{u} (Fin n) ↦
            (orderedFamilyConfigurationOver f n).left)
          (fun _ ↦ r) ≫
        projectiveConfigurationMarkedToIncidence 𝒜 f n := by
  exact
    ((isPullback_constantCoverToBase (ULift.{u} (Fin n)) r).paste_horiz
      (isPullback_projectiveConfigurationIncidenceToBase 𝒜 f n)).isoPullback_hom_fst

/-- On a specified label, the splitting isomorphism maps to the corresponding
marked incidence point. -/
@[reassoc]
lemma projectiveConfigurationIncidenceFiberIsoConstantCover_component_fst
    {R : Type u} [CommRing R]
    (r : Spec (.of R) ⟶ (orderedFamilyConfigurationOver f n).left)
    (i : Fin n) :
    Sigma.ι (fun _ : ULift.{u} (Fin n) ↦ Spec (.of R)) (ULift.up i) ≫
        (projectiveConfigurationIncidenceFiberIsoConstantCover 𝒜 f n r).hom ≫
        pullback.fst (projectiveConfigurationIncidenceToBase 𝒜 f n)
          (r ≫ projectiveConfigurationQuotientMap 𝒜 f n) =
      r ≫ Sigma.ι (fun _ : ULift.{u} (Fin n) ↦
        (orderedFamilyConfigurationOver f n).left) (ULift.up i) ≫
        projectiveConfigurationMarkedToIncidence 𝒜 f n := by
  let sR := Sigma.ι (fun _ : ULift.{u} (Fin n) ↦ Spec (.of R)) (ULift.up i)
  let sO := Sigma.ι (fun _ : ULift.{u} (Fin n) ↦
    (orderedFamilyConfigurationOver f n).left) (ULift.up i)
  let m := CategoryTheory.Limits.Sigma.map
    (f := fun _ : ULift.{u} (Fin n) ↦ Spec (.of R))
    (g := fun _ : ULift.{u} (Fin n) ↦
      (orderedFamilyConfigurationOver f n).left) (fun _ ↦ r)
  let j := projectiveConfigurationMarkedToIncidence 𝒜 f n
  have hs : sR ≫ m = r ≫ sO := Sigma.ι_map (fun _ ↦ r) (ULift.up i)
  calc
    sR ≫ (projectiveConfigurationIncidenceFiberIsoConstantCover 𝒜 f n r).hom ≫
        pullback.fst (projectiveConfigurationIncidenceToBase 𝒜 f n)
          (r ≫ projectiveConfigurationQuotientMap 𝒜 f n) =
      sR ≫ (m ≫ j) := congrArg (sR ≫ ·)
        (projectiveConfigurationIncidenceFiberIsoConstantCover_hom_fst 𝒜 f n r)
    _ = (sR ≫ m) ≫ j := (Category.assoc _ _ _).symm
    _ = (r ≫ sO) ≫ j := congrArg (· ≫ j) hs
    _ = r ≫ sO ≫ j := Category.assoc _ _ _

/-- Under the splitting isomorphism, the structure map is the constant cover
of the coefficient spectrum. -/
@[reassoc]
lemma projectiveConfigurationIncidenceFiberIsoConstantCover_hom_snd
    {R : Type u} [CommRing R]
    (r : Spec (.of R) ⟶ (orderedFamilyConfigurationOver f n).left) :
    (projectiveConfigurationIncidenceFiberIsoConstantCover 𝒜 f n r).hom ≫
        pullback.snd (projectiveConfigurationIncidenceToBase 𝒜 f n)
          (r ≫ projectiveConfigurationQuotientMap 𝒜 f n) =
      constantCoverToBase (ULift.{u} (Fin n)) (Spec (.of R)) := by
  exact
    ((isPullback_constantCoverToBase (ULift.{u} (Fin n)) r).paste_horiz
      (isPullback_projectiveConfigurationIncidenceToBase 𝒜 f n)).isoPullback_hom_snd

end AllCharacteristics
