import AllCharacteristics.AffineEtaleSourceSmooth
import AllCharacteristics.SourceOpenNeighborhoodCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Descent of smoothness along affine étale covers

A locally finitely presented morphism with smooth composite along an affine,
surjective étale cover is smooth. The proof reduces on actual affine opens
to faithful flat descent of the cotangent criterion.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u

/-- Smoothness descends along an affine surjective étale source cover when
the target is affine. -/
lemma smooth_of_surjective_etale_affine_source_over_affine
    {X Y Z : Scheme.{u}} [IsAffine Z]
    (q : X ⟶ Y) [IsAffineHom q] [Etale q] [Surjective q]
    (p : Y ⟶ Z) [LocallyOfFinitePresentation p] [Smooth (q ≫ p)] : Smooth p := by
  let : IsZariskiLocalAtSource (@Smooth : MorphismProperty Scheme.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _
      (inferInstance : HasRingHomProperty @Smooth.{u} RingHom.Smooth)
  apply property_of_source_open_neighborhoods (@Smooth : MorphismProperty Scheme.{u})
  intro y
  obtain ⟨i, z, rfl⟩ := Y.affineCover.exists_eq y
  let j := Y.affineCover.f i
  let r := pullback.snd q j
  have : Smooth (r ≫ (j ≫ p)) := by
    change Smooth (pullback.snd q j ≫ j ≫ p)
    rw [← pullback.condition_assoc]
    infer_instance
  exact ⟨Y.affineCover.X i, j, inferInstance, ⟨z, rfl⟩,
    smooth_of_surjective_etale_between_affines r (j ≫ p)⟩

/-- Smoothness descends along an affine surjective étale source cover over
an arbitrary target scheme. -/
theorem smooth_of_surjective_etale_affine_source
    {X Y Z : Scheme.{u}}
    (q : X ⟶ Y) [IsAffineHom q] [Etale q] [Surjective q]
    (p : Y ⟶ Z) [LocallyOfFinitePresentation p] [Smooth (q ≫ p)] : Smooth p := by
  let : IsZariskiLocalAtTarget (@Smooth : MorphismProperty Scheme.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtTarget _ _
      (inferInstance : HasRingHomProperty @Smooth.{u} RingHom.Smooth)
  let : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtTarget _ _
      (inferInstance : HasRingHomProperty @LocallyOfFinitePresentation.{u} RingHom.FinitePresentation)
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Smooth.{u})
    (fun U : Z.affineOpens => U.1) (iSup_affineOpens_eq_top Z)]
  intro U
  have : IsAffine U.1.toScheme := U.2
  have : Smooth ((q ∣_ p ⁻¹ᵁ U.1) ≫ (p ∣_ U.1)) := by
    rw [← morphismRestrict_comp]
    exact IsZariskiLocalAtTarget.restrict (P := @Smooth.{u}) inferInstance U.1
  have : IsAffineHom (q ∣_ p ⁻¹ᵁ U.1) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom.{u})
      (isPullback_morphismRestrict q (p ⁻¹ᵁ U.1)).flip inferInstance
  have : Surjective (q ∣_ p ⁻¹ᵁ U.1) :=
    IsZariskiLocalAtTarget.restrict (P := @Surjective.{u}) inferInstance (p ⁻¹ᵁ U.1)
  have : LocallyOfFinitePresentation (p ∣_ U.1) :=
    IsZariskiLocalAtTarget.restrict (P := @LocallyOfFinitePresentation.{u}) inferInstance U.1
  exact smooth_of_surjective_etale_affine_source_over_affine
    (q ∣_ p ⁻¹ᵁ U.1) (p ∣_ U.1)

end AllCharacteristics
