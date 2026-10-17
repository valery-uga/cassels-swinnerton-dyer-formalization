import AllCharacteristics.ProjectiveConfigurationBaseChangeSmooth
import AllCharacteristics.SmoothSchemeRegularity
import AllCharacteristics.UniversalCubicDistinctQuartets
import AllCharacteristics.UniversalNonzeroSmoothLocus

/-! # The universal smooth cubic over its distinct-quartet base

These are pullbacks of the original universal cubic and its actual unordered
distinct-configuration quotient. The quartet base is smooth over the ring
and has regular local rings when that ring is regular. The pulled-back cubic
is proper and smooth. The full symmetric power at collisions is not asserted
to be regular.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
namespace UniversalHomogeneous
universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R]

/-- The original unordered distinct quartets restricted to smooth nonzero cubic equations. -/
noncomputable def smoothDistinctCubicQuartetBase : Scheme.{u} :=
  pullback (cubicDistinctQuartetToCoefficients R) (nonzeroSmoothParameterOpen R (Fin 4) 3).ι

/-- The actual map from smooth distinct quartets to smooth cubic coefficients. -/
noncomputable def smoothDistinctCubicQuartetToSmoothCoefficients :
    smoothDistinctCubicQuartetBase R ⟶ (nonzeroSmoothParameterOpen R (Fin 4) 3).toScheme :=
  pullback.snd (cubicDistinctQuartetToCoefficients R) (nonzeroSmoothParameterOpen R (Fin 4) 3).ι

/-- The restriction map to the original unordered distinct-quartet scheme. -/
noncomputable def smoothDistinctCubicQuartetToDistinctQuartets :
    smoothDistinctCubicQuartetBase R ⟶ (cubicDistinctQuartetOpen R).toScheme :=
  pullback.fst (cubicDistinctQuartetToCoefficients R) (nonzeroSmoothParameterOpen R (Fin 4) 3).ι

/-- The actual original coefficient map of the restricted quartet base. -/
noncomputable def smoothDistinctCubicQuartetToCoefficients :
    smoothDistinctCubicQuartetBase R ⟶ Spec (.of (Coefficients (Fin 4) 3 R)) :=
  smoothDistinctCubicQuartetToSmoothCoefficients R ≫ (nonzeroSmoothParameterOpen R (Fin 4) 3).ι

/-- The structure map of the restricted quartet base to the coefficient ring. -/
noncomputable def smoothDistinctCubicQuartetToBaseRing :
    smoothDistinctCubicQuartetBase R ⟶ Spec (.of R) :=
  smoothDistinctCubicQuartetToCoefficients R ≫ coefficientSchemeToBase R (Fin 4) 3

/-- The smooth distinct-quartet base is the stated actual pullback. -/
lemma isPullback_smoothDistinctCubicQuartetBase :
    IsPullback (smoothDistinctCubicQuartetToDistinctQuartets R)
      (smoothDistinctCubicQuartetToSmoothCoefficients R) (cubicDistinctQuartetToCoefficients R)
      (nonzeroSmoothParameterOpen R (Fin 4) 3).ι :=
  IsPullback.of_hasPullback _ _

/-- Unordered distinct quartets in the universal smooth cubic vary smoothly. -/
instance smooth_smoothDistinctCubicQuartetToSmoothCoefficients :
    Smooth (smoothDistinctCubicQuartetToSmoothCoefficients R) := by
  have hf : Smooth (pullback.snd (familyToCoefficients R (Fin 4) 3)
      (nonzeroSmoothParameterOpen R (Fin 4) 3).ι) := by
    apply smooth_pullback_of_range_subset_properSmoothBase (familyToCoefficients R (Fin 4) 3)
      (nonzeroSmoothParameterOpen R (Fin 4) 3).ι
    rintro _ ⟨x, rfl⟩
    exact x.property.2
  let I := HomogeneousProjective.equationIdeal (form (Fin 4) 3 R) (form_isHomogeneous (Fin 4) 3 R)
  have : Smooth (pullback.snd (show Proj (HomogeneousProjective.grading I) ⟶
      Spec (.of (Coefficients (Fin 4) 3 R)) from HomogeneousProjective.toBase I)
      (nonzeroSmoothParameterOpen R (Fin 4) 3).ι) := hf
  have : LocallyOfFiniteType (show Proj (HomogeneousProjective.grading I) ⟶
      Spec (.of (Coefficients (Fin 4) 3 R)) from HomogeneousProjective.toBase I) :=
    inferInstanceAs (LocallyOfFiniteType (familyToCoefficients R (Fin 4) 3))
  exact smooth_pullback_projectiveConfigurationQuotient
    (HomogeneousProjective.grading I) (HomogeneousProjective.toBase I) 4
    (nonzeroSmoothParameterOpen R (Fin 4) 3).ι

/-- The actual smooth distinct-quartet base is smooth over the ring. -/
instance smooth_smoothDistinctCubicQuartetToBaseRing :
    Smooth (smoothDistinctCubicQuartetToBaseRing R) := by
  have : Smooth ((nonzeroSmoothParameterOpen R (Fin 4) 3).ι ≫ coefficientSchemeToBase R (Fin 4) 3) :=
    smooth_nonzeroSmoothParameterOpen_toBase R (Fin 4) 3
  change Smooth ((smoothDistinctCubicQuartetToSmoothCoefficients R ≫
    (nonzeroSmoothParameterOpen R (Fin 4) 3).ι) ≫ coefficientSchemeToBase R (Fin 4) 3)
  rw [Category.assoc]
  infer_instance

/-- The smooth distinct-quartet base is locally noetherian over a noetherian ring. -/
instance isLocallyNoetherian_smoothDistinctCubicQuartetBase :
    IsLocallyNoetherian (smoothDistinctCubicQuartetBase R) :=
  LocallyOfFiniteType.isLocallyNoetherian (smoothDistinctCubicQuartetToBaseRing R)

/-- Every stalk of the smooth distinct-quartet base is regular over a regular ring. -/
lemma isRegularLocalRing_smoothDistinctCubicQuartet_stalk (hR : IsRegularRing R)
    (x : smoothDistinctCubicQuartetBase R) :
    IsRegularLocalRing ((smoothDistinctCubicQuartetBase R).presheaf.stalk x) := by
  let := hR
  exact isRegularLocalRing_stalk_of_smooth (smoothDistinctCubicQuartetToBaseRing R)
    (isRegularLocalRing_spec_stalk R) x

/-- The universal cubic pulled back to the actual smooth distinct-quartet base. -/
noncomputable def cubicOverSmoothDistinctQuartets : Scheme.{u} :=
  pullback (familyToCoefficients R (Fin 4) 3) (smoothDistinctCubicQuartetToCoefficients R)

/-- The actual cubic family over smooth distinct quartets. -/
noncomputable def cubicOverSmoothDistinctQuartetsToBase :
    cubicOverSmoothDistinctQuartets R ⟶ smoothDistinctCubicQuartetBase R :=
  pullback.snd (familyToCoefficients R (Fin 4) 3) (smoothDistinctCubicQuartetToCoefficients R)

/-- The pullback map to the original universal cubic. -/
noncomputable def cubicOverSmoothDistinctQuartetsToUniversal :
    cubicOverSmoothDistinctQuartets R ⟶ family R (Fin 4) 3 :=
  pullback.fst (familyToCoefficients R (Fin 4) 3) (smoothDistinctCubicQuartetToCoefficients R)

/-- The cubic over smooth distinct quartets retains its actual coefficient pullback square. -/
lemma isPullback_cubicOverSmoothDistinctQuartets :
    IsPullback (cubicOverSmoothDistinctQuartetsToUniversal R) (cubicOverSmoothDistinctQuartetsToBase R)
      (familyToCoefficients R (Fin 4) 3) (smoothDistinctCubicQuartetToCoefficients R) :=
  IsPullback.of_hasPullback _ _

/-- The actual cubic family over smooth distinct quartets is proper. -/
instance isProper_cubicOverSmoothDistinctQuartetsToBase :
    IsProper (cubicOverSmoothDistinctQuartetsToBase R) := by
  change IsProper (pullback.snd (familyToCoefficients R (Fin 4) 3)
    (smoothDistinctCubicQuartetToCoefficients R))
  infer_instance

/-- The actual cubic family over smooth distinct quartets is smooth. -/
instance smooth_cubicOverSmoothDistinctQuartetsToBase :
    Smooth (cubicOverSmoothDistinctQuartetsToBase R) := by
  apply smooth_pullback_of_range_subset_properSmoothBase (familyToCoefficients R (Fin 4) 3)
    (smoothDistinctCubicQuartetToCoefficients R)
  rintro _ ⟨x, rfl⟩
  exact (smoothDistinctCubicQuartetToSmoothCoefficients R x).property.2

end UniversalHomogeneous
end AllCharacteristics
