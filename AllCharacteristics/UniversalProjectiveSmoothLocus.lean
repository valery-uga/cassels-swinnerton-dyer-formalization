import AllCharacteristics.UniversalProjectiveFamilyCharts
import AllCharacteristics.ProperSmoothBase
import AllCharacteristics.RegularAffineStalks

/-!
# The smooth open of projective equation parameters

Over a noetherian coefficient ring, the proper universal projective family has
an open parameter locus over which it is smooth. The restricted family is
proper and smooth. This parameter open has regular local rings when the
coefficient ring is regular.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
namespace UniversalHomogeneous
universe u
variable (R : Type u) [CommRing R] (σ : Type) [Finite σ] (d : ℕ)

/-- The global universal family is locally of finite presentation over a noetherian base. -/
instance locallyOfFinitePresentation_projectiveUniversalToBase [IsNoetherianRing R] :
    LocallyOfFinitePresentation (projectiveUniversalToBase R σ d) := by
  have : IsLocallyNoetherian (projectiveParameters R σ d) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveParametersToBase R σ d)
  infer_instance

/-- The projective parameter open where the entire universal hypersurface is smooth. -/
noncomputable def projectiveSmoothParameterOpen [IsNoetherianRing R] :
    (projectiveParameters R σ d).Opens :=
  properSmoothBase (projectiveUniversalToBase R σ d)

/-- The universal hypersurface over its projective smooth parameter open. -/
noncomputable def projectiveSmoothFamily [IsNoetherianRing R] : Scheme.{u} :=
  ((projectiveUniversalToBase R σ d) ⁻¹ᵁ projectiveSmoothParameterOpen R σ d).toScheme

/-- Its structure morphism to the smooth parameter open. -/
noncomputable def projectiveSmoothFamilyToBase [IsNoetherianRing R] :
    projectiveSmoothFamily R σ d ⟶ (projectiveSmoothParameterOpen R σ d).toScheme :=
  projectiveUniversalToBase R σ d ∣_ projectiveSmoothParameterOpen R σ d

/-- The restricted projective universal family is proper. -/
instance isProper_projectiveSmoothFamilyToBase [IsNoetherianRing R] :
    IsProper (projectiveSmoothFamilyToBase R σ d) :=
  IsZariskiLocalAtTarget.restrict (P := @IsProper.{u})
    (isProper_projectiveUniversalToBase R σ d) (projectiveSmoothParameterOpen R σ d)

/-- The restricted projective universal family is smooth. -/
instance smooth_projectiveSmoothFamilyToBase [IsNoetherianRing R] :
    Smooth (projectiveSmoothFamilyToBase R σ d) :=
  smooth_on_properSmoothBase (projectiveUniversalToBase R σ d)

/-- This is the largest projective parameter open over which the family is smooth. -/
theorem smooth_projectiveUniversal_restrict_iff [IsNoetherianRing R]
    (U : (projectiveParameters R σ d).Opens) :
    Smooth (projectiveUniversalToBase R σ d ∣_ U) ↔ U ≤ projectiveSmoothParameterOpen R σ d :=
  smooth_morphismRestrict_iff_le_properSmoothBase (projectiveUniversalToBase R σ d) U

/-- The projective smooth parameter open is smooth over the coefficient ring. -/
theorem smooth_projectiveSmoothParameter_toBase [IsNoetherianRing R] :
    Smooth ((projectiveSmoothParameterOpen R σ d).ι ≫ projectiveParametersToBase R σ d) := by
  infer_instance

/-- The projective smooth parameter open has regular local rings over a regular base. -/
theorem isRegularLocalRing_projectiveSmoothParameter_stalk [IsRegularRing R]
    (x : (projectiveSmoothParameterOpen R σ d).toScheme) :
    IsRegularLocalRing ((projectiveSmoothParameterOpen R σ d).toScheme.presheaf.stalk x) := by
  have := isRegularLocalRing_projectiveParameters_stalk R σ d
    ((projectiveSmoothParameterOpen R σ d).ι x)
  exact isRegularLocalRing_stalk_of_openImmersion (projectiveSmoothParameterOpen R σ d).ι x

end UniversalHomogeneous
end AllCharacteristics
