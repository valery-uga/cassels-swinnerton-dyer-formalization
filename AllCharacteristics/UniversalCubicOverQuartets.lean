import AllCharacteristics.UniversalCubicQuartetQuotient
import AllCharacteristics.UniversalNonzeroSmoothLocus

/-!
# The actual smooth universal cubic family over the quartet parameter scheme

The constructed quartet quotient is restricted to the original nonzero
smooth coefficient open. Pulling back the actual universal cubic along
this parameter map gives a proper smooth family, over the integers or any
noetherian coefficient ring. The full quartet base can have collision
singularities. The later regularity argument concerns the distinct-point
open or Hilbert parameter loci, and the Hilbert comparison remains separate.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
namespace UniversalHomogeneous
universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R]

/-- The actual open of quartet parameters whose original cubic is nonzero and smooth. -/
noncomputable def smoothCubicQuartetOpen : (cubicQuartetQuotient R).Opens :=
  (cubicQuartetQuotientToCoefficients R) ⁻¹ᵁ nonzeroSmoothParameterOpen R (Fin 4) 3

/-- The actual quartet parameter scheme over the smooth cubic coefficient open. -/
noncomputable def smoothCubicQuartetBase : Scheme.{u} := (smoothCubicQuartetOpen R).toScheme

/-- The original coefficient map of a smooth cubic with an unordered quartet. -/
noncomputable def smoothCubicQuartetToCoefficients :
    smoothCubicQuartetBase R ⟶ Spec (.of (Coefficients (Fin 4) 3 R)) :=
  (smoothCubicQuartetOpen R).ι ≫ cubicQuartetQuotientToCoefficients R

/-- The actual universal cubic surface pulled back to the smooth quartet parameter scheme. -/
noncomputable def cubicOverSmoothQuartets : Scheme.{u} :=
  pullback (familyToCoefficients R (Fin 4) 3) (smoothCubicQuartetToCoefficients R)

/-- The actual cubic-family projection to its smooth quartet parameters. -/
noncomputable def cubicOverSmoothQuartetsToBase :
    cubicOverSmoothQuartets R ⟶ smoothCubicQuartetBase R :=
  pullback.snd (familyToCoefficients R (Fin 4) 3) (smoothCubicQuartetToCoefficients R)

/-- The original universal-cubic projection retained by the quartet family. -/
noncomputable def cubicOverSmoothQuartetsToUniversal :
    cubicOverSmoothQuartets R ⟶ family R (Fin 4) 3 :=
  pullback.fst (familyToCoefficients R (Fin 4) 3) (smoothCubicQuartetToCoefficients R)

/-- The quartet family is the actual base change of the original universal cubic. -/
theorem isPullback_cubicOverSmoothQuartets :
    IsPullback (cubicOverSmoothQuartetsToUniversal R) (cubicOverSmoothQuartetsToBase R)
      (familyToCoefficients R (Fin 4) 3) (smoothCubicQuartetToCoefficients R) :=
  IsPullback.of_hasPullback _ _

/-- The actual universal cubic family over smooth quartet parameters is proper. -/
instance isProper_cubicOverSmoothQuartetsToBase : IsProper (cubicOverSmoothQuartetsToBase R) := by
  change IsProper (pullback.snd (familyToCoefficients R (Fin 4) 3) (smoothCubicQuartetToCoefficients R))
  infer_instance

/-- The actual universal cubic family over smooth quartet parameters is smooth. -/
instance smooth_cubicOverSmoothQuartetsToBase : Smooth (cubicOverSmoothQuartetsToBase R) := by
  apply smooth_pullback_of_range_subset_properSmoothBase (familyToCoefficients R (Fin 4) 3)
    (smoothCubicQuartetToCoefficients R)
  rintro _ ⟨x, rfl⟩
  exact x.property.2

end UniversalHomogeneous
end AllCharacteristics
