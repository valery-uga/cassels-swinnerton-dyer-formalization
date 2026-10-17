import AllCharacteristics.CubicQuarticSubschemeSection
import AllCharacteristics.FlatStalkCharacteristic
import AllCharacteristics.UniversalQuartetSubscheme

/-! # Rational section from the universal quartet subscheme

The universal smooth distinct-quartet family carries an actual finite flat
rank-four subscheme.  The generic-fiber lifting theorem therefore supplies a
rational section as soon as the quartet base is known to be integral with
characteristic-zero function field.  The integrality statement is kept
explicit here; it is the remaining geometric identification of the universal
parameter component, rather than an implicit assumption in the section proof.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
namespace UniversalHomogeneous
universe u

variable (R : Type u) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R]

/-- The actual smooth universal cubic over the distinct-quartet base has a
generic rational section supplied by its finite rank-four subscheme. -/
theorem exists_rational_section_cubicOverSmoothDistinctQuartets
    [IsIntegral (smoothDistinctCubicQuartetBase R)] :
    ∃ s : (smoothDistinctCubicQuartetBase R).RationalMap
        (cubicOverSmoothDistinctQuartets R),
      s.compHom (cubicOverSmoothDistinctQuartetsToBase R) =
        Scheme.Hom.toRationalMap (𝟙 (smoothDistinctCubicQuartetBase R)) := by
  letI : Flat (smoothDistinctCubicQuartetToBaseRing R) := inferInstance
  letI : CharZero (smoothDistinctCubicQuartetBase R).functionField :=
    charZero_functionField_of_flat_over_domain R
      (smoothDistinctCubicQuartetToBaseRing R)
  exact exists_rational_section_cubicFamily_of_quarticSubscheme
    (p := form (Fin 4) 3 R) (hp := form_isHomogeneous (Fin 4) 3 R)
    (b := smoothDistinctCubicQuartetToCoefficients R)
    (D := smoothDistinctCubicQuartetFiniteSubscheme R)

end UniversalHomogeneous
end AllCharacteristics
