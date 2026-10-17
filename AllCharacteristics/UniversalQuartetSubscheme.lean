import AllCharacteristics.ProjectiveConfigurationIncidenceFiniteEtale
import AllCharacteristics.UniversalSmoothDistinctQuartets

/-! # The actual universal quartet subscheme

The original universal cubic over its unordered distinct-quartet base carries a finite flat subscheme of rank four over every coefficient ring. Its restriction to the actual smooth nonzero coefficient locus is constructed by the proved Cartesian family map and retains its pullback ideal.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
namespace UniversalHomogeneous
universe u
variable (R : Type u) [CommRing R]

noncomputable def cubicOverDistinctQuartets : Scheme.{u} :=
  pullback (familyToCoefficients R (Fin 4) 3) (cubicDistinctQuartetToCoefficients R)

noncomputable def cubicOverDistinctQuartetsToBase : cubicOverDistinctQuartets R ⟶ (cubicDistinctQuartetOpen R).toScheme :=
  pullback.snd (familyToCoefficients R (Fin 4) 3) (cubicDistinctQuartetToCoefficients R)

noncomputable def cubicDistinctQuartetFiniteSubscheme : FiniteSubschemeDatum (cubicOverDistinctQuartetsToBase R) 4 :=
  projectiveConfigurationFiniteSubscheme
    (HomogeneousProjective.grading (HomogeneousProjective.equationIdeal
      (form (Fin 4) 3 R) (form_isHomogeneous (Fin 4) 3 R)))
    (HomogeneousProjective.toBase (HomogeneousProjective.equationIdeal
      (form (Fin 4) 3 R) (form_isHomogeneous (Fin 4) 3 R))) 4

variable [IsNoetherianRing R]

noncomputable def cubicSmoothDistinctQuartetFamilyMap : cubicOverSmoothDistinctQuartets R ⟶ cubicOverDistinctQuartets R :=
  baseChangedFamilyMap (familyToCoefficients R (Fin 4) 3)
    (smoothDistinctCubicQuartetToCoefficients R) (cubicDistinctQuartetToCoefficients R)
    (smoothDistinctCubicQuartetToDistinctQuartets R) (isPullback_smoothDistinctCubicQuartetBase R).w

lemma isPullback_cubicSmoothDistinctQuartetFamilyMap :
    IsPullback (cubicSmoothDistinctQuartetFamilyMap R) (cubicOverSmoothDistinctQuartetsToBase R)
      (cubicOverDistinctQuartetsToBase R) (smoothDistinctCubicQuartetToDistinctQuartets R) :=
  isPullback_baseChangedFamilyMap _ _ _ _ _

noncomputable def smoothDistinctCubicQuartetFiniteSubscheme :
    FiniteSubschemeDatum (cubicOverSmoothDistinctQuartetsToBase R) 4 :=
  FiniteSubschemeDatum.baseChange (cubicSmoothDistinctQuartetFamilyMap R)
    (smoothDistinctCubicQuartetToDistinctQuartets R) (isPullback_cubicSmoothDistinctQuartetFamilyMap R)
    (cubicDistinctQuartetFiniteSubscheme R)

lemma smoothDistinctCubicQuartetFiniteSubscheme_ideal :
    (smoothDistinctCubicQuartetFiniteSubscheme R).val =
      (cubicDistinctQuartetFiniteSubscheme R).val.comap (cubicSmoothDistinctQuartetFamilyMap R) := rfl

end UniversalHomogeneous
end AllCharacteristics
