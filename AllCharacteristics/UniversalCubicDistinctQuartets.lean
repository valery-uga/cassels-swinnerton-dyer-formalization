import AllCharacteristics.HomogeneousConfigurationQuotient
import AllCharacteristics.UniversalCubicQuartetQuotient

/-!
# The actual finite étale distinct-quartet cover of the universal cubic

This is the quotient of the original distinct-point open in the fourth
relative power of the universal cubic, over its original coefficient scheme.
All characteristics and arbitrary commutative coefficient rings are included.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
namespace UniversalHomogeneous
universe u
variable (R : Type u) [CommRing R]

/-- The actual unordered distinct-quartet open of the universal cubic quotient. -/
noncomputable def cubicDistinctQuartetOpen : (cubicQuartetQuotient R).Opens :=
  HomogeneousProjective.configurationQuotientOpen
    (HomogeneousProjective.equationIdeal (form (Fin 4) 3 R) (form_isHomogeneous (Fin 4) 3 R)) 4

/-- The original ordered distinct quartets map to their actual unordered quotient. -/
noncomputable def cubicDistinctQuartetQuotientMap :
    (orderedFamilyConfigurationOver (familyToCoefficients R (Fin 4) 3) 4).left ⟶
      (cubicDistinctQuartetOpen R).toScheme :=
  HomogeneousProjective.configurationQuotientMap
    (HomogeneousProjective.equationIdeal (form (Fin 4) 3 R) (form_isHomogeneous (Fin 4) 3 R)) 4

/-- The actual coefficient map for the unordered distinct quartets. -/
noncomputable def cubicDistinctQuartetToCoefficients :
    (cubicDistinctQuartetOpen R).toScheme ⟶ Spec (.of (Coefficients (Fin 4) 3 R)) :=
  HomogeneousProjective.configurationQuotientToBase
    (HomogeneousProjective.equationIdeal (form (Fin 4) 3 R) (form_isHomogeneous (Fin 4) 3 R)) 4

/-- The actual distinct-quartet cover retains the universal cubic coefficient map. -/
theorem cubicDistinctQuartetQuotientMap_toCoefficients :
    cubicDistinctQuartetQuotientMap R ≫ cubicDistinctQuartetToCoefficients R =
      (orderedFamilyConfigurationOver (familyToCoefficients R (Fin 4) 3) 4).hom :=
  HomogeneousProjective.configurationQuotientMap_toBase
    (HomogeneousProjective.equationIdeal (form (Fin 4) 3 R) (form_isHomogeneous (Fin 4) 3 R)) 4

/-- The actual universal-cubic distinct-quartet cover is étale in every characteristic. -/
instance etale_cubicDistinctQuartetQuotientMap : Etale (cubicDistinctQuartetQuotientMap R) :=
  HomogeneousProjective.etale_configurationQuotientMap
    (HomogeneousProjective.equationIdeal (form (Fin 4) 3 R) (form_isHomogeneous (Fin 4) 3 R)) 4

/-- The actual universal-cubic distinct-quartet cover is finite. -/
instance isFinite_cubicDistinctQuartetQuotientMap : IsFinite (cubicDistinctQuartetQuotientMap R) :=
  HomogeneousProjective.isFinite_configurationQuotientMap
    (HomogeneousProjective.equationIdeal (form (Fin 4) 3 R) (form_isHomogeneous (Fin 4) 3 R)) 4

/-- The actual universal-cubic distinct-quartet cover is surjective. -/
instance surjective_cubicDistinctQuartetQuotientMap : Surjective (cubicDistinctQuartetQuotientMap R) :=
  HomogeneousProjective.surjective_configurationQuotientMap
    (HomogeneousProjective.equationIdeal (form (Fin 4) 3 R) (form_isHomogeneous (Fin 4) 3 R)) 4

/-- The actual universal-cubic distinct-quartet cover is proper. -/
instance isProper_cubicDistinctQuartetQuotientMap : IsProper (cubicDistinctQuartetQuotientMap R) := by
  infer_instance

end UniversalHomogeneous
end AllCharacteristics
