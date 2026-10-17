import AllCharacteristics.ProjectiveConfigurationFiniteEtale
import AllCharacteristics.HomogeneousTupleQuotient

/-! # Finite étale configuration quotients for actual homogeneous projective schemes -/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R)) (n : ℕ)

/-- The actual homogeneous projective structure morphism is separated. -/
instance isSeparated_homogeneousToBase : IsSeparated (toBase I) :=
  inferInstanceAs (IsSeparated (show Proj (grading I) ⟶ Spec (.of R) from toBase I))

/-- The actual unordered distinct-configuration open of a homogeneous projective scheme. -/
noncomputable def configurationQuotientOpen : (tupleQuotient I n).Opens :=
  projectiveConfigurationQuotientOpen (grading I) (toBase I) n

/-- The actual finite étale quotient from the original ordered configurations. -/
noncomputable def configurationQuotientMap :
    (orderedFamilyConfigurationOver (toBase I) n).left ⟶ (configurationQuotientOpen I n).toScheme :=
  projectiveConfigurationQuotientMap (grading I) (toBase I) n

/-- The unordered configurations retain the original coefficient map. -/
noncomputable def configurationQuotientToBase :
    (configurationQuotientOpen I n).toScheme ⟶ Spec (.of R) :=
  projectiveConfigurationQuotientToBase (grading I) (toBase I) n

/-- The configuration cover is over the original coefficient ring. -/
theorem configurationQuotientMap_toBase :
    configurationQuotientMap I n ≫ configurationQuotientToBase I n =
      (orderedFamilyConfigurationOver (toBase I) n).hom :=
  projectiveConfigurationQuotientMap_toBase (grading I) (toBase I) n

/-- The actual homogeneous configuration quotient map is étale over every coefficient ring. -/
instance etale_configurationQuotientMap : Etale (configurationQuotientMap I n) :=
  etale_projectiveConfigurationQuotientMap (grading I) (toBase I) n

/-- The actual homogeneous configuration quotient map is finite. -/
instance isFinite_configurationQuotientMap : IsFinite (configurationQuotientMap I n) :=
  isFinite_projectiveConfigurationQuotientMap_of_etale (grading I) (toBase I) n

/-- Every point of the actual homogeneous configuration quotient is covered. -/
instance surjective_configurationQuotientMap : Surjective (configurationQuotientMap I n) :=
  surjective_projectiveConfigurationQuotientMap (grading I) (toBase I) n

/-- The actual homogeneous configuration quotient map is proper. -/
instance isProper_configurationQuotientMap : IsProper (configurationQuotientMap I n) := by
  infer_instance

end HomogeneousProjective
end AllCharacteristics
