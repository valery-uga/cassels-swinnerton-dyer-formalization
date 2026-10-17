import AllCharacteristics.ProjectiveConfigurationFactorization
import AllCharacteristics.UniversalCubicDistinctQuartets

/-! # Categorical descent for actual homogeneous configurations and universal cubic quartets -/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u
namespace HomogeneousProjective
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R)) (n : ℕ)

/-- The original ordered homogeneous configurations have the categorical
quotient property for arbitrary target schemes over every coefficient ring. -/
theorem existsUnique_configurationFactor {T : Scheme.{u}}
    (a : (orderedFamilyConfigurationOver (toBase I) n).left ⟶ T)
    (ha : ∀ g : Equiv.Perm (Fin n), configurationRightAction (toBase I) n g ≫ a = a) :
    ∃! b : (configurationQuotientOpen I n).toScheme ⟶ T,
      configurationQuotientMap I n ≫ b = a :=
  existsUnique_projectiveConfigurationFactor (grading I) (toBase I) n a ha

end HomogeneousProjective
namespace UniversalHomogeneous
variable (R : Type u) [CommRing R]

/-- Every invariant morphism from the original ordered distinct universal
cubic quartets factors uniquely through the actual unordered-quartet open. -/
theorem existsUnique_cubicDistinctQuartetFactor {T : Scheme.{u}}
    (a : (orderedFamilyConfigurationOver (familyToCoefficients R (Fin 4) 3) 4).left ⟶ T)
    (ha : ∀ g : Equiv.Perm (Fin 4),
      configurationRightAction (familyToCoefficients R (Fin 4) 3) 4 g ≫ a = a) :
    ∃! b : (cubicDistinctQuartetOpen R).toScheme ⟶ T,
      cubicDistinctQuartetQuotientMap R ≫ b = a :=
  HomogeneousProjective.existsUnique_configurationFactor
    (HomogeneousProjective.equationIdeal (form (Fin 4) 3 R) (form_isHomogeneous (Fin 4) 3 R)) 4 a ha

end UniversalHomogeneous
end AllCharacteristics
