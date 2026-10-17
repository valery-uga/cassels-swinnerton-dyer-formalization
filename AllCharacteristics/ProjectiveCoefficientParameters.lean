import AllCharacteristics.ProjectiveSpaceCharts
import AllCharacteristics.UniversalNonzeroSmoothLocus

/-!
# Projective parameters and normalized universal equations

The coefficient parameter space is the actual Proj on degree-d monomials.
On each standard chart its universal equation has distinguished coefficient
one, so the associated projective hypersurface is proper and flat. All of
these constructions work over arbitrary commutative coefficient rings.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable (R : Type u) [CommRing R] (σ : Type) (d : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The zero homogeneous ideal in the projective coefficient coordinates. -/
noncomputable abbrev ParameterIdeal :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Monomials σ d) R) := ⊥

/-- The actual projective space of coefficients of degree-d equations. -/
noncomputable def projectiveParameters : Scheme.{u} := scheme (ParameterIdeal R σ d)

/-- Projective coefficient space over its original coefficient base. -/
noncomputable def projectiveParametersToBase : projectiveParameters R σ d ⟶ Spec (.of R) :=
  toBase (ParameterIdeal R σ d)

/-- Projective coefficient space is proper over the base. -/
instance isProper_projectiveParametersToBase [Finite σ] :
    IsProper (projectiveParametersToBase R σ d) := isProper_toBase _

/-- Projective coefficient space is smooth over the base in every characteristic. -/
instance smooth_projectiveParametersToBase [Finite σ] :
    Smooth (projectiveParametersToBase R σ d) := smooth_toBase_bot

/-- Every local stalk of projective coefficient space is regular over a regular base. -/
theorem isRegularLocalRing_projectiveParameters_stalk [IsRegularRing R] [Finite σ]
    (x : projectiveParameters R σ d) :
    IsRegularLocalRing ((projectiveParameters R σ d).presheaf.stalk x) :=
  isRegularLocalRing_projectiveSpace_stalk x

/-- The ring of the chart where a specified coefficient is nonzero. -/
abbrev ParameterChartRing (j : Monomials σ d) := ChartRing (ParameterIdeal R σ d) j

/-- The actual standard open chart in projective coefficient space. -/
noncomputable def parameterChartι (j : Monomials σ d) :
    Spec (.of (ParameterChartRing R σ d j)) ⟶ projectiveParameters R σ d :=
  chartι (ParameterIdeal R σ d) j

instance isOpenImmersion_parameterChartι (j : Monomials σ d) :
    IsOpenImmersion (parameterChartι R σ d j) := isOpenImmersion_chartι _ _

/-- The normalized coefficient charts cover the entire projective parameter space. -/
noncomputable def parameterChartCover : (projectiveParameters R σ d).AffineOpenCover :=
  coordinateOpenCover (ParameterIdeal R σ d)

/-- The chart structure morphism is the original coefficient homomorphism. -/
theorem parameterChartι_toBase (j : Monomials σ d) :
    parameterChartι R σ d j ≫ projectiveParametersToBase R σ d =
      Spec.map (CommRingCat.ofHom (chartBaseMap (ParameterIdeal R σ d) j)) :=
  chartι_toBase _ _

/-- Send universal coefficients to their ratios with the distinguished coefficient. -/
noncomputable def normalizedCoefficientMap (j : Monomials σ d) :
    Coefficients σ d R →+* ParameterChartRing R σ d j :=
  eval₂Hom (chartBaseMap (ParameterIdeal R σ d) j) (chartCoordinate (ParameterIdeal R σ d) j)

variable [Finite σ]

/-- The universal homogeneous equation on one projective coefficient chart. -/
noncomputable def normalizedForm (j : Monomials σ d) :
    MvPolynomial σ (ParameterChartRing R σ d j) :=
  (form σ d R).map (normalizedCoefficientMap R σ d j)

/-- The normalized universal equation has the prescribed degree. -/
theorem normalizedForm_isHomogeneous (j : Monomials σ d) :
    (normalizedForm R σ d j).IsHomogeneous d :=
  (form_isHomogeneous σ d R).map (normalizedCoefficientMap R σ d j)

/-- Each coefficient of the normalized equation is the corresponding coordinate ratio. -/
theorem normalizedForm_coeff (j m : Monomials σ d) :
    (normalizedForm R σ d j).coeff m.1 = chartCoordinate (ParameterIdeal R σ d) j m := by
  rw [normalizedForm, MvPolynomial.coeff_map, form_coeff]
  exact eval₂Hom_X' _ _ m

/-- The distinguished coefficient of the normalized equation is exactly one. -/
theorem normalizedForm_coeff_self (j : Monomials σ d) :
    (normalizedForm R σ d j).coeff j.1 = 1 := by
  rw [normalizedForm_coeff, chartCoordinate_self]

/-- The actual universal hypersurface over one projective coefficient chart. -/
noncomputable def normalizedFamilyToBase (j : Monomials σ d) :
    hypersurface (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j) ⟶
      Spec (.of (ParameterChartRing R σ d j)) :=
  hypersurfaceToBase (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)

/-- The universal hypersurface over each normalized coefficient chart is proper. -/
instance isProper_normalizedFamilyToBase (j : Monomials σ d) :
    IsProper (normalizedFamilyToBase R σ d j) := isProper_hypersurfaceToBase _ _

/-- The universal hypersurface over each normalized coefficient chart is flat. -/
instance flat_normalizedFamilyToBase (j : Monomials σ d) :
    Flat (normalizedFamilyToBase R σ d j) :=
  flat_hypersurfaceToBase_of_isUnit_coeff (normalizedForm R σ d j)
    (normalizedForm_isHomogeneous R σ d j) j.1 (by
      rw [normalizedForm_coeff_self]
      exact isUnit_one)

/-- Every specialization of a normalized equation to a nontrivial ring is nonzero. -/
theorem normalizedForm_map_ne_zero (j : Monomials σ d)
    {A : Type u} [CommRing A] [Nontrivial A] (f : ParameterChartRing R σ d j →+* A) :
    (normalizedForm R σ d j).map f ≠ 0 := by
  intro h
  have hc := congrArg (fun p : MvPolynomial σ A ↦ p.coeff j.1) h
  rw [MvPolynomial.coeff_map, normalizedForm_coeff_self, map_one, MvPolynomial.coeff_zero] at hc
  exact one_ne_zero hc

end UniversalHomogeneous
end AllCharacteristics
