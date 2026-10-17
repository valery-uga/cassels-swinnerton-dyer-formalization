import AllCharacteristics.ProjectiveConfigurationGenericPoint
import AllCharacteristics.VoisinGenericCubicConfiguration

/-!
# The generic cubic configuration is one closed point

The irreducibility of incidence over unordered configurations survives the
identification of the generic fiber with the coefficient-changed cubic.
Consequently a closed subscheme defined over the configuration function
field either misses the generic configuration or contains it entirely.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

variable (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
variable [hordered :
  IsIntegral (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) n).left]

local instance : IsIntegral (cubicConfigurationBase p hp n) :=
  @isIntegral_projectiveConfigurationQuotientOpen _ _ _ _ _
    (grading (equationIdeal p hp)) _ _ _ (toBase (equationIdeal p hp)) n hordered

variable (a : CommRingCat.of K ⟶ CommRingCat.of
  (cubicConfigurationBase p hp n).functionField)
variable (ha : Spec.map a =
  cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n)

/-- The finite datum on the coefficient-changed cubic has exactly one
topological point, just as the generic incidence fiber does. -/
theorem cubicConfigurationGenericFiniteSubscheme_nonempty_subsingleton (i : Fin n) :
    Nonempty (cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subscheme ∧
      Subsingleton (cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subscheme := by
  unfold cubicConfigurationGenericFiniteSubscheme
    hypersurfaceFiniteSubschemeOfCoefficientBaseChange
  apply nonempty_subsingleton_of_schemeIso
    (FiniteSubschemeDatum.transportAlongAmbientIsoSubschemeIso _ _ _ _ _)
  exact @projectiveConfigurationGenericFiniteSubschemeAtBaseMap_nonempty_subsingleton
    _ _ _ _ _ (grading (equationIdeal p hp)) _ K _
    (toBase (equationIdeal p hp))
    (isSeparated_homogeneousToBase (equationIdeal p hp)) n hordered _ _ i

/-- The generic rank-`n` datum on the cubic is a field spectrum, without
an additional transitivity or perfectness assumption. -/
theorem cubicConfigurationGenericFiniteSubscheme_isField (i : Fin n) :
    IsField Γ((cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subscheme, ⊤) := by
  let D := cubicConfigurationGenericFiniteSubscheme p hp n a ha
  let f := hypersurfaceToBase (p.map a.hom) (hp.map a.hom)
  have h := cubicConfigurationGenericFiniteSubscheme_nonempty_subsingleton p hp n a ha i
  have : Nonempty D.val.subscheme := h.1
  have : Subsingleton D.val.subscheme := h.2
  have : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  have : Etale (D.val.subschemeι ≫ f) :=
    etale_cubicConfigurationGenericFiniteSubscheme_toBase p hp n a ha
  exact finiteEtaleScheme_isField_of_subsingleton (D.val.subschemeι ≫ f)

/-- A closed subscheme of the generic cubic either misses the configuration
or contains it scheme-theoretically. This applies in particular to a fixed
curve defined over the configuration function field. -/
theorem cubicConfigurationGenericFiniteSubscheme_isEmpty_pullback_or_factors
    (i : Fin n) {C : Scheme.{u}}
    (j : C ⟶ hypersurface (p.map a.hom) (hp.map a.hom)) [IsClosedImmersion j] :
    IsEmpty (pullback j (cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subschemeι :
      Scheme.{u}) ∨
      ∃ h : (cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subscheme ⟶ C,
        h ≫ j = (cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subschemeι := by
  let D := cubicConfigurationGenericFiniteSubscheme p hp n a ha
  let f := hypersurfaceToBase (p.map a.hom) (hp.map a.hom)
  have : Subsingleton D.val.subscheme :=
    (cubicConfigurationGenericFiniteSubscheme_nonempty_subsingleton p hp n a ha i).2
  have : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  have : IsAffine D.val.subscheme := isAffine_of_isAffineHom (D.val.subschemeι ≫ f)
  let : Field Γ(D.val.subscheme, ⊤) :=
    (cubicConfigurationGenericFiniteSubscheme_isField p hp n a ha i).toField
  have : IsReduced D.val.subscheme := isReduced_of_isAffine_isReduced D.val.subscheme
  exact isEmpty_pullback_or_factors_of_reduced_subsingleton j D.val.subschemeι

end AllCharacteristics.HomogeneousProjective
