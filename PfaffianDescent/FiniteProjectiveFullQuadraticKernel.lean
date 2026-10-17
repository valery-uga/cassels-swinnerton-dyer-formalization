import PfaffianDescent.NormalizedQuadraticSystemCompleteIntersection
import PfaffianDescent.FiniteProjectiveNormalizedCoordinates

/-! Full quadratic systems of actual finite projective closed subschemes.
The chosen coordinates take values in Γ(Z, ⊤), so infinitesimal structure is
retained.  The choice is made internally and its exact ambient map is retained.
This leaf supplies the infinite-field case of the full-base-locus proposition;
it does not claim arbitrary-field descent. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

section CoordinateData
variable {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsAffine Z]
    [Algebra K Γ(Z, ⊤)]

/-- A scheme-theoretic coordinate presentation, with the original immersion
recorded as an equality of ambient morphisms. -/
structure FiniteProjectiveQuadraticCoordinates where
  x : Fin 4 → Γ(Z, ⊤)
  ell : MvPolynomial (Fin 4) K
  homogeneous : ell.IsHomogeneous 1
  normalized : ell.eval₂ (algebraMap K Γ(Z, ⊤)) x = 1
  generates : Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x)
  ambient : normalizedFiniteEquationPoint ⊥ x ell homogeneous normalized
      (fun p hp => by simp [show p = 0 from Ideal.mem_bot.mp hp]) ≫
        quotientProjMap ⊥ = Z.isoSpec.inv ≫ i ≫ quotientProjMap I

end CoordinateData

section ActualFiniteScheme
variable {K : Type u} [Field K] [Infinite K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase I)]

theorem nonempty_finiteProjectiveQuadraticCoordinates :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    Nonempty (FiniteProjectiveQuadraticCoordinates I i) := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  obtain ⟨ell, hell, x, he₀, hellOne, hgen, _, hambient⟩ :=
    finite_projective_closed_subscheme_normalized_ambient_chart I i
  have hn : ell.eval₂ (algebraMap K Γ(Z, ⊤)) x = 1 := by
    exact hellOne
  refine ⟨⟨x, ell, hell, hn, hgen, ?_⟩⟩
  simpa only [normalizedFiniteEquationPoint] using hambient

/-- Canonical choice of an actual chart of the entire finite scheme. -/
def finiteProjectiveQuadraticCoordinates :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    FiniteProjectiveQuadraticCoordinates I i := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  exact Classical.choice (nonempty_finiteProjectiveQuadraticCoordinates I i)

/-- The full quadratic restriction kernel, without taking radicals. -/
def finiteProjectiveFullQuadraticKernel :
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    Submodule K (MvPolynomial (Fin 4) K) := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
  exact normalizedQuadraticSystem (finiteProjectiveQuadraticCoordinates I i).x

/-- Base locus of all quadrics in the actual restriction kernel. -/
def finiteProjectiveFullQuadraticBaseIdeal :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
  exact normalizedQuadraticBaseIdeal (finiteProjectiveQuadraticCoordinates I i).x

theorem finiteProjectiveFullQuadraticKernel_finrank_eq_three
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ toBase I) = 8)
    [IsFinite (toBase (finiteProjectiveFullQuadraticBaseIdeal I i))] :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    Module.finrank K (finiteProjectiveFullQuadraticKernel I i) = 3 := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
  let c := finiteProjectiveQuadraticCoordinates I i
  have hA : Module.finrank K Γ(Z, ⊤) = 8 :=
    (finiteSchemeCoefficient_finrank (i ≫ toBase I)).trans hZ
  exact normalizedQuadraticSystem_finrank_eq_three_of_finite_full_base
    c.x c.ell c.homogeneous c.normalized c.generates hA

/-- Finite full base locus gives a triple containing this exact finite
scheme.  The resulting map is an isomorphism, with its original projective
embedding and its ground-field structural morphism both retained. -/
theorem finiteProjectiveFullQuadraticKernel_exists_triple_iso
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ toBase I) = 8)
    [IsFinite (toBase (finiteProjectiveFullQuadraticBaseIdeal I i))] :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
    ∃ q : Fin 3 → finiteProjectiveFullQuadraticKernel I i,
      IsFinite (toBase (normalizedQuadraticTripleIdeal
        (finiteProjectiveQuadraticCoordinates I i).x q)) ∧
      ∃ l : Z ⟶ scheme (normalizedQuadraticTripleIdeal
          (finiteProjectiveQuadraticCoordinates I i).x q),
        IsIso l ∧
        l ≫ quotientProjMap (normalizedQuadraticTripleIdeal
          (finiteProjectiveQuadraticCoordinates I i).x q) = i ≫ quotientProjMap I ∧
        l ≫ toBase (normalizedQuadraticTripleIdeal
          (finiteProjectiveQuadraticCoordinates I i).x q) = i ≫ toBase I := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
  let c := finiteProjectiveQuadraticCoordinates I i
  have hA : Module.finrank K Γ(Z, ⊤) = 8 :=
    (finiteSchemeCoefficient_finrank (i ≫ toBase I)).trans hZ
  obtain ⟨q, hfinite⟩ := exists_finite_triple_of_finite_full_quadratic_system
    (normalizedQuadraticSystem c.x) (normalizedQuadraticSystem_homogeneous c.x)
  letI := hfinite
  let T := normalizedQuadraticTripleIdeal c.x q
  let e := normalizedFiniteEquationPoint T c.x c.ell c.homogeneous c.normalized
    (normalizedQuadraticTripleIdeal_evaluation_zero c.x q)
  letI : IsIso e := normalizedQuadraticTriplePoint_isIso_of_finite
    c.x c.ell c.homogeneous c.normalized c.generates hA q
  let l : Z ⟶ scheme T := Z.isoSpec.hom ≫ e
  refine ⟨q, hfinite, l, inferInstance, ?_, ?_⟩
  · change (Z.isoSpec.hom ≫ e) ≫ quotientProjMap T = i ≫ quotientProjMap I
    rw [Category.assoc, normalizedFiniteEquationPoint_toAmbient, c.ambient]
    simp
  · change (Z.isoSpec.hom ≫ e) ≫ toBase T = i ≫ toBase I
    rw [Category.assoc, normalizedFiniteEquationPoint_toBase,
      finiteSchemeCoefficient_spec]
    simp

end ActualFiniteScheme
end PfaffianDescent
