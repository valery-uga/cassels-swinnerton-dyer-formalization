import AllCharacteristics.UniversalTripleFamilyCocycle
import AllCharacteristics.ProjectiveRestrictionOfEq

/-!
# Actual triple-family comparisons restrict the original overlap comparisons

Each of the three triple-intersection comparisons commutes with the original
pair-overlap isomorphism and the canonical Cartesian restriction maps. Thus
the proved triple cocycle is the cocycle of the original overlap families.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable (R : Type u) [CommRing R] (σ : Type) [Finite σ] (d : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I₀" => ParameterIdeal R σ d

/-- An actual pair-overlap family comparison is natural under any further
coefficient restriction with specified source and target chart maps. -/
theorem normalizedOverlapFamilyIso_restriction {A : Type u} [CommRing A]
    (i j : Monomials σ d) (t : ChartOverlapRing I₀ i j →+* A)
    (f : ParameterChartRing R σ d i →+* A) (g : ParameterChartRing R σ d j →+* A)
    (hf : t.comp (chartOverlapLeftMap I₀ i j) = f)
    (hg : t.comp (chartOverlapRightMap I₀ i j) = g)
    (h : equationIdeal ((normalizedForm R σ d i).map f) ((normalizedForm_isHomogeneous R σ d i).map f) =
      equationIdeal ((normalizedForm R σ d j).map g) ((normalizedForm_isHomogeneous R σ d j).map g)) :
    (hypersurfaceFiberComparison f (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i)
      g (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j) h).hom ≫
      projectiveFiberRestrictionOfEq (chartOverlapRightMap I₀ i j) t g
        (equationIdeal (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)) hg =
    projectiveFiberRestrictionOfEq (chartOverlapLeftMap I₀ i j) t f
      (equationIdeal (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i)) hf ≫
      (normalizedOverlapFamilyIso R σ d i j).hom := by
  have hn := hypersurfaceFiberComparison_naturality_of_eq (chartOverlapLeftMap I₀ i j)
    (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i)
    (chartOverlapRightMap I₀ i j) (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
    (normalizedOverlap_ideal_eq R σ d i j) t f g hf hg h
  have he := congrArg Iso.hom (normalizedOverlapFamilyIso_eq_fiberComparison (R := R) i j)
  exact hn.trans (congrArg (fun a ↦ projectiveFiberRestrictionOfEq (chartOverlapLeftMap I₀ i j)
    t f (equationIdeal (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i)) hf ≫ a) he.symm)

variable (i j l : Monomials σ d)

/-- The first-to-middle triple comparison is the actual restriction of the first pair comparison. -/
theorem normalizedTripleFirstMiddleIso_restriction :
    (normalizedTripleFirstMiddleIso R σ d i j l).hom ≫
      projectiveFiberRestrictionOfEq (chartOverlapRightMap I₀ i j) (chartTripleFromFirstPair I₀ i j l)
        (normalizedTripleMiddleChartMap R σ d i j l)
        (equationIdeal (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)) rfl =
    projectiveFiberRestrictionOfEq (chartOverlapLeftMap I₀ i j) (chartTripleFromFirstPair I₀ i j l)
      (normalizedTripleFirstChartMap R σ d i j l)
      (equationIdeal (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i)) rfl ≫
      (normalizedOverlapFamilyIso R σ d i j).hom :=
  normalizedOverlapFamilyIso_restriction R σ d i j (chartTripleFromFirstPair I₀ i j l)
    (normalizedTripleFirstChartMap R σ d i j l) (normalizedTripleMiddleChartMap R σ d i j l)
    rfl rfl (normalizedTriple_first_middle_ideal R σ d i j l)

/-- The middle-to-last triple comparison is the actual restriction of the last pair comparison. -/
theorem normalizedTripleMiddleLastIso_restriction :
    (normalizedTripleMiddleLastIso R σ d i j l).hom ≫
      projectiveFiberRestrictionOfEq (chartOverlapRightMap I₀ j l) (chartTripleFromLastPair I₀ i j l)
        (normalizedTripleLastChartMap R σ d i j l)
        (equationIdeal (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l)) rfl =
    projectiveFiberRestrictionOfEq (chartOverlapLeftMap I₀ j l) (chartTripleFromLastPair I₀ i j l)
      (normalizedTripleMiddleChartMap R σ d i j l)
      (equationIdeal (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j))
      (chartTriple_middle_compat I₀ i j l).symm ≫ (normalizedOverlapFamilyIso R σ d j l).hom :=
  normalizedOverlapFamilyIso_restriction R σ d j l (chartTripleFromLastPair I₀ i j l)
    (normalizedTripleMiddleChartMap R σ d i j l) (normalizedTripleLastChartMap R σ d i j l)
    (chartTriple_middle_compat I₀ i j l).symm rfl (normalizedTriple_middle_last_ideal R σ d i j l)

/-- The direct triple comparison is the actual restriction of the outer pair comparison. -/
theorem normalizedTripleFirstLastIso_restriction :
    (normalizedTripleFirstLastIso R σ d i j l).hom ≫
      projectiveFiberRestrictionOfEq (chartOverlapRightMap I₀ i l) (chartTripleFromOuterPair I₀ i j l)
        (normalizedTripleLastChartMap R σ d i j l)
        (equationIdeal (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l))
        (chartTriple_last_compat I₀ i j l).symm =
    projectiveFiberRestrictionOfEq (chartOverlapLeftMap I₀ i l) (chartTripleFromOuterPair I₀ i j l)
      (normalizedTripleFirstChartMap R σ d i j l)
      (equationIdeal (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i))
      (chartTriple_first_compat I₀ i j l).symm ≫ (normalizedOverlapFamilyIso R σ d i l).hom :=
  normalizedOverlapFamilyIso_restriction R σ d i l (chartTripleFromOuterPair I₀ i j l)
    (normalizedTripleFirstChartMap R σ d i j l) (normalizedTripleLastChartMap R σ d i j l)
    (chartTriple_first_compat I₀ i j l).symm (chartTriple_last_compat I₀ i j l).symm
    (normalizedTriple_first_last_ideal R σ d i j l)

end UniversalHomogeneous
end AllCharacteristics
