import AllCharacteristics.ProjectiveTripleOverlap
import AllCharacteristics.NormalizedFamilyBaseChange

/-!
# Universal family coherence on actual triple intersections

The coefficient maps are the restrictions from the actual product-coordinate
triple intersection. The three pairwise specialized equations have equal
homogeneous ideals, and their canonical actual fiber isomorphisms satisfy the
cocycle law over that intersection spectrum.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable (R : Type u) [CommRing R] (σ : Type) [Finite σ] (d : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I₀" => ParameterIdeal R σ d

/-- The two equations restricted to an actual pair intersection generate the same ideal. -/
theorem normalizedOverlap_ideal_eq (i j : Monomials σ d) :
    equationIdeal ((normalizedForm R σ d i).map (chartOverlapLeftMap I₀ i j))
      ((normalizedForm_isHomogeneous R σ d i).map (chartOverlapLeftMap I₀ i j)) =
    equationIdeal ((normalizedForm R σ d j).map (chartOverlapRightMap I₀ i j))
      ((normalizedForm_isHomogeneous R σ d j).map (chartOverlapRightMap I₀ i j)) :=
  equationIdeal_eq_of_unit_multiple _ _ _ _
    (↑((chartOverlapUnit I₀ i j)⁻¹) : ChartOverlapRing I₀ i j)
    ((chartOverlapUnit I₀ i j)⁻¹).isUnit (normalizedForm_overlap_relation R σ d i j)

variable (i j l : Monomials σ d)

/-- The first coefficient chart restricted to the actual triple intersection. -/
noncomputable def normalizedTripleFirstChartMap : ParameterChartRing R σ d i →+* ChartTripleRing I₀ i j l :=
  (chartTripleFromFirstPair I₀ i j l).comp (chartOverlapLeftMap I₀ i j)

/-- The middle coefficient chart restricted to that same triple intersection. -/
noncomputable def normalizedTripleMiddleChartMap : ParameterChartRing R σ d j →+* ChartTripleRing I₀ i j l :=
  (chartTripleFromFirstPair I₀ i j l).comp (chartOverlapRightMap I₀ i j)

/-- The last coefficient chart restricted to that same triple intersection. -/
noncomputable def normalizedTripleLastChartMap : ParameterChartRing R σ d l →+* ChartTripleRing I₀ i j l :=
  (chartTripleFromLastPair I₀ i j l).comp (chartOverlapRightMap I₀ j l)

/-- The first and middle equations define the same hypersurface on the actual triple intersection. -/
theorem normalizedTriple_first_middle_ideal :
    equationIdeal ((normalizedForm R σ d i).map (normalizedTripleFirstChartMap R σ d i j l))
      ((normalizedForm_isHomogeneous R σ d i).map (normalizedTripleFirstChartMap R σ d i j l)) =
    equationIdeal ((normalizedForm R σ d j).map (normalizedTripleMiddleChartMap R σ d i j l))
      ((normalizedForm_isHomogeneous R σ d j).map (normalizedTripleMiddleChartMap R σ d i j l)) :=
  equationIdeal_specialization_eq_map (chartOverlapLeftMap I₀ i j)
    (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i)
    (chartOverlapRightMap I₀ i j) (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
    (normalizedOverlap_ideal_eq R σ d i j) (chartTripleFromFirstPair I₀ i j l)

/-- The middle and last equations agree as ideals, using the proved agreement of
both restrictions from the shared middle coefficient chart. -/
theorem normalizedTriple_middle_last_ideal :
    equationIdeal ((normalizedForm R σ d j).map (normalizedTripleMiddleChartMap R σ d i j l))
      ((normalizedForm_isHomogeneous R σ d j).map (normalizedTripleMiddleChartMap R σ d i j l)) =
    equationIdeal ((normalizedForm R σ d l).map (normalizedTripleLastChartMap R σ d i j l))
      ((normalizedForm_isHomogeneous R σ d l).map (normalizedTripleLastChartMap R σ d i j l)) := by
  have he := congrArg (fun f : ParameterChartRing R σ d j →+* ChartTripleRing I₀ i j l ↦
    equationIdeal ((normalizedForm R σ d j).map f) ((normalizedForm_isHomogeneous R σ d j).map f))
      (chartTriple_middle_compat I₀ i j l)
  exact he.trans (equationIdeal_specialization_eq_map (chartOverlapLeftMap I₀ j l)
    (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
    (chartOverlapRightMap I₀ j l) (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l)
    (normalizedOverlap_ideal_eq R σ d j l) (chartTripleFromLastPair I₀ i j l))

/-- The outer pair equation equality restricts to the same first and last
triple-chart equations, via the actual pair-restriction compatibility identities. -/
theorem normalizedTriple_first_last_ideal :
    equationIdeal ((normalizedForm R σ d i).map (normalizedTripleFirstChartMap R σ d i j l))
      ((normalizedForm_isHomogeneous R σ d i).map (normalizedTripleFirstChartMap R σ d i j l)) =
    equationIdeal ((normalizedForm R σ d l).map (normalizedTripleLastChartMap R σ d i j l))
      ((normalizedForm_isHomogeneous R σ d l).map (normalizedTripleLastChartMap R σ d i j l)) := by
  have hi := congrArg (fun f : ParameterChartRing R σ d i →+* ChartTripleRing I₀ i j l ↦
    equationIdeal ((normalizedForm R σ d i).map f) ((normalizedForm_isHomogeneous R σ d i).map f))
      (chartTriple_first_compat I₀ i j l)
  have hl := congrArg (fun f : ParameterChartRing R σ d l →+* ChartTripleRing I₀ i j l ↦
    equationIdeal ((normalizedForm R σ d l).map f) ((normalizedForm_isHomogeneous R σ d l).map f))
      (chartTriple_last_compat I₀ i j l)
  have he := equationIdeal_specialization_eq_map (chartOverlapLeftMap I₀ i l)
    (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i)
    (chartOverlapRightMap I₀ i l) (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l)
    (normalizedOverlap_ideal_eq R σ d i l) (chartTripleFromOuterPair I₀ i j l)
  exact hi.trans (he.trans hl.symm)

/-- The first-to-middle actual chart-family comparison over the triple intersection. -/
noncomputable def normalizedTripleFirstMiddleIso :
    pullback (normalizedFamilyToBase R σ d i)
      (Spec.map (CommRingCat.ofHom (normalizedTripleFirstChartMap R σ d i j l))) ≅
    pullback (normalizedFamilyToBase R σ d j)
      (Spec.map (CommRingCat.ofHom (normalizedTripleMiddleChartMap R σ d i j l))) :=
  hypersurfaceFiberComparison (normalizedTripleFirstChartMap R σ d i j l)
    (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i)
    (normalizedTripleMiddleChartMap R σ d i j l)
    (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
    (normalizedTriple_first_middle_ideal R σ d i j l)

/-- The middle-to-last actual chart-family comparison over the triple intersection. -/
noncomputable def normalizedTripleMiddleLastIso :
    pullback (normalizedFamilyToBase R σ d j)
      (Spec.map (CommRingCat.ofHom (normalizedTripleMiddleChartMap R σ d i j l))) ≅
    pullback (normalizedFamilyToBase R σ d l)
      (Spec.map (CommRingCat.ofHom (normalizedTripleLastChartMap R σ d i j l))) :=
  hypersurfaceFiberComparison (normalizedTripleMiddleChartMap R σ d i j l)
    (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
    (normalizedTripleLastChartMap R σ d i j l)
    (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l)
    (normalizedTriple_middle_last_ideal R σ d i j l)

/-- The direct outer-pair actual family comparison over the triple intersection. -/
noncomputable def normalizedTripleFirstLastIso :
    pullback (normalizedFamilyToBase R σ d i)
      (Spec.map (CommRingCat.ofHom (normalizedTripleFirstChartMap R σ d i j l))) ≅
    pullback (normalizedFamilyToBase R σ d l)
      (Spec.map (CommRingCat.ofHom (normalizedTripleLastChartMap R σ d i j l))) :=
  hypersurfaceFiberComparison (normalizedTripleFirstChartMap R σ d i j l)
    (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i)
    (normalizedTripleLastChartMap R σ d i j l)
    (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l)
    (normalizedTriple_first_last_ideal R σ d i j l)

/-- The actual universal chart families satisfy the cocycle on their actual
triple intersection, with the outer comparison induced from the outer pair. -/
theorem normalizedTripleFamilyIso_comp :
    normalizedTripleFirstMiddleIso R σ d i j l ≪≫ normalizedTripleMiddleLastIso R σ d i j l =
      normalizedTripleFirstLastIso R σ d i j l :=
  hypersurfaceFiberComparison_comp (normalizedTripleFirstChartMap R σ d i j l)
    (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i)
    (normalizedTripleMiddleChartMap R σ d i j l)
    (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
    (normalizedTripleLastChartMap R σ d i j l)
    (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l)
    (normalizedTriple_first_middle_ideal R σ d i j l) (normalizedTriple_middle_last_ideal R σ d i j l)

end UniversalHomogeneous
end AllCharacteristics
