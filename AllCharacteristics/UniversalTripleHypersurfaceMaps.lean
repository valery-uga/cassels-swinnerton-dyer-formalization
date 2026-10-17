import AllCharacteristics.UniversalTripleFamilyCocycle
import AllCharacteristics.UniversalOverlapSymmetry

/-!
# Canonical maps from the actual universal triple hypersurface

A single hypersurface over the triple-intersection coefficient ring maps to
all three pair-overlap families. Its six chart projections agree with the
three canonical projective coefficient maps.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable (R : Type u) [CommRing R] (σ : Type) [Finite σ] (d : ℕ)
variable (i j l : Monomials σ d)
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I₀" => ParameterIdeal R σ d
local notation "Fi" => normalizedTripleFirstChartMap R σ d i j l
local notation "Fj" => normalizedTripleMiddleChartMap R σ d i j l
local notation "Fl" => normalizedTripleLastChartMap R σ d i j l
/-- The common homogeneous ideal of the actual universal triple hypersurface. -/
noncomputable abbrev normalizedTripleIdeal : HomogeneousIdeal (homogeneousSubmodule σ (ChartTripleRing I₀ i j l)) :=
  equationIdeal ((normalizedForm R σ d l).map Fl) ((normalizedForm_isHomogeneous R σ d l).map Fl)

local notation "WIdeal" => normalizedTripleIdeal R σ d i j l

/-- The actual triple hypersurface, using the last normalized equation on the common triple spectrum. -/
noncomputable def normalizedTripleHypersurface : Scheme.{u} := scheme WIdeal

/-- Its structure map to the actual triple coefficient spectrum. -/
noncomputable def normalizedTripleToBase :
    normalizedTripleHypersurface R σ d i j l ⟶ Spec (.of (ChartTripleRing I₀ i j l)) := toBase WIdeal

/-- The first pair's ideal restricts to the triple hypersurface ideal. -/
theorem normalizedTripleFirstPair_ideal :
    (equationIdeal ((normalizedForm R σ d j).map (chartOverlapRightMap I₀ i j))
      ((normalizedForm_isHomogeneous R σ d j).map (chartOverlapRightMap I₀ i j))).toIdeal.map
        (MvPolynomial.map (chartTripleFromFirstPair I₀ i j l)) = (WIdeal).toIdeal :=
  (equationIdeal_map_comp (chartOverlapRightMap I₀ i j) (chartTripleFromFirstPair I₀ i j l)
    (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)).trans
    (congrArg HomogeneousIdeal.toIdeal (normalizedTriple_middle_last_ideal R σ d i j l))

/-- The outer pair's equation restricts to the chosen triple equation. -/
theorem normalizedTripleOuterPair_ideal :
    (equationIdeal ((normalizedForm R σ d l).map (chartOverlapRightMap I₀ i l))
      ((normalizedForm_isHomogeneous R σ d l).map (chartOverlapRightMap I₀ i l))).toIdeal.map
        (MvPolynomial.map (chartTripleFromOuterPair I₀ i j l)) = (WIdeal).toIdeal :=
  equationIdeal_map_of_eq _ _ _ _ _ (by
    rw [MvPolynomial.map_map, ← chartTriple_last_compat]
    rfl)

/-- The last pair's equation restricts to the chosen triple equation. -/
theorem normalizedTripleLastPair_ideal :
    (equationIdeal ((normalizedForm R σ d l).map (chartOverlapRightMap I₀ j l))
      ((normalizedForm_isHomogeneous R σ d l).map (chartOverlapRightMap I₀ j l))).toIdeal.map
        (MvPolynomial.map (chartTripleFromLastPair I₀ i j l)) = (WIdeal).toIdeal :=
  equationIdeal_map_comp (chartOverlapRightMap I₀ j l) (chartTripleFromLastPair I₀ i j l)
    (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l)

/-- The canonical map from the triple hypersurface to the first pair-overlap family. -/
noncomputable def normalizedTripleToFirstPair : normalizedTripleHypersurface R σ d i j l ⟶
    normalizedOverlapHypersurface R σ d i j :=
  projectiveCoefficientMap (chartTripleFromFirstPair I₀ i j l) _ WIdeal
    (normalizedTripleFirstPair_ideal R σ d i j l)

/-- The canonical map from the triple hypersurface to the outer pair-overlap family. -/
noncomputable def normalizedTripleToOuterPair : normalizedTripleHypersurface R σ d i j l ⟶
    normalizedOverlapHypersurface R σ d i l :=
  projectiveCoefficientMap (chartTripleFromOuterPair I₀ i j l) _ WIdeal
    (normalizedTripleOuterPair_ideal R σ d i j l)

/-- The canonical map from the triple hypersurface to the last pair-overlap family. -/
noncomputable def normalizedTripleToLastPair : normalizedTripleHypersurface R σ d i j l ⟶
    normalizedOverlapHypersurface R σ d j l :=
  projectiveCoefficientMap (chartTripleFromLastPair I₀ i j l) _ WIdeal
    (normalizedTripleLastPair_ideal R σ d i j l)

/-- The first chart's universal ideal maps to the triple ideal. -/
theorem normalizedTripleFirstChart_ideal :
    (equationIdeal (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i)).toIdeal.map
      (MvPolynomial.map Fi) = (WIdeal).toIdeal :=
  (equationIdeal_map Fi (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i)).trans
    (congrArg HomogeneousIdeal.toIdeal (normalizedTriple_first_last_ideal R σ d i j l))

/-- The middle chart's universal ideal maps to that same triple ideal. -/
theorem normalizedTripleMiddleChart_ideal :
    (equationIdeal (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)).toIdeal.map
      (MvPolynomial.map Fj) = (WIdeal).toIdeal :=
  (equationIdeal_map Fj (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)).trans
    (congrArg HomogeneousIdeal.toIdeal (normalizedTriple_middle_last_ideal R σ d i j l))

/-- The canonical projection from the triple hypersurface to the first universal chart family. -/
noncomputable def normalizedTripleToFirstChart : normalizedTripleHypersurface R σ d i j l ⟶
    hypersurface (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i) :=
  projectiveCoefficientMap Fi _ WIdeal (normalizedTripleFirstChart_ideal R σ d i j l)

/-- The canonical projection to the middle universal chart family. -/
noncomputable def normalizedTripleToMiddleChart : normalizedTripleHypersurface R σ d i j l ⟶
    hypersurface (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j) :=
  projectiveCoefficientMap Fj _ WIdeal (normalizedTripleMiddleChart_ideal R σ d i j l)

/-- The canonical projection to the last universal chart family. -/
noncomputable def normalizedTripleToLastChart : normalizedTripleHypersurface R σ d i j l ⟶
    hypersurface (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l) :=
  projectiveCoefficientMap Fl _ WIdeal
    (equationIdeal_map Fl (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l))

/-- The first pair's left projection is the triple's first chart projection. -/
theorem normalizedTripleToFirstPair_left :
    normalizedTripleToFirstPair R σ d i j l ≫ normalizedOverlapToLeft R σ d i j =
      normalizedTripleToFirstChart R σ d i j l :=
  projectiveCoefficientMap_comp_eq (chartOverlapLeftMap I₀ i j) (chartTripleFromFirstPair I₀ i j l)
    Fi _ _ _
    (equationIdeal_map_of_unit_multiple _ _ _ _ _ _ ((chartOverlapUnit I₀ i j)⁻¹).isUnit
      (normalizedForm_overlap_relation R σ d i j))
    (normalizedTripleFirstPair_ideal R σ d i j l) (normalizedTripleFirstChart_ideal R σ d i j l) rfl

/-- The first pair's right projection is the triple's middle chart projection. -/
theorem normalizedTripleToFirstPair_right :
    normalizedTripleToFirstPair R σ d i j l ≫ normalizedOverlapToRight R σ d i j =
      normalizedTripleToMiddleChart R σ d i j l :=
  projectiveCoefficientMap_comp_eq (chartOverlapRightMap I₀ i j) (chartTripleFromFirstPair I₀ i j l)
    Fj _ _ _
    (equationIdeal_map (chartOverlapRightMap I₀ i j) (normalizedForm R σ d j)
      (normalizedForm_isHomogeneous R σ d j))
    (normalizedTripleFirstPair_ideal R σ d i j l) (normalizedTripleMiddleChart_ideal R σ d i j l) rfl

/-- The outer pair's left projection is the same first chart projection. -/
theorem normalizedTripleToOuterPair_left :
    normalizedTripleToOuterPair R σ d i j l ≫ normalizedOverlapToLeft R σ d i l =
      normalizedTripleToFirstChart R σ d i j l :=
  projectiveCoefficientMap_comp_eq (chartOverlapLeftMap I₀ i l) (chartTripleFromOuterPair I₀ i j l)
    Fi _ _ _
    (equationIdeal_map_of_unit_multiple _ _ _ _ _ _ ((chartOverlapUnit I₀ i l)⁻¹).isUnit
      (normalizedForm_overlap_relation R σ d i l))
    (normalizedTripleOuterPair_ideal R σ d i j l) (normalizedTripleFirstChart_ideal R σ d i j l)
    (chartTriple_first_compat I₀ i j l).symm

/-- The outer pair's right projection is the same last chart projection. -/
theorem normalizedTripleToOuterPair_right :
    normalizedTripleToOuterPair R σ d i j l ≫ normalizedOverlapToRight R σ d i l =
      normalizedTripleToLastChart R σ d i j l :=
  projectiveCoefficientMap_comp_eq (chartOverlapRightMap I₀ i l) (chartTripleFromOuterPair I₀ i j l)
    Fl _ _ _
    (equationIdeal_map (chartOverlapRightMap I₀ i l) (normalizedForm R σ d l)
      (normalizedForm_isHomogeneous R σ d l))
    (normalizedTripleOuterPair_ideal R σ d i j l)
    (equationIdeal_map Fl (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l))
    (chartTriple_last_compat I₀ i j l).symm

/-- The last pair's left projection is the same middle chart projection. -/
theorem normalizedTripleToLastPair_left :
    normalizedTripleToLastPair R σ d i j l ≫ normalizedOverlapToLeft R σ d j l =
      normalizedTripleToMiddleChart R σ d i j l :=
  projectiveCoefficientMap_comp_eq (chartOverlapLeftMap I₀ j l) (chartTripleFromLastPair I₀ i j l)
    Fj _ _ _
    (equationIdeal_map_of_unit_multiple _ _ _ _ _ _ ((chartOverlapUnit I₀ j l)⁻¹).isUnit
      (normalizedForm_overlap_relation R σ d j l))
    (normalizedTripleLastPair_ideal R σ d i j l) (normalizedTripleMiddleChart_ideal R σ d i j l)
    (chartTriple_middle_compat I₀ i j l).symm

/-- The last pair's right projection is the same last chart projection. -/
theorem normalizedTripleToLastPair_right :
    normalizedTripleToLastPair R σ d i j l ≫ normalizedOverlapToRight R σ d j l =
      normalizedTripleToLastChart R σ d i j l :=
  projectiveCoefficientMap_comp_eq (chartOverlapRightMap I₀ j l) (chartTripleFromLastPair I₀ i j l)
    Fl _ _ _
    (equationIdeal_map (chartOverlapRightMap I₀ j l) (normalizedForm R σ d l)
      (normalizedForm_isHomogeneous R σ d l))
    (normalizedTripleLastPair_ideal R σ d i j l)
    (equationIdeal_map Fl (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l)) rfl

end UniversalHomogeneous
end AllCharacteristics
