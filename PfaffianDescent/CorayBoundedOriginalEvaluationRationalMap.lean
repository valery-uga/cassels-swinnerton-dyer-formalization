import PfaffianDescent.CorayExplicitProjectiveEvaluationPoint
import PfaffianDescent.CorayOriginalChartGenericLinearity
import AllCharacteristics.FunctionFieldRationalMapDominance

/-! Source-only / unverified. Explicit generic evaluation of the actual
bounded degree-n through-P family spreads to a rational map over ORIGINAL K.
Its generic point and normalized coordinates are retained in the exported
conclusion. No image dimension/rank, integral member, or transversality is
supplied or inferred from this map construction. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped AlgebraicGeometry PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

section
variable {K L : Type u} [Field K] [CommRing L] [Algebra K L]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
  [IsIntegral (hypersurface p hp)]
variable (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
  (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]

/-- Actual generic values of an actual basis, carrying the independently
defined ORIGINAL-pi K function-field action. -/
def cubicThroughPointBasisGenericCoordinates {m : ℕ}
    (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy)) :
    Fin m → SchemeFunctionFieldOver (hypersurfaceToBase p hp) :=
  fun a => cubicThroughPointGenericLinearEvaluation p hp n y hpy j (b a)

end

section
variable {K L : Type u} [Field K] [CommRing L] [Algebra K L]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
  [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
variable (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
  (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]

include hp0 in
/-- Every basis coordinate is nonzero in the actual generic field, proved
from prime-cone normalization and the actual generic germ. -/
theorem cubicThroughPointBasisGenericCoordinates_ne_zero {m : ℕ}
    (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) : cubicThroughPointBasisGenericCoordinates p hp n y hpy j b a ≠ 0 := by
  change cubicThroughPointGenericLinearEvaluation p hp n y hpy j (b a) ≠ 0
  exact (evaluatedBasis_linearIndependent
    (K := K) (V := cubicThroughCoordinateSections p hp n y hpy)
    (B := SchemeFunctionFieldOver (hypersurfaceToBase p hp)) (ι := Fin m)
    b (cubicThroughPointGenericLinearEvaluation p hp n y hpy j)
    (cubicThroughPointGenericLinearEvaluation_injective p hp n y hpy j hp0)).ne_zero a

/-- Actual normalized generic chart hom, with its nonzero denominator
proved from the ORIGINAL bounded family, not supplied as an output premise. -/
def cubicThroughPointBasisGenericChartMap {m : ℕ}
    (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) :
    ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a →+*
      (hypersurface p hp).functionField :=
  projectiveEvaluationChartMap (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp))
    (cubicThroughPointBasisGenericCoordinates p hp n y hpy j b) a
    (cubicThroughPointBasisGenericCoordinates_ne_zero p hp hp0 n y hpy j b a)

theorem cubicThroughPointBasisGenericChartMap_coordinate {m : ℕ}
    (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a i : Fin m) :
    cubicThroughPointBasisGenericChartMap p hp hp0 n y hpy j b a
      (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a i) =
        @Div.div (hypersurface p hp).functionField
          (inferInstance : Div (hypersurface p hp).functionField)
          (cubicThroughPointBasisGenericCoordinates p hp n y hpy j b i)
          (cubicThroughPointBasisGenericCoordinates p hp n y hpy j b a) :=
  projectiveEvaluationChartMap_coordinate
    (K := K) (F := (hypersurface p hp).functionField) (σ := Fin m)
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp))
    (cubicThroughPointBasisGenericCoordinates p hp n y hpy j b) a
    (cubicThroughPointBasisGenericCoordinates_ne_zero p hp hp0 n y hpy j b a) i

/-- The specified original bounded-system generic point is the Spec map
of the ACTUAL chart map with the exported coordinate ratios. -/
def cubicThroughPointBasisGenericPoint {m : ℕ}
    (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) :
    Spec (hypersurface p hp).functionField ⟶
      scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) :=
  Spec.map (CommRingCat.ofHom
    (cubicThroughPointBasisGenericChartMap p hp hp0 n y hpy j b a)) ≫
      chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem cubicThroughPointBasisGenericPoint_toBase {m : ℕ}
    (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) :
    cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a ≫
      toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) =
        (hypersurface p hp).fromSpecStalk (genericPoint (hypersurface p hp)) ≫
          hypersurfaceToBase p hp := by
  change projectiveEvaluationPoint
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp))
    (cubicThroughPointBasisGenericCoordinates p hp n y hpy j b) a
    (cubicThroughPointBasisGenericCoordinates_ne_zero p hp hp0 n y hpy j b a) ≫ _ = _
  rw [projectiveEvaluationPoint_toBase,
    ← cubicChartGenericEvaluation_coefficient_eq p hp j]
  exact affineChartGenericEvaluation_coefficient_spec (hypersurfaceToBase p hp)
    (chartι (equationIdeal p hp) j) (chartBaseMap (equationIdeal p hp) j)
    (chartι_toBase (equationIdeal p hp) j)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual evaluation point spreads to a rational map over ORIGINAL K,
with its EXACT specified generic field point retained in the conclusion. -/
theorem exists_cubicThroughPointBasisEvaluationRationalMap {m : ℕ}
    (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) :
    ∃ f : (hypersurface p hp) ⤏
        scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)),
      f.compHom (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K))) =
        (hypersurfaceToBase p hp).toRationalMap ∧
      f.fromFunctionField = cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a := by
  exact AllCharacteristics.rationalMap_of_functionField_map (hypersurfaceToBase p hp)
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)))
    (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a)
    (cubicThroughPointBasisGenericPoint_toBase p hp hp0 n y hpy j b a)

variable [FiniteDimensional K L]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- From the actual Coray H_n-d window, choose a basis and nonzero chart
entry internally and construct the ORIGINAL-K evaluation rational map to
P^(m-1), m≥5. No image/rank/regularity premise is added. -/
theorem exists_bounded_cubicThroughPointEvaluationRationalMap
    (hsize : finrank K L + 5 ≤ (n + 3).choose 3 - n.choose 3) :
    ∃ m : ℕ, 5 ≤ m ∧
      ∃ (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
        (a : Fin m)
        (f : (hypersurface p hp) ⤏
          scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K))),
        f.compHom (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K))) =
          (hypersurfaceToBase p hp).toRationalMap ∧
        f.fromFunctionField = cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a := by
  letI : Module.Finite K (grading (equationIdeal p hp) n) :=
    Module.Finite.iff_fg.mpr ((homogeneousSubmodule_fg (Fin 4) K n).map
      (Ideal.Quotient.mkₐ K (equationIdeal p hp).toIdeal).toLinearMap)
  let W := cubicThroughCoordinateSections p hp n y hpy
  letI : Module.Free K W := Module.Free.of_divisionRing K W
  let b : Module.Basis (Fin (finrank K W)) K W := Module.finBasis K W
  have h5 : 5 ≤ finrank K W :=
    cubicThroughCoordinateSections_finrank_ge_five p hp hp0 n y hpy hsize
  let a : Fin (finrank K W) := ⟨0, lt_of_lt_of_le (by decide : 0 < 5) h5⟩
  obtain ⟨f, hfbase, hfgeneric⟩ :=
    exists_cubicThroughPointBasisEvaluationRationalMap p hp hp0 n y hpy j b a
  exact ⟨finrank K W, h5, b, a, f, hfbase, hfgeneric⟩

end
end PfaffianDescent.Coray
end
