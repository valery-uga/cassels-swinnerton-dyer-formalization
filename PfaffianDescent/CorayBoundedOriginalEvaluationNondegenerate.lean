import PfaffianDescent.CorayBoundedOriginalEvaluationRationalMap
import PfaffianDescent.CorayProjectiveEvaluationLinearForm

/-! Source-only / unverified. The SAME bounded-family evaluation admits
no nonzero original-K linear equation, including in its actual normalized
projective chart. This is not a dimension or differential-rank theorem. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped AlgebraicGeometry PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K L : Type u} [Field K] [CommRing L] [Algebra K L]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
  [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
variable (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
  (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]

include hp0 in
/-- Injectivity of the actual original-K generic evaluation preserves
all original-K linear relations of the actual section basis. -/
theorem cubicThroughPointBasisGenericCoordinates_relation_iff {m : ℕ}
    (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (c : Fin m → K) :
    (∑ i, c i • cubicThroughPointBasisGenericCoordinates p hp n y hpy j b i = 0) ↔
      c = 0 := by
  exact evaluatedBasis_relation_iff
    (K := K) (V := cubicThroughCoordinateSections p hp n y hpy)
    (B := SchemeFunctionFieldOver (hypersurfaceToBase p hp)) (ι := Fin m)
    b (cubicThroughPointGenericLinearEvaluation p hp n y hpy j)
    (cubicThroughPointGenericLinearEvaluation_injective p hp n y hpy j hp0) c

/-- The actual chart map kills an original-K linear hyperplane equation
exactly when all its original coefficients vanish. No image dimension or
separability assumption is used. -/
theorem cubicThroughPointBasisGenericChartMap_linearForm_zero_iff {m : ℕ}
    (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) (c : Fin m → K) :
    cubicThroughPointBasisGenericChartMap p hp hp0 n y hpy j b a
      (projectiveChartLinearForm a c) = 0 ↔ c = 0 := by
  change projectiveEvaluationChartMap
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp))
    (cubicThroughPointBasisGenericCoordinates p hp n y hpy j b) a
    (cubicThroughPointBasisGenericCoordinates_ne_zero p hp hp0 n y hpy j b a)
    (projectiveChartLinearForm a c) = 0 ↔ c = 0
  refine (projectiveEvaluationChartMap_linearForm_zero_iff
    (K := K) (F := (hypersurface p hp).functionField) (σ := Fin m)
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp))
    (cubicThroughPointBasisGenericCoordinates p hp n y hpy j b) a
    (cubicThroughPointBasisGenericCoordinates_ne_zero p hp hp0 n y hpy j b a)
    c).trans ?_
  change (∑ i, c i • cubicThroughPointBasisGenericCoordinates p hp n y hpy j b i = 0) ↔
    c = 0
  exact cubicThroughPointBasisGenericCoordinates_relation_iff p hp hp0 n y hpy j b c

end PfaffianDescent.Coray
end
