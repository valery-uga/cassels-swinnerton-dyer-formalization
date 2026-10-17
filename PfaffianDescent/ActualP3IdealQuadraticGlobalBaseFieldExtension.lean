import PfaffianDescent.ActualP3IdealQuadraticGlobalBase
import PfaffianDescent.IntrinsicFiniteProjectiveQuadraticFieldExtension

/-! Field extension of the quadratic series and base ideal defined using
genuine ideal-sheaf global sections of the same finite embedded subscheme.
The entire scheme structure is retained, including nilpotents. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem p3ActualIdealQuadraticGlobalBaseIdeal_actual_fieldExtension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i] [IsFinite (i ≫ ambientToBase)] :
    letI : IsClosedImmersion (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i) :=
      canonicalProjectiveFieldBaseChangeEmbedding_isClosedImmersion i
    p3ActualIdealQuadraticGlobalBaseIdeal
        (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i) =
      HomogeneousIdeal.map (ambientCoefficientGradedRingHom (algebraMap k K))
        (p3ActualIdealQuadraticGlobalBaseIdeal i) := by
  letI : IsClosedImmersion (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i) :=
    canonicalProjectiveFieldBaseChangeEmbedding_isClosedImmersion i
  rw [p3ActualIdealQuadraticGlobalBaseIdeal_eq_intrinsic,
    p3ActualIdealQuadraticGlobalBaseIdeal_eq_intrinsic]
  exact intrinsicFullQuadraticBaseIdeal_actual_fieldExtension i

theorem p3ActualIdealQuadraticHZero_actual_fieldExtension_finrank
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i] [IsFinite (i ≫ ambientToBase)] :
    letI : IsClosedImmersion (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i) :=
      canonicalProjectiveFieldBaseChangeEmbedding_isClosedImmersion i
    finrank K (ActualP3IdealQuadraticHZero
        (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i)) =
      finrank k (ActualP3IdealQuadraticHZero i) := by
  letI : IsClosedImmersion (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i) :=
    canonicalProjectiveFieldBaseChangeEmbedding_isClosedImmersion i
  change finrank K (SchemeModuleGlobalSectionsOver _ _) =
    finrank k (SchemeModuleGlobalSectionsOver _ _)
  rw [p3ActualIdealQuadratic_finrank_eq_intrinsic,
    p3ActualIdealQuadratic_finrank_eq_intrinsic]
  exact intrinsicFullQuadraticSystem_actual_fieldExtension_finrank i

end PfaffianDescent
