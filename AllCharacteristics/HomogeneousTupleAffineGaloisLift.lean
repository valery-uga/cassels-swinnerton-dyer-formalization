import AllCharacteristics.HomogeneousTupleFiniteFieldLift
import AllCharacteristics.ProjectiveTupleFieldPointAffineChart

/-!
# Affine Galois lifts of rational unordered homogeneous tuples

A rational point of the full unordered tuple quotient can be lifted over a
finite Galois extension and both the lift and the rational quotient point can
be placed in one concrete common-affine invariant-quotient chart.
-/

open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics
namespace HomogeneousProjective

universe u

variable {K : Type u} [Field K] [CharZero K]
variable {sigma : Type} [Finite sigma]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal
  (MvPolynomial.homogeneousSubmodule sigma K)) (n : ℕ)

/-- The local invariant quotient chart in the full homogeneous tuple
quotient.  The projective separatedness instance is installed internally so
the chart can be named in theorem statements. -/
noncomputable def tupleQuotientAffineChart
    (U : (scheme I).affineOpens) :
    commonOpenTupleQuotient (toBase I) U.val n ⟶ tupleQuotient I n := by
  letI : (scheme I).IsSeparated :=
    inferInstanceAs ((Proj (grading I)).IsSeparated)
  exact commonOpenTupleQuotientGluedChart (toBase I) n U

/-- A rational unordered tuple admits an ordered lift over a finite Galois
extension inside one affine quotient chart. -/
theorem tupleQuotient_exists_finiteGalois_affineChartLift
    (c : Spec (.of K) ⟶ tupleQuotient I n)
    (hc : c ≫ tupleQuotientToBase I n = 𝟙 _) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : FiniteDimensional K L) (_ : IsGalois K L)
      (U : (scheme I).affineOpens)
      (aU : Spec (.of L) ⟶
        (orderedFamilyCommonOpen (toBase I) U.val n).toScheme)
      (cU : Spec (.of K) ⟶ commonOpenTupleQuotient (toBase I) U.val n),
      cU ≫ tupleQuotientAffineChart I n U = c ∧
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ cU =
          aU ≫ commonOpenTupleQuotientMap (toBase I) U.val n U.property ∧
      cU ≫ commonOpenTupleQuotientToBase (toBase I) U.val n = 𝟙 _ := by
  obtain ⟨L, _, _, _, _, a, hquot, -⟩ :=
    tupleQuotient_exists_finiteGalois_orderedLift I n c hc
  obtain ⟨U, aU, cU, -, hcU, hlocal, hcUbase⟩ :=
    exists_projectiveTuple_fieldPoint_affineChart
      (grading I) (toBase I) n (𝟙 _) c hc a hquot
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    U, aU, cU, ?_, hlocal, hcUbase⟩
  letI : (scheme I).IsSeparated :=
    inferInstanceAs ((Proj (grading I)).IsSeparated)
  change cU ≫ commonOpenTupleQuotientGluedChart (toBase I) n U = c
  exact hcU

end HomogeneousProjective
end AllCharacteristics
