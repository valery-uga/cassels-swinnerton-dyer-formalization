import PfaffianDescent.ActualPositiveTwistChartBasisUnitAction
import PfaffianDescent.ActualPullbackTrivializationBasisComposition
import PfaffianDescent.ActualPositiveTwistNativeChartUnitIso

/- SOURCE ONLY / UNVERIFIED. Infer the proof's actual equality from the
accepted unit-comparison composition law. This keeps the SAME standard
chart, homogeneous basis, and native unit-Iso composition. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory BundleSectionZeroLocus
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The coefficient-one identity for the actual native twist trivialization,
with its equality type inferred from the actual composition law. -/
def actualPositiveTwistNativeChartUnitIso_basis
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (a : Fin 4) (m : ℕ) :=
  let ell : grading (R := K) (σ := Fin 4) I 1 :=
    ⟨coordinate (R := K) (σ := Fin 4) I a,
      coordinate_mem (R := K) (σ := Fin 4) I a⟩
  let U := Proj.basicOpen (grading (R := K) (σ := Fin 4) I)
    (coordinate (R := K) (σ := Fin 4) I a)
  let e := Proj.basicOpenIsoSpec (grading (R := K) (σ := Fin 4) I)
    (coordinate (R := K) (σ := Fin 4) I a)
    (coordinate_mem (R := K) (σ := Fin 4) I a) (by decide : 0 < 1)
  let T := positiveSheafOfModules (grading (R := K) (σ := Fin 4) I) m
  let eU : (Scheme.Modules.pullback U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app T ≪≫
      actualPositiveTwistChartUnitIso (K := K) I ell m
  actualPullbackTrivializationBasisComposition e.inv U.ι T
    (actualPositiveTwistChartBasisInvHom (K := K) I ell m) eU
    (actualPositiveTwistChartPullbackUnitIso_basis (K := K) I ell m)

end PfaffianDescent
