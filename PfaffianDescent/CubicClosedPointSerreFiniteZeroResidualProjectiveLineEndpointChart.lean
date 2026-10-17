import PfaffianDescent.ProjectiveLinePoints

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

def cubicClosedPointSerreFiniteZeroResidual_endpointChart
    (K : Type u) [Field K] (b : Bool) :
    Spec (.of K) ⟶ (lineProjOpenCover K).X b :=
  grassmannianChartEvaluation K (lineChartMatrix K 0) ≫
    (lineGrassmannianProjChartIso K b).inv

theorem cubicClosedPointSerreFiniteZeroResidual_endpointChart_toLine
    (K : Type u) [Field K] (b : Bool) :
    cubicClosedPointSerreFiniteZeroResidual_endpointChart K b ≫
      (lineProjOpenCover K).f b = projectiveLineEndpoint K b := by
  change (_ ≫ (lineGrassmannianProjChartIso K b).inv) ≫ chartι (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) b =
    grassmannianChartEvaluation K (lineChartMatrix K 0) ≫
      grassmannianChartι K (lineChartPermutation b) ≫ lineGrassmannianToProj K
  rw [Category.assoc, ← lineGrassmannianChart_toProj]

theorem cubicClosedPointSerreFiniteZeroResidual_endpointChart_coordinate
    (K : Type u) [Field K] (b : Bool) :
    affineFunctionHom (cubicClosedPointSerreFiniteZeroResidual_endpointChart K b)
      (chartCoordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) b (!b)) = 0 := by
  rw [cubicClosedPointSerreFiniteZeroResidual_endpointChart,
    lineGrassmannianProjChartIso_inv_coordinate]
  simp only [Bool.not_eq_self, ↓reduceIte, grassmannianChartFunctions]
  unfold grassmannianChartEvaluation affineFunctionHom
  rw [← Scheme.ΓSpecIso_inv_naturality]
  change (Scheme.ΓSpecIso (.of K)).inv.hom
    ((MvPolynomial.aeval (R := K) (fun ij : Fin 1 × Fin 1 =>
      lineChartMatrix K 0 ij.1 ij.2)).toRingHom (MvPolynomial.X (0, 0))) = 0
  simp [lineChartMatrix]

end PfaffianDescent
