import PfaffianDescent.ActualOpenImmersionDifferentialSheafIso
import AllCharacteristics.HomogeneousProjective
import AllCharacteristics.CoordinateCharts

/- SOURCE ONLY / UNVERIFIED. The SAME native Spec(chart ring) and actual
cubic structure morphism are retained in the genuine Ω chart comparison. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- No smoothness, rank, chart-square or sheaf-comparison certificate is
needed: the actual chart-to-base identity is derived internally. -/
def actualCubicNativeChartDifferentialSheafIso
    {K : Type u} [CommRing K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4) :
    letI : Algebra K (ChartRing (equationIdeal p hp) j) :=
      (chartBaseMap (equationIdeal p hp) j).toAlgebra
    schemeRelativeDifferentials (Spec.map (CommRingCat.ofHom
      (algebraMap K (ChartRing (equationIdeal p hp) j)))) ≅
      (Scheme.Modules.pullback (chartι (equationIdeal p hp) j)).obj
        (schemeRelativeDifferentials (hypersurfaceToBase p hp)) := by
  let I := equationIdeal p hp
  letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
  have hs : chartι I j ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K (ChartRing I j))) := chartι_toBase I j
  exact (eqToIso (congrArg schemeRelativeDifferentials hs.symm)) ≪≫
    actualOpenImmersionDifferentialSheafPullbackIso (chartι I j) (hypersurfaceToBase p hp)

end PfaffianDescent
