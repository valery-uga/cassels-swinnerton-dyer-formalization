import PfaffianDescent.ActualOpenImmersionDifferentialSheafIso
import PfaffianDescent.CorayPlaneCubicJacobianSmooth

/-! SOURCE ONLY173. The actual normalized Fin3 cubic chart belongs to
the SAME original relative differential sheaf. Uses the existing generic
open-immersion producer; no new differential-sheaf comparison premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Exact native scheme chart comparison for the ORIGINAL Fin3 equation,
over the ORIGINAL coefficient field/ring. Equation, chart and base maps
are retained rather than replaced by an abstract genus-one curve. -/
def actualPlaneCubicNativeChartDifferentialSheafIso173
    {K : Type u} [CommRing K]
    (p : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 3) (j : Fin 3) :
    letI : Algebra K (ChartRing (equationIdeal p hp) j) :=
      (chartBaseMap (equationIdeal p hp) j).toAlgebra
    schemeRelativeDifferentials (Spec.map (CommRingCat.ofHom
      (algebraMap K (ChartRing (equationIdeal p hp) j)))) ≅
      (Scheme.Modules.pullback (chartι (equationIdeal p hp) j)).obj
        (schemeRelativeDifferentials (hypersurfaceToBase p hp)) := by
  let I := equationIdeal p hp
  letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
  have hbase : chartι I j ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K (ChartRing I j))) := chartι_toBase I j
  exact (eqToIso (congrArg schemeRelativeDifferentials hbase.symm)) ≪≫
    actualOpenImmersionDifferentialSheafPullbackIso (chartι I j) (hypersurfaceToBase p hp)

end PfaffianDescent.Coray
