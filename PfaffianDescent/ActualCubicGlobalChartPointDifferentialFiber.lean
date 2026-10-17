import PfaffianDescent.ActualCubicNativeChartDifferentialSheafIso
import PfaffianDescent.ActualAffineSchemeDifferentialPointFiber

/- SOURCE ONLY / UNVERIFIED. The fiber of the SAME global cubic Ω at
an actual native-chart point is the genuine Kähler tensor fiber. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def actualCubicGlobalChartPointDifferentialFiberEquiv
    {K L : Type u} [CommRing K] [CommRing L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (ρ : ChartRing (equationIdeal p hp) j →+* L) :
    letI : Algebra K (ChartRing (equationIdeal p hp) j) :=
      (chartBaseMap (equationIdeal p hp) j).toAlgebra
    letI : Algebra (ChartRing (equationIdeal p hp) j) L := ρ.toAlgebra
    (moduleSpecΓFunctor (R := CommRingCat.of L)).obj
      ((Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom ρ) ≫ chartι (equationIdeal p hp) j)).obj
          (schemeRelativeDifferentials (hypersurfaceToBase p hp))) ≃ₗ[L]
      L ⊗[ChartRing (equationIdeal p hp) j]
        KaehlerDifferential K (ChartRing (equationIdeal p hp) j) := by
  let I := equationIdeal p hp
  letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : Algebra (ChartRing I j) L := ρ.toAlgebra
  let z := Spec.map (CommRingCat.ofHom ρ)
  let Ω := schemeRelativeDifferentials (hypersurfaceToBase p hp)
  let e₁ := ((Scheme.Modules.pullbackComp z (chartι I j)).app Ω).symm
  let e₂ := (Scheme.Modules.pullback z).mapIso
    (actualCubicNativeChartDifferentialSheafIso p hp j).symm
  exact ((moduleSpecΓFunctor (R := CommRingCat.of L)).mapIso (e₁ ≪≫ e₂)).toLinearEquiv ≪≫ₗ
    actualAffineSchemeDifferentialPointFiberEquiv (k := K) ρ

end PfaffianDescent
