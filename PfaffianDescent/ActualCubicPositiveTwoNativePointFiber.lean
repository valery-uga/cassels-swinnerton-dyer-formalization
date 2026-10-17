import PfaffianDescent.ActualCubicPositiveTwoNativeChartTildeIso
import PfaffianDescent.AffineTildeActualPointClass

/- SOURCE ONLY / UNVERIFIED. The GENUINE Omega(2) point fiber in its actual
native O(2) chart generator, with SAME original point factorization. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def actualCubicPositiveTwoOriginalNativePointFiberEquiv
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q : Spec (.of L) ⟶ hypersurface p hp) (j : Fin 4)
    (rho : ChartRing (equationIdeal p hp) j →+* L)
    (hfac : Spec.map (CommRingCat.ofHom rho) ≫ chartι (equationIdeal p hp) j = q) :
    letI : Algebra K (ChartRing (equationIdeal p hp) j) :=
      (chartBaseMap (equationIdeal p hp) j).toAlgebra
    letI : Algebra (ChartRing (equationIdeal p hp) j) L := rho.toAlgebra
    (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback q).obj (actualCubicPositiveTwoDifferentials p hp)) ≃ₗ[L]
      L ⊗[ChartRing (equationIdeal p hp) j]
        KaehlerDifferential K (ChartRing (equationIdeal p hp) j) := by
  let I := equationIdeal p hp
  let R := ChartRing I j
  letI : Algebra K R := (chartBaseMap I j).toAlgebra
  letI : Algebra R L := rho.toAlgebra
  let qU := Spec.map (CommRingCat.ofHom rho)
  let M := actualCubicPositiveTwoDifferentials p hp
  let eChart := actualCubicPositiveTwoNativeChartTildeIso p hp j
  let eQ := ((Scheme.Modules.pullbackCongr hfac).app M).symm
  let eComp := (Scheme.Modules.pullbackComp qU (chartι I j)).symm.app M
  exact ((moduleSpecΓFunctor (R := .of L)).mapIso
    (eQ ≪≫ eComp ≪≫ (Scheme.Modules.pullback qU).mapIso eChart)).toLinearEquiv ≪≫ₗ
      affineTildeActualPointFiberEquiv (CommRingCat.ofHom rho)
        (ModuleCat.of R (KaehlerDifferential K R))

end PfaffianDescent
