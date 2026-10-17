import PfaffianDescent.ActualOpenImmersionDifferentialSheafIso
import PfaffianDescent.ActualPositiveTwistPullbackTensorIso
import PfaffianDescent.ActualPointTwistUntwistRatio
import PfaffianDescent.ActualModulePointChartSourceFactorization
import PfaffianDescent.ActualAffineSchemeDifferentialPointFiber

/-! SOURCE ONLY / UNVERIFIED contingency028. One shared arbitrary-chart
factory for the TRUE Omega(2) point-to-Kaehler map. The original producer
and comparison both apply this same constant; no original point choice,
original trivialization, desired comparison or coefficient certificate is
constructed or assumed by this generic definition. The original caller
supplies its internally constructed chart/factorization/trivialization. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The literal genuine tensor pullback, point untwist, open differential
chart, base equality and affine differential fiber composition. -/
def actualCubicPositiveTwoChartContractedNativeDifferentialMap
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a : Fin 4)
    (rho : ChartRing (equationIdeal p hp) a →+* L)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (hfac : Spec.map (CommRingCat.ofHom rho) ≫ chartι (equationIdeal p hp) a = q)
    (eT : (Scheme.Modules.pullback q).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf) :
    let I := equationIdeal p hp
    let R := ChartRing I a
    letI : Algebra K R := (chartBaseMap I a).toAlgebra
    letI : Algebra R L := rho.toAlgebra
    (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback q).obj
        (schemeModuleTensor (schemeRelativeDifferentials (toBase I))
          (positiveSheafOfModules (grading I) 2))) →ₗ[L]
            (L ⊗[R] KaehlerDifferential K R) := by
  dsimp only
  let I := equationIdeal p hp
  let R := ChartRing I a
  letI : Algebra K R := (chartBaseMap I a).toAlgebra
  letI : Algebra R L := rho.toAlgebra
  let f := chartι I a
  let j := Spec.map (CommRingCat.ofHom rho)
  let T := positiveSheafOfModules (grading I) 2
  let W := schemeRelativeDifferentials (toBase I)
  let Et := actualModulePointChartSourceFactorizationIso f j q hfac
    W (schemeRelativeDifferentials (f ≫ toBase I))
    (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
  let Ebase := (Scheme.Modules.pullback j).mapIso
    (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I a)))
  let c := (actualPositiveTwistPullbackTensorIso I q W 2).hom ≫
    (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
      ((Scheme.Modules.pullback q).obj T) eT).hom
  exact (actualAffineSchemeDifferentialPointFiberEquiv (k := K) rho).toLinearMap.comp
    ((moduleSpecΓFunctor (R := .of L)).map (c ≫ Et.hom ≫ Ebase.hom)).hom

/-- Preserve the exact literal map at ordinary cubic chart/field-point
data. This proved formula records all actual morphisms before original
quartic choice and original point-trivialization specialization. -/
lemma actualCubicPositiveTwoChartContractedNativeDifferentialMap_eq_formula
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a : Fin 4)
    (rho : ChartRing (equationIdeal p hp) a →+* L)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (hfac : Spec.map (CommRingCat.ofHom rho) ≫ chartι (equationIdeal p hp) a = q)
    (eT : (Scheme.Modules.pullback q).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf) :
    let I := equationIdeal p hp
    let R := ChartRing I a
    letI : Algebra K R := (chartBaseMap I a).toAlgebra
    letI : Algebra R L := rho.toAlgebra
    let f := chartι I a
    let j := Spec.map (CommRingCat.ofHom rho)
    let W := schemeRelativeDifferentials (toBase I)
    let T := positiveSheafOfModules (grading I) 2
    let Et := actualModulePointChartSourceFactorizationIso f j q hfac
      W (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I a)))
    let c := (actualPositiveTwistPullbackTensorIso I q W 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T) eT).hom
    actualCubicPositiveTwoChartContractedNativeDifferentialMap p hp a rho q hfac eT =
      (actualAffineSchemeDifferentialPointFiberEquiv (k := K) rho).toLinearMap.comp
        ((moduleSpecΓFunctor (R := .of L)).map (c ≫ Et.hom ≫ Ebase.hom)).hom := by
  rfl

end PfaffianDescent
