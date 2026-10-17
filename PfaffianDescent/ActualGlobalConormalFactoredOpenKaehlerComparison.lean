import PfaffianDescent.ActualGlobalConormalAffineOpenKaehlerComparison
import PfaffianDescent.ActualFactoredIdealOpenRestrictionIso

/-! SOURCE ONLY, UNVERIFIED. The whole global conormal map for the actual
point q agrees with the affine Kaehler map using its literal chart
factorization. No differential or fiber-square certificate is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false

lemma actualGlobalConormalFactoredOpenKaehlerComparison
    {k R L : Type u} [CommRing k] [CommRing R] [Field L] [Algebra k R]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) (f : Spec (.of R) ⟶ X)
    [IsOpenImmersion f] (rho : R →+* L) (hrho : Function.Surjective rho)
    (q : Spec (.of L) ⟶ X) [IsClosedImmersion q]
    (hfac : Spec.map (CommRingCat.ofHom rho) ≫ f = q)
    (hBase : f ≫ g = Spec.map (CommRingCat.ofHom (algebraMap k R))) :
    letI : Algebra R L := rho.toAlgebra
    let j := Spec.map (CommRingCat.ofHom rho)
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ hrho
    let Es := actualModulePointChartSourceFactorizationIso f j q hfac
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q hfac)
    let Et := actualModulePointChartSourceFactorizationIso f j q hfac
      (schemeRelativeDifferentials g) (schemeRelativeDifferentials (f ≫ g))
      (actualOpenImmersionDifferentialSheafRestrictionIso f g).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials hBase))
    ((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap g q ≫ Et.hom ≫ Ebase.hom)).hom =
      (actualAffineConormalDifferentialFiberMap (k := k) rho hrho).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom := by
  subst q
  exact actualGlobalConormalAffineOpenKaehlerComparison g f rho hrho hBase

end PfaffianDescent
