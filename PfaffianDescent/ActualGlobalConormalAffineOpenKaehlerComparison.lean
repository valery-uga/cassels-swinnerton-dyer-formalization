import PfaffianDescent.ActualGlobalConormalAffineOpenFullMapSquare
import PfaffianDescent.ActualAffineGlobalConormalDifferentialFiberComparison

/-! SOURCE ONLY, UNVERIFIED. Compare the whole original/global conormal
differential with the actual affine Kaehler fiber map. The only base-square
input is the literal chart-to-ground-field morphism, not a differential or
fiber comparison; the original projective chart caller derives it. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false

/-- Equality transport for the actual conormal map, proved with independent
base morphisms before specializing to a composite chart morphism. -/
private lemma actualGlobalConormalBaseTransport001
    {k : Type u} [CommRing k] {Y Z : Scheme.{u}}
    (g g' : Y ⟶ Spec (.of k)) (q : Z ⟶ Y) [IsClosedImmersion q]
    (h : g = g') :
    actualGlobalClosedConormalDifferentialMap g q ≫
      ((Scheme.Modules.pullback q).mapIso
        (eqToIso (congrArg schemeRelativeDifferentials h))).hom =
      actualGlobalClosedConormalDifferentialMap g' q := by
  cases h
  simp

lemma actualGlobalConormalAffineOpenKaehlerComparison
    {k R L : Type u} [CommRing k] [CommRing R] [Field L] [Algebra k R]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) (f : Spec (.of R) ⟶ X)
    [IsOpenImmersion f] (rho : R →+* L) (hrho : Function.Surjective rho)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom rho) ≫ f)]
    (hBase : f ≫ g = Spec.map (CommRingCat.ofHom (algebraMap k R))) :
    letI : Algebra R L := rho.toAlgebra
    let j := Spec.map (CommRingCat.ofHom rho)
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ hrho
    let J := closedImmersionModule (j ≫ f)
    let Es := actualModulePointChartSourceFactorizationIso f j (j ≫ f) rfl
      J (closedImmersionModule j)
      (cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso f j)
    let Et := actualModulePointChartSourceFactorizationIso f j (j ≫ f) rfl
      (schemeRelativeDifferentials g) (schemeRelativeDifferentials (f ≫ g))
      (actualOpenImmersionDifferentialSheafRestrictionIso f g).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials hBase))
    ((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap g (j ≫ f) ≫ Et.hom ≫ Ebase.hom)).hom =
      (actualAffineConormalDifferentialFiberMap (k := k) rho hrho).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom := by
  dsimp only
  letI : Algebra R L := rho.toAlgebra
  let j := Spec.map (CommRingCat.ofHom rho)
  letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ hrho
  let G := moduleSpecΓFunctor (R := .of L)
  let Es := actualModulePointChartSourceFactorizationIso f j (j ≫ f) rfl
    (closedImmersionModule (j ≫ f)) (closedImmersionModule j)
    (cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso f j)
  let Et := actualModulePointChartSourceFactorizationIso f j (j ≫ f) rfl
    (schemeRelativeDifferentials g) (schemeRelativeDifferentials (f ≫ g))
    (actualOpenImmersionDifferentialSheafRestrictionIso f g).symm
  let Ebase := (Scheme.Modules.pullback j).mapIso
    (eqToIso (congrArg schemeRelativeDifferentials hBase))
  let Dg := actualGlobalClosedConormalDifferentialMap g (j ≫ f)
  let Dy := actualGlobalClosedConormalDifferentialMap (f ≫ g) j
  let Da := actualGlobalClosedConormalDifferentialMap
    (Spec.map (CommRingCat.ofHom (algebraMap k R))) j
  have hWhole := actualGlobalConormalAffineOpenFullMapSquare g f rho hrho
  have hAffine := actualAffineGlobalConormalDifferentialFiberComparison (k := k) rho hrho
  have hTransport : actualGlobalClosedConormalDifferentialMap (f ≫ g) j ≫
      ((Scheme.Modules.pullback j).mapIso
        (eqToIso (congrArg schemeRelativeDifferentials hBase))).hom =
      actualGlobalClosedConormalDifferentialMap
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) j := by
    exact actualGlobalConormalBaseTransport001 (f ≫ g)
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) j hBase
  change (G.map (Dg ≫ Et.hom ≫ Ebase.hom)).hom =
    (actualAffineConormalDifferentialFiberMap (k := k) rho hrho).comp (G.map Es.hom).hom
  calc
    _ = (G.map Ebase.hom).hom.comp (G.map (Dg ≫ Et.hom)).hom := by
      rw [← Category.assoc, Functor.map_comp]
      rfl
    _ = (G.map Ebase.hom).hom.comp (G.map (Es.hom ≫ Dy)).hom := by
      rw [hWhole]
    _ = (G.map (Es.hom ≫ Da)).hom := by
      apply LinearMap.ext
      intro z
      change G.map Ebase.hom (G.map (Es.hom ≫ Dy) z) = G.map (Es.hom ≫ Da) z
      rw [← ModuleCat.comp_apply, ← Functor.map_comp, Category.assoc, hTransport]
    _ = _ := by
      rw [Functor.map_comp]
      change (G.map Da).hom.comp (G.map Es.hom).hom = _
      rw [hAffine]

end PfaffianDescent
