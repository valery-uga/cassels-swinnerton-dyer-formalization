import PfaffianDescent.ActualModulePointSectionPullbackTop

/- SOURCE ONLY / UNVERIFIED. Actual module point-chart comparison includes
the SAME original source equality; the section square follows by equality
transport and genuine point pullback. No extra point comparison is assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

def actualModulePointChartSourceFactorizationIso
    {L : Type u} [Field L] {X U : Scheme.{u}}
    (f : U ⟶ X) [IsOpenImmersion f] (j : Spec (.of L) ⟶ U)
    (q : Spec (.of L) ⟶ X) (hfac : j ≫ f = q)
    (M : X.Modules) (N : U.Modules)
    (e : (Scheme.Modules.restrictFunctor f).obj M ≅ N) :
    (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback j).obj N :=
  eqToIso (congrArg (fun r => (Scheme.Modules.pullback r).obj M) hfac.symm) ≪≫
    cubicClosedPointSerreSurfaceJetCotangent_pointChartModuleIso f j M N e

lemma actualModulePointChartSourceFactorization_section
    {L : Type u} [Field L] {X U : Scheme.{u}}
    (f : U ⟶ X) [IsOpenImmersion f] (j : Spec (.of L) ⟶ U)
    (q : Spec (.of L) ⟶ X) (hfac : j ≫ f = q)
    (M : X.Modules) (N : U.Modules)
    (e : (Scheme.Modules.restrictFunctor f).obj M ≅ N)
    (v : schemeModuleUnit X ⟶ M) (t : schemeModuleUnit U ⟶ N)
    (h : (Scheme.Modules.restrictUnitIso f).inv ≫
      (Scheme.Modules.restrictFunctor f).map v ≫ e.hom = t) :
    (moduleSpecΓFunctor (R := .of L)).map
      (actualModulePointChartSourceFactorizationIso f j q hfac M N e).hom
      (actualModulePointSectionClass q M v) =
    actualModulePointSectionClass j N t := by
  cases hfac
  simpa only [actualModulePointChartSourceFactorizationIso, Iso.trans_hom,
    eqToIso_refl, Iso.refl_hom, Category.id_comp] using
    actualModulePointChartSectionClass f j M N e v t h

end PfaffianDescent
