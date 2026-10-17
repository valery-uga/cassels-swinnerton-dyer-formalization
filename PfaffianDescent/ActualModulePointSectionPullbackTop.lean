import PfaffianDescent.ActualModulePointSectionClass
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointChartSectionHom

/- SOURCE ONLY / UNVERIFIED. Actual point class is the genuine point
pullback's top section. This applies to ANY actual source module. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

lemma actualModulePointSectionClass_eq_pullbackTop
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (M : X.Modules) (v : schemeModuleUnit X ⟶ M) :
    actualModulePointSectionClass q M v =
      (pullbackSection q M (isIso_pullbackUnitComparison q) (M.unitHomEquiv v)).val (op ⊤) := by
  letI : IsIso (pullbackUnitComparison q) := isIso_pullbackUnitComparison q
  let P := Scheme.Modules.pullback q
  let s := pullbackSection q M (isIso_pullbackUnitComparison q) (M.unitHomEquiv v)
  have hs := pullbackSection_unitHomEquiv_symm_eq_inv q M
    (isIso_pullbackUnitComparison q) (M.unitHomEquiv v)
  rw [M.unitHomEquiv.symm_apply_apply v] at hs
  change ((P.obj M).unitHomEquiv
      (inv (pullbackUnitComparison q) ≫ P.map v)).val (op ⊤) = _
  rw [← hs, (P.obj M).unitHomEquiv.apply_symm_apply]

lemma actualModulePointChartSectionClass
    {L : Type u} [Field L] {X U : Scheme.{u}}
    (f : U ⟶ X) [IsOpenImmersion f] (j : Spec (.of L) ⟶ U)
    (M : X.Modules) (N : U.Modules)
    (e : (Scheme.Modules.restrictFunctor f).obj M ≅ N)
    (v : schemeModuleUnit X ⟶ M) (t : schemeModuleUnit U ⟶ N)
    (h : (Scheme.Modules.restrictUnitIso f).inv ≫
      (Scheme.Modules.restrictFunctor f).map v ≫ e.hom = t) :
    (moduleSpecΓFunctor (R := .of L)).map
        (cubicClosedPointSerreSurfaceJetCotangent_pointChartModuleIso f j M N e).hom
        (actualModulePointSectionClass (j ≫ f) M v) =
      actualModulePointSectionClass j N t := by
  rw [actualModulePointSectionClass_eq_pullbackTop,
    actualModulePointSectionClass_eq_pullbackTop]
  have he := cubicClosedPointSerreSurfaceJetCotangent_pointChartModuleIso_sectionHom
    f j M N e v t h
  exact congrArg (fun s => s.val (op ⊤)) he

end PfaffianDescent
