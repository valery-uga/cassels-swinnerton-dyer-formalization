import PfaffianDescent.ActualModulePointChartSourceFactorization
import PfaffianDescent.ActualPointLocalOpenRestrictionComparison
import PfaffianDescent.ActualPointLocalSectionClassNaturality

/-! SOURCE ONLY, UNVERIFIED. The actual source-factorization point Iso
acts on local sections by the actual restriction unit and module Iso. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option backward.isDefEq.respectTransparency false

lemma actualPointLocalChartSourceFactorization
    {L : Type u} [Field L] {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (j : Spec (.of L) ⟶ Y)
    (q : Spec (.of L) ⟶ X) (hfac : j ≫ f = q)
    (M : X.Modules) (N : Y.Modules)
    (e : (Scheme.Modules.restrictFunctor f).obj M ≅ N)
    (U : X.Opens) (hU : q ⁻¹ᵁ U = ⊤) (z : M.val.obj (op U)) :
    (moduleSpecΓFunctor (R := .of L)).map
      (actualModulePointChartSourceFactorizationIso f j q hfac M N e).hom
      (actualPointLocalSectionClass q M U hU z) =
    actualPointLocalSectionClass j N (f ⁻¹ᵁ U)
      (by rw [← Scheme.Hom.comp_preimage, hfac]; exact hU)
      (e.hom.val.app (op (f ⁻¹ᵁ U))
        (((Scheme.Modules.restrictAdjunction f).unit.app M).val.app (op U) z)) := by
  cases hfac
  change (moduleSpecΓFunctor (R := .of L)).map
      ((cubicClosedPointSerreSurfaceJetCotangent_pointOpenRestrictPullbackIso f j M).hom ≫
        (Scheme.Modules.pullback j).map e.hom)
      (actualPointLocalSectionClass (j ≫ f) M U hU z) = _
  rw [Functor.map_comp, ModuleCat.comp_apply,
    actualPointLocalOpenRestrictionComparison,
    actualPointLocalSectionClass_naturality]

end PfaffianDescent
