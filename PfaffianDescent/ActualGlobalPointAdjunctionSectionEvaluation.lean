import PfaffianDescent.ActualModulePointSectionClass
import PfaffianDescent.BundleSectionZeroLocusNaturality

/- SOURCE ONLY / UNVERIFIED. Evaluation of the TRUE point-pullback
section after ANY module map equals evaluation of its actual adjoint.
The source is an arbitrary scheme, not assumed affine. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite BundleSectionZeroLocus
universe u
attribute [local instance] isIso_pullbackUnitComparison

lemma actualPullbackUnitComparison_adjunct {X Z : Scheme.{u}} (q : Z ⟶ X) :
    (Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _
      (pullbackUnitComparison q) =
        SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom := by
  letI : (SheafOfModules.pushforward q.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction q).isRightAdjoint
  change (SheafOfModules.pullbackPushforwardAdjunction
    q.toRingCatSheafHom).homEquiv _ _
      (SheafOfModules.pullbackObjUnitToUnit q.toRingCatSheafHom) = _
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    q.toRingCatSheafHom

lemma actualGlobalPointAdjunctionSectionEvaluation
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (M : X.Modules) (N : (Spec (.of L)).Modules)
    (v : schemeModuleUnit X ⟶ M)
    (d : (Scheme.Modules.pullback q).obj M ⟶ N) :
    (moduleSpecΓFunctor (R := .of L)).map d (actualModulePointSectionClass q M v) =
      (((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _) d).val.app
        (op ⊤) (v.val.app (op ⊤) (1 : Γ(X, ⊤))) := by
  let P := Scheme.Modules.pullback q
  let Q := Scheme.Modules.pushforward q
  let O : X.Modules := schemeModuleUnit X
  let adj := Scheme.Modules.pullbackPushforwardAdjunction q
  let a := adj.unit.app O
  let c := pullbackUnitComparison q
  have hq : a ≫ Q.map c =
      SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom := by
    exact actualPullbackUnitComparison_adjunct q
  have hc : c.val.app (op ⊤) (a.val.app (op ⊤) (1 : Γ(X, ⊤))) =
      (1 : Γ(Spec (.of L), ⊤)) := by
    have h := congrArg (fun m => m.val.app (op ⊤) (1 : Γ(X, ⊤))) hq
    change c.val.app (op ⊤) (a.val.app (op ⊤) (1 : Γ(X, ⊤))) =
      q.appTop (1 : Γ(X, ⊤)) at h
    exact h.trans (map_one q.appTop.hom)
  have hi := congrArg (fun z => (inv c).val.app (op ⊤) z) hc
  have huv : a.val.app (op ⊤) (1 : Γ(X, ⊤)) =
      (inv c).val.app (op ⊤) (1 : Γ(Spec (.of L), ⊤)) := by
    have hcancel := congrArg (fun m => m.val.app (op ⊤)
      (a.val.app (op ⊤) (1 : Γ(X, ⊤)))) (IsIso.hom_inv_id c)
    exact hcancel.symm.trans hi
  have hv := adj.homEquiv_naturality_left v d
  have hunit := congrArg (fun m => m.val.app (op ⊤) (1 : Γ(X, ⊤))) hv
  rw [Adjunction.homEquiv_unit] at hunit
  change d.val.app (op ⊤)
      ((P.map v).val.app (op ⊤) (a.val.app (op ⊤) (1 : Γ(X, ⊤)))) =
    ((adj.homEquiv _ _) d).val.app (op ⊤)
      (v.val.app (op ⊤) (1 : Γ(X, ⊤))) at hunit
  rw [huv] at hunit
  exact hunit

end PfaffianDescent
