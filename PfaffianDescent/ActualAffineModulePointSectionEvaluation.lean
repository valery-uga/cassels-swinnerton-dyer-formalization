import PfaffianDescent.ActualModulePointSectionClass
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentAffineEvaluationPullbackSection

/- SOURCE ONLY / UNVERIFIED. Actual morphism-valued point-section class
and the installed actual affine evaluation are the SAME map, not certificates. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

lemma actualAffineModulePointSectionClass_eq_evaluation
    {R L : Type u} [CommRing R] [Field L] (rho : R →+* L)
    (M : (Spec (.of R)).Modules) (t : schemeModuleUnit (Spec (.of R)) ⟶ M) :
    actualModulePointSectionClass (Spec.map (CommRingCat.ofHom rho)) M t =
    (cubicClosedPointSerreSurfaceJetCotangent_affineModulePointEvaluation
      (CommRingCat.ofHom rho) M).hom
      (t.val.app (op ⊤) (1 : Γ(Spec (.of R), ⊤))) := by
  let f := Spec.map (CommRingCat.ofHom rho)
  letI : IsIso (pullbackUnitComparison f) := isIso_pullbackUnitComparison f
  let P := Scheme.Modules.pullback f
  let s := pullbackSection f M (isIso_pullbackUnitComparison _) (M.unitHomEquiv t)
  have hs := pullbackSection_unitHomEquiv_symm_eq_inv f M
    (isIso_pullbackUnitComparison _) (M.unitHomEquiv t)
  have hcancel : M.unitHomEquiv.symm (M.unitHomEquiv t) = t :=
    M.unitHomEquiv.symm_apply_apply t
  have hs' : (P.obj M).unitHomEquiv.symm s =
      inv (pullbackUnitComparison f) ≫ P.map t :=
    hs.trans (congrArg (fun v => inv (pullbackUnitComparison f) ≫ P.map v) hcancel)
  have heval : (P.obj M).unitHomEquiv
      (inv (pullbackUnitComparison f) ≫ P.map t) = s :=
    (congrArg (P.obj M).unitHomEquiv hs').symm.trans
      ((P.obj M).unitHomEquiv.apply_symm_apply s)
  have hclass : actualModulePointSectionClass f M t = s.val (op ⊤) := by
    exact congrArg (fun v => v.val (op ⊤)) heval
  exact hclass.trans
    (cubicClosedPointSerreSurfaceJetCotangent_affineModulePointEvaluation_pullbackSection rho M t).symm

end PfaffianDescent
