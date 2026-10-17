import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentAffineEvaluationSection

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual affine point evaluation is the top section of the native
point pullback, for the actual section represented by t. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_affineModulePointEvaluation_pullbackSection
    {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B)
    (M : (Spec (CommRingCat.of A)).Modules)
    (t : SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf ⟶ M) :
    (cubicClosedPointSerreSurfaceJetCotangent_affineModulePointEvaluation
      (CommRingCat.ofHom g) M).hom
      (t.val.app (op ⊤) (1 : Γ(Spec (CommRingCat.of A), ⊤))) =
    (pullbackSection (Spec.map (CommRingCat.ofHom g)) M
      (isIso_pullbackUnitComparison _) (M.unitHomEquiv t)).val (op ⊤) := by
  let f := Spec.map (CommRingCat.ofHom g)
  let P := Scheme.Modules.pullback f
  let s := pullbackSection f M (isIso_pullbackUnitComparison _) (M.unitHomEquiv t)
  have hs := pullbackSection_unitHomEquiv_symm_eq_inv f M
    (isIso_pullbackUnitComparison _) (M.unitHomEquiv t)
  rw [Equiv.symm_apply_apply] at hs
  have htop := congrArg (fun a => a.val.app (op ⊤)
    (1 : Γ(Spec (CommRingCat.of B), ⊤))) hs
  have hu := congrArg (fun a => a.val (op ⊤)) ((P.obj M).unitHomEquiv.apply_symm_apply s)
  have h := (SheafOfModules.unitHomEquiv_apply_coe (P.obj M)
    ((P.obj M).unitHomEquiv.symm s) (op ⊤)).symm.trans hu
  exact (cubicClosedPointSerreSurfaceJetCotangent_affineModulePointEvaluation_sectionHom g M t).trans
    (htop.symm.trans h)

end PfaffianDescent
