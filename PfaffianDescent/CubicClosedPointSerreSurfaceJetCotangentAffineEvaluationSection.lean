import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentAffineEvaluationNaturality
import PfaffianDescent.BundleSectionZeroLocusNaturality

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] isIso_pullbackUnitComparison

/-- Actual affine point evaluation agrees with the literal section morphism
pulled to the point, with its native pullback-unit coordinate. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_affineModulePointEvaluation_sectionHom
    {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B)
    (M : (Spec (CommRingCat.of A)).Modules)
    (t : SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf ⟶ M) :
    (cubicClosedPointSerreSurfaceJetCotangent_affineModulePointEvaluation
      (CommRingCat.ofHom g) M).hom
      (t.val.app (op ⊤) (1 : Γ(Spec (CommRingCat.of A), ⊤))) =
    (inv (pullbackUnitComparison (Spec.map (CommRingCat.ofHom g))) ≫
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map t).val.app (op ⊤)
        (1 : Γ(Spec (CommRingCat.of B), ⊤)) := by
  let f := Spec.map (CommRingCat.ofHom g)
  let O : (Spec (CommRingCat.of A)).Modules := SheafOfModules.unit _
  let P := Scheme.Modules.pullback f
  let Q := Scheme.Modules.pushforward f
  let a := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app O
  let c := pullbackUnitComparison f
  have hq : a ≫ Q.map c = SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    affineCanonicalPullbackUnit_adjunct g
  have hqv := congrArg (fun m => m.val.app (op ⊤)
    (1 : Γ(Spec (CommRingCat.of A), ⊤))) hq
  have hc : c.val.app (op ⊤)
      (a.val.app (op ⊤) (1 : Γ(Spec (CommRingCat.of A), ⊤))) =
      (1 : Γ(Spec (CommRingCat.of B), ⊤)) := by
    change c.val.app (op ⊤)
      (a.val.app (op ⊤) (1 : Γ(Spec (CommRingCat.of A), ⊤))) =
      f.appTop (1 : Γ(Spec (CommRingCat.of A), ⊤)) at hqv
    exact hqv.trans (map_one f.appTop.hom)
  have hi := congrArg (fun z => (inv c).val.app (op ⊤) z) hc
  have huv : a.val.app (op ⊤) (1 : Γ(Spec (CommRingCat.of A), ⊤)) =
      (inv c).val.app (op ⊤) (1 : Γ(Spec (CommRingCat.of B), ⊤)) := by
    have hcancel := congrArg (fun m => m.val.app (op ⊤)
      (a.val.app (op ⊤) (1 : Γ(Spec (CommRingCat.of A), ⊤)))) (IsIso.hom_inv_id c)
    exact hcancel.symm.trans hi
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality t
  have hnv := congrArg (fun m => m.val.app (op ⊤)
    (1 : Γ(Spec (CommRingCat.of A), ⊤))) hn
  exact hnv.trans (congrArg (fun z => (P.map t).val.app (op ⊤) z) huv)

end PfaffianDescent
