import PfaffianDescent.ActualPointLocalAdjunctionSectionEvaluation
import PfaffianDescent.ActualPointOpenRestrictAdjunctionUnit

/- SOURCE ONLY / UNVERIFIED. Direct ORIGINAL local point classes match
the actual open-chart classes via the genuinely constructed point/open
pullback Iso. Its unit identity is derived upstream from actual adjunction
composition; no desired point/fiber square is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u

lemma actualPointLocalOpenRestrictionComparison
    {L : Type u} [Field L] {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (j : Spec (.of L) ⟶ Y)
    (M : X.Modules) (U : X.Opens) (hU : (j ≫ f) ⁻¹ᵁ U = ⊤)
    (z : M.val.obj (op U)) :
    (moduleSpecΓFunctor (R := .of L)).map
      (cubicClosedPointSerreSurfaceJetCotangent_pointOpenRestrictPullbackIso f j M).hom
      (actualPointLocalSectionClass (j ≫ f) M U hU z) =
    actualPointLocalSectionClass j ((Scheme.Modules.restrictFunctor f).obj M)
      (f ⁻¹ᵁ U) (by simpa only [Scheme.Hom.comp_preimage] using hU)
      (((Scheme.Modules.restrictAdjunction f).unit.app M).val.app (op U) z) := by
  rw [actualPointLocalAdjunctionSectionEvaluation, Adjunction.homEquiv_unit,
    actualPointOpenRestrictAdjunctionUnit]
  rfl

end PfaffianDescent
