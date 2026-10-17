import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/- SOURCE ONLY / UNVERIFIED. Legitimate Gamma comparison ONLY over a field
spectrum. No full faithfulness assumption on arbitrary affine sheaves. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace PrimeSpectrum
universe u

private theorem field_basicOpen_eq_top
    {L : Type u} [Field L] (a : L) (ha : a ≠ 0) : basicOpen a = ⊤ := by
  ext x
  simp only [mem_basicOpen, Opens.mem_top, iff_true]
  have hx : x.asIdeal = ⊥ :=
    (IsSimpleOrder.eq_bot_or_eq_top x.asIdeal).resolve_right x.2.ne_top
  simpa only [hx, Ideal.mem_bot] using ha

/-- Any sheaf of modules over Spec(field) is recovered from its ACTUAL
Gamma module. Principal opens are top or bottom; the empty value is
terminal by the actual sheaf condition, not a quasicoherence certificate. -/
theorem actualFieldPointModule_fromTildeGamma_isIso
    {L : Type u} [Field L] (M : (Spec (.of L)).Modules) :
    IsIso M.fromTildeΓ := by
  rw [← isIso_iff_of_reflects_iso _ modulesSpecToSheaf]
  let phi := modulesSpecToSheaf.map M.fromTildeΓ
  have hTop : IsIso (phi.hom.app (op ⊤)) := by
    change IsIso ((modulesSpecToSheaf.map M.fromTildeΓ).hom.app (op ⊤))
    rw [← isIso_comp_left_iff
      (tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)) ⊤),
      Scheme.Modules.toOpen_fromTildeΓ_app]
    simpa using IsIso.id ((modulesSpecToSheaf.obj M).presheaf.obj (op ⊤))
  have hBot : IsIso (phi.hom.app (op ⊥)) := by
    let F := modulesSpecToSheaf.obj ((tilde.functor (.of L)).obj
      ((moduleSpecΓFunctor (R := .of L)).obj M))
    let G := modulesSpecToSheaf.obj M
    have hF := F.isTerminalOfEmpty
    have hG := G.isTerminalOfEmpty
    let inv : G.obj.obj (op ⊥) ⟶ F.obj.obj (op ⊥) := hF.from _
    refine ⟨⟨inv, ?_, ?_⟩⟩
    · exact hF.hom_ext _ _
    · exact hG.hom_ext _ _
  refine TopCat.Sheaf.isIso_iff_isIso_basis (φ := phi) isBasis_basic_opens (fun a => ?_)
  by_cases ha : a = 0
  · simpa only [ha, basicOpen_zero] using hBot
  · simpa only [field_basicOpen_eq_top a ha] using hTop

/-- Full faithfulness is DERIVED for the field-point functor via its actual
adjunction counit, rather than postulated for arbitrary sheaves. -/
def actualFieldPointModuleGamma_fullyFaithful
    {L : Type u} [Field L] :
    (moduleSpecΓFunctor (R := CommRingCat.of L)).FullyFaithful := by
  letI (M : (Spec (.of L)).Modules) : IsIso M.fromTildeΓ :=
    actualFieldPointModule_fromTildeGamma_isIso M
  letI : IsIso (tilde.adjunction (R := CommRingCat.of L)).counit :=
    NatIso.isIso_of_isIso_app _
  exact (tilde.adjunction (R := CommRingCat.of L)).fullyFaithfulROfIsIsoCounit

end PfaffianDescent
