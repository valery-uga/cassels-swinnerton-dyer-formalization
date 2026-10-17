import PfaffianDescent.LocalExtResidueInjective
import PfaffianDescent.SchemePushforwardUnitSections

/-!
# Sections of the actual point sheaf away from its support

An open disjoint from a morphism's image has zero sections of every pushed
forward module. In particular the untwisted point quotient has zero sections
on every nondistinguished member of the adapted cover.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace PfaffianDescent

universe u

set_option backward.isDefEq.respectTransparency false in
/-- Empty preimage gives zero sections of a pushed-forward module. -/
theorem schemeModulePushforward_sections_subsingleton_off_image
    {Z X : Scheme.{u}} (i : Z ⟶ X) (M : Z.Modules)
    (V : X.Opens) (hV : ∀ z : Z, i z ∉ V) :
    Subsingleton (((Scheme.Modules.pushforward i).obj M).val.obj (op V)) := by
  have hpre : (TopologicalSpace.Opens.map i.base).obj V = ⊥ := by
    ext z
    change i z ∈ V ↔ False
    exact ⟨fun hz => hV z hz, False.elim⟩
  let F : Z.toTopCat.Sheaf AddCommGrpCat.{u} :=
    (SheafOfModules.toSheaf Z.ringCatSheaf).obj M
  change Subsingleton (F.obj.obj (op ((TopologicalSpace.Opens.map i.base).obj V)))
  exact AddCommGrpCat.subsingleton_of_isZero ((F.isTerminalOfEqEmpty hpre).isZero)

set_option backward.isDefEq.respectTransparency false in
/-- The pushforward of an actual field point has zero sections on an open
avoiding that point. -/
theorem fieldPointPushforward_sections_subsingleton_away_point
    {L : Type u} [Field L] {X : Scheme.{u}} (i : Spec (.of L) ⟶ X)
    (M : (Spec (.of L)).Modules) (V : X.Opens) (hV : i default ∉ V) :
    Subsingleton (((Scheme.Modules.pushforward i).obj M).val.obj (op V)) := by
  apply schemeModulePushforward_sections_subsingleton_off_image i M V
  intro z
  have hz : z = default := Subsingleton.elim _ _
  simpa only [hz] using hV

set_option backward.isDefEq.respectTransparency false in
/-- The actual unit-twisted ideal-sequence quotient inherits the point's
section vanishing, through its constructed pushforward isomorphism. -/
theorem fieldPointUnitQuotient_sections_subsingleton_away_point
    {L : Type u} [Field L] {X : Scheme.{u}} (i : Spec (.of L) ⟶ X)
    [IsClosedImmersion i] (V : X.Opens) (hV : i default ∉ V) :
    Subsingleton ((closedImmersionIdealTwistSequence i
      (SheafOfModules.unit X.ringCatSheaf)).X₃.val.obj (op V)) := by
  let e := closedImmersionIdealTwistSequenceUnitTargetIso i
  letI := fieldPointPushforward_sections_subsingleton_away_point i
    (SheafOfModules.unit (Spec (.of L)).ringCatSheaf) V hV
  refine ⟨fun a b => ?_⟩
  have hab : e.hom.val.app (op V) a = e.hom.val.app (op V) b := Subsingleton.elim _ _
  have h := congrArg (e.inv.val.app (op V)) hab
  change (e.hom ≫ e.inv).val.app (op V) a = (e.hom ≫ e.inv).val.app (op V) b at h
  rw [e.hom_inv_id] at h
  exact h

end PfaffianDescent
