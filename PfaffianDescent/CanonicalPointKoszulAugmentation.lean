import PfaffianDescent.FieldPointKoszulGeneratorIdentification
import PfaffianDescent.PointAdaptedCechAugmentation

/-!
# The canonical restriction in the point Koszul augmentation square

The global section is the actual restriction of one. Its restriction to
the point chart is the normalized Koszul generator in the canonical
quotient-stalk coordinate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace PfaffianDescent

universe u

set_option backward.isDefEq.respectTransparency false in
/-- Canonical closed-subscheme restriction sections commute with shrinking. -/
theorem closedImmersionUnitTwistRestrictionSection_map
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {U W : X.Opens} (j : W ⟶ U) (r : Γ(X, U)) :
    (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃.val.map
        j.op (closedImmersionUnitTwistRestrictionSection i U r) =
      closedImmersionUnitTwistRestrictionSection i W (X.presheaf.map j.op r) := by
  unfold closedImmersionUnitTwistRestrictionSection
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  rfl

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The actual restriction-of-one section, with its local generator identity
and its Cech-to-Koszul augmentation square. There is no existential choice
of a normalized global section. -/
theorem closedFieldPointUnitTwistRestriction_one_augmentation_square
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    {J : Type u} (V : J → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (V j)).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (V j))))
    (U : X.Opens) (hx : i default ∈ U) (q f : Γ(X, U)) :
    letI := schemeModuleStalkModule (show X.Modules from
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
      (i default)
    ∀ (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap
        i (i default)) = Ideal.span
          ({X.presheaf.germ U (i default) hx q, X.presheaf.germ U (i default) hx f} : Set _)),
    let Q := (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃
    let s := closedImmersionUnitTwistRestrictionSection i ⊤ 1
    let m := fieldPointSectionRepresenterKoszulSection i (SheafOfModules.unit X.ringCatSheaf)
      V hV eV U hx q f (closedImmersionUnitTwistStalkQuotientIso i (i default)
        (X.presheaf.germ U (i default) hx q) (X.presheaf.germ U (i default) hx f) hkernel)
    Q.val.map (homOfLE (le_top : U ≤ ⊤)).op s = m ∧
      sectionRepresenterCechAugmentation X.ringCatSheaf
          (PointAdaptedAffineCover.opens U (i default)) ⊤ isTerminalTop ≫
        (sectionRepresenterCechTargetIsoTerminal X.ringCatSheaf
          (PointAdaptedAffineCover.opens U (i default)) ⊤ isTerminalTop).hom ≫
        sectionRepresenterAugmentation X.ringCatSheaf ⊤ Q s =
      PointAdaptedAffineCover.onC₀ U (i default) ≫
        sectionRepresenterKoszulAugmentation X.ringCatSheaf U Q m := by
  dsimp only
  letI := schemeModuleStalkModule (show X.Modules from
    (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (i default)
  intro hkernel
  have hs := closedImmersionUnitTwistRestrictionSection_map i
    (homOfLE (le_top : U ≤ ⊤)) 1
  rw [map_one, closedFieldPointUnitTwistRestriction_one_eq_koszulSection
    i V hV eV U hx q f hkernel] at hs
  refine ⟨hs, ?_⟩
  have h := PointAdaptedAffineCover.augmentation_square_fieldPointUnitQuotient
    i U (closedImmersionUnitTwistRestrictionSection i ⊤ 1)
  dsimp only at h
  rw [hs] at h
  exact h

end PfaffianDescent
