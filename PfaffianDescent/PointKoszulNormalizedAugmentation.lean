import PfaffianDescent.PointSkyscraperGlobalSection
import PfaffianDescent.PointAdaptedCechAugmentation

/-!
# The normalized point Koszul augmentation and the actual Cech square

The already proved exact point resolution uses a normalized local section.
Here that very section is extended globally and inserted into the actual
Cech augmentation square, without an unproved identification of generators.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace PfaffianDescent

universe u

set_option backward.isDefEq.respectTransparency false in
/-- Extend the exact Koszul resolution's generator and prove its actual
Cech augmentation square for the untwisted field-point quotient. -/
theorem exists_fieldPointUnitKoszul_normalized_augmentation_square
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    {J : Type u} (V : J → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (V j)).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (V j))))
    (U : X.Opens) (hx : i default ∈ U) (q f : Γ(X, U))
    (qM : (schemeModuleStalkModuleFunctor X (i default)).obj
        (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃ ≅
      ModuleCat.of (X.presheaf.stalk (i default))
        (sectionRepresenterPointKoszulQuotient X U (i default) hx q f)) :
    let Q := (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃
    let m := fieldPointSectionRepresenterKoszulSection i
      (SheafOfModules.unit X.ringCatSheaf) V hV eV U hx q f qM
    ∃ s : Q.val.obj (op (⊤ : X.Opens)),
      Q.val.map (homOfLE (le_top : U ≤ ⊤)).op s = m ∧
      sectionRepresenterCechAugmentation X.ringCatSheaf
          (PointAdaptedAffineCover.opens U (i default)) ⊤
          (isTerminalTop : IsTerminal (⊤ : X.Opens)) ≫
        (sectionRepresenterCechTargetIsoTerminal X.ringCatSheaf
          (PointAdaptedAffineCover.opens U (i default)) ⊤
          (isTerminalTop : IsTerminal (⊤ : X.Opens))).hom ≫
        sectionRepresenterAugmentation X.ringCatSheaf ⊤ Q s =
      PointAdaptedAffineCover.onC₀ U (i default) ≫
        sectionRepresenterKoszulAugmentation X.ringCatSheaf U Q m := by
  obtain ⟨s, hs⟩ := exists_fieldPointKoszul_global_section i
    (SheafOfModules.unit X.ringCatSheaf) V hV eV U hx q f qM
  refine ⟨s, hs, ?_⟩
  have h := PointAdaptedAffineCover.augmentation_square_fieldPointUnitQuotient i U s
  dsimp only at h
  rw [hs] at h
  exact h

end PfaffianDescent
