import PfaffianDescent.SectionRepresenterCechAugmentationComponents
import PfaffianDescent.PointAdaptedCechKoszulFirstLift
import PfaffianDescent.PointPushforwardSectionsSupport

/-!
# The augmentation square for the actual point quotient

The point's global section is zero on every other cover member, by the
proved support theorem. Consequently the adapted vertex map commutes
with the Cech augmentation and the point augmentation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace PfaffianDescent

universe u

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition of a section augmentation is restriction of its section. -/
theorem sectionRepresenterAugmentation_restrict
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {W U : C} (j : W ⟶ U) (M : SheafOfModules.{u} R) (m : M.val.obj (op U)) :
    (sectionRepresenterFunctor R).map j ≫ sectionRepresenterAugmentation R U M m =
      sectionRepresenterAugmentation R W M (M.val.map j.op m) := by
  apply (sectionRepresenterHomEquiv R W M).injective
  rw [sectionRepresenterHomEquiv_precomp, sectionRepresenterHomEquiv_augmentation,
    sectionRepresenterHomEquiv_augmentation]

namespace PointAdaptedAffineCover

set_option backward.isDefEq.respectTransparency false in
/-- The augmentation square for a section supported at the chosen point. -/
theorem augmentation_square_of_supported_section
    {X : Scheme.{u}} (U : X.Opens) (x : X) (M : X.Modules)
    (s : M.val.obj (op (⊤ : X.Opens)))
    (hsupport : ∀ V : X.Opens, x ∉ V →
      M.val.map (homOfLE (le_top : V ≤ ⊤)).op s = 0) :
    sectionRepresenterCechAugmentation X.ringCatSheaf (opens U x) ⊤
        (isTerminalTop : IsTerminal (⊤ : X.Opens)) ≫
      (sectionRepresenterCechTargetIsoTerminal X.ringCatSheaf (opens U x) ⊤
        (isTerminalTop : IsTerminal (⊤ : X.Opens))).hom ≫
      sectionRepresenterAugmentation X.ringCatSheaf ⊤ M s =
    onC₀ U x ≫ sectionRepresenterAugmentation X.ringCatSheaf U M
      (M.val.map (homOfLE (le_top : U ≤ ⊤)).op s) := by
  let r := sectionRepresenterAugmentation X.ringCatSheaf U M
    (M.val.map (homOfLE (le_top : U ≤ ⊤)).op s)
  let g := sectionRepresenterAugmentation X.ringCatSheaf ⊤ M s
  have hv (i : Index X x) : vertexMap U x i ≫ r =
      (sectionRepresenterFunctor X.ringCatSheaf).map
        (homOfLE (le_top : opens U x i ≤ ⊤)) ≫ g := by
    cases i with
    | none =>
      change 𝟙 (sectionRepresenter X.ringCatSheaf U) ≫ r = _
      rw [Category.id_comp]
      exact (sectionRepresenterAugmentation_restrict X.ringCatSheaf
        (homOfLE (le_top : U ≤ ⊤)) M s).symm
    | some V =>
      change (0 : sectionRepresenter X.ringCatSheaf V.val ⟶
        sectionRepresenter X.ringCatSheaf U) ≫ r =
        (sectionRepresenterFunctor X.ringCatSheaf).map
          (homOfLE (le_top : V.val ≤ ⊤)) ≫ sectionRepresenterAugmentation X.ringCatSheaf ⊤ M s
      rw [zero_comp, sectionRepresenterAugmentation_restrict,
        hsupport V.val V.prop.2, sectionRepresenterAugmentation_zero]
  apply Sigma.hom_ext
  intro f
  change Sigma.ι (fun a : Fin 1 → Index X x =>
      sectionRepresenter X.ringCatSheaf (∏ᶜ fun k : Fin 1 => opens U x (a k))) f ≫
      sectionRepresenterCechAugmentation X.ringCatSheaf (opens U x) ⊤ (isTerminalTop : IsTerminal (⊤ : X.Opens)) ≫
        (sectionRepresenterCechTargetIsoTerminal X.ringCatSheaf (opens U x) ⊤
          (isTerminalTop : IsTerminal (⊤ : X.Opens))).hom ≫ g =
    Sigma.ι (fun a : Fin 1 → Index X x =>
      sectionRepresenter X.ringCatSheaf (∏ᶜ fun k : Fin 1 => opens U x (a k))) f ≫
      sectionRepresenterCechVertexMap X.ringCatSheaf (opens U x)
        (sectionRepresenter X.ringCatSheaf U) (vertexMap U x) ≫ r
  have he := sectionRepresenterCechAugmentation_component X.ringCatSheaf (opens U x)
    ⊤ (isTerminalTop : IsTerminal (⊤ : X.Opens)) f
  have he' := congrArg (fun k : sectionRepresenter X.ringCatSheaf
      (∏ᶜ fun k : Fin 1 => opens U x (f k)) ⟶ sectionRepresenter X.ringCatSheaf ⊤ =>
        k ≫ g) he
  have hr := sectionRepresenterCechVertexMap_component X.ringCatSheaf (opens U x)
    (sectionRepresenter X.ringCatSheaf U) (vertexMap U x) f
  have hr' := congrArg (fun k : sectionRepresenter X.ringCatSheaf
      (∏ᶜ fun k : Fin 1 => opens U x (f k)) ⟶ sectionRepresenter X.ringCatSheaf U =>
        k ≫ r) hr
  calc
    _ = (sectionRepresenterFunctor X.ringCatSheaf).map
        ((isTerminalTop : IsTerminal (⊤ : X.Opens)).from
          (∏ᶜ fun k : Fin 1 => opens U x (f k))) ≫ g := by
      simpa only [Category.assoc] using he'
    _ = (sectionRepresenterFunctor X.ringCatSheaf).map
        (Pi.π (fun k : Fin 1 => opens U x (f k)) 0) ≫ vertexMap U x (f 0) ≫ r := by
      rw [hv, ← Category.assoc, ← Functor.map_comp]
      congr 2
    _ = _ := by
      symm
      simpa only [Category.assoc] using hr'

set_option backward.isDefEq.respectTransparency false in
/-- The actual untwisted field-point quotient satisfies the augmentation
square with no support or compatibility hypothesis. -/
theorem augmentation_square_fieldPointUnitQuotient
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i] (U : X.Opens)
    (s : (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit X.ringCatSheaf)).X₃.val.obj (op (⊤ : X.Opens))) :
    let Q := (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃
    sectionRepresenterCechAugmentation X.ringCatSheaf (opens U (i default)) ⊤
        (isTerminalTop : IsTerminal (⊤ : X.Opens)) ≫
      (sectionRepresenterCechTargetIsoTerminal X.ringCatSheaf (opens U (i default)) ⊤
        (isTerminalTop : IsTerminal (⊤ : X.Opens))).hom ≫
      sectionRepresenterAugmentation X.ringCatSheaf ⊤ Q s =
    onC₀ U (i default) ≫ sectionRepresenterAugmentation X.ringCatSheaf U Q
      (Q.val.map (homOfLE (le_top : U ≤ ⊤)).op s) := by
  apply augmentation_square_of_supported_section
  intro V hV
  exact @Subsingleton.elim
    ((closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃.val.obj (op V))
    (fieldPointUnitQuotient_sections_subsingleton_away_point i V hV) _ _

end PointAdaptedAffineCover
end PfaffianDescent
