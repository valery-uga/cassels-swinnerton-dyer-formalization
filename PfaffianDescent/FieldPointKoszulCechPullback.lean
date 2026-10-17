import PfaffianDescent.PointAdaptedCechExt
import PfaffianDescent.PointKoszulNormalizedAugmentation

/-!
# Actual point Koszul classes pulled back to Cech classes

The geometric comparison maps, normalized global section, augmentation
square, and exact resolutions instantiate source naturality. This proves
an equality of actual Ext classes, not a comparison square assumed as data.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped nonZeroDivisors ZeroObject

namespace PfaffianDescent

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

universe u

set_option backward.isDefEq.respectTransparency false in
/-- The actual normalized point Koszul class pulls back to a cocycle on
the actual adapted Cech cover. All comparison squares are constructed. -/
theorem exists_fieldPointUnitKoszul_cech_pullback
    {L : Type u} [Field L] {X : Scheme.{u}}
    [IsAffineHom (pullback.diagonal (terminal.from X))] [hExt : HasExt.{u} X.Modules]
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    {J : Type u} (V : J → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (V j)).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (V j))))
    (U : X.Opens) (hU : IsAffineOpen U) (hx : i default ∈ U) (q f : Γ(X, U))
    (qM : (schemeModuleStalkModuleFunctor X (i default)).obj
        (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃ ≅
      ModuleCat.of (X.presheaf.stalk (i default))
        (sectionRepresenterPointKoszulQuotient X U (i default) hx q f))
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ i default →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤)
    (hqreg : X.presheaf.germ U (i default) hx q ∈ (X.presheaf.stalk (i default))⁰)
    (hfreg : Ideal.Quotient.mk (Ideal.span {X.presheaf.germ U (i default) hx q})
        (X.presheaf.germ U (i default) hx f) ∈
      ((X.presheaf.stalk (i default)) ⧸ Ideal.span {X.presheaf.germ U (i default) hx q})⁰)
    (Y : X.Modules) (y : Y.val.obj (op U)) :
    let Q := (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃
    ∃ (s : Q.val.obj (op (⊤ : X.Opens)))
      (a₁ : (sectionRepresenterCechChain X.ringCatSheaf
          (PointAdaptedAffineCover.opens U (i default))).X 1 ⟶
        ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U)
      (a₂ : (sectionRepresenterCechChain X.ringCatSheaf
          (PointAdaptedAffineCover.opens U (i default))).X 2 ⟶
        sectionRepresenter X.ringCatSheaf U)
      (z : DegreeTwoCocycle
        ((sectionRepresenterCechChain X.ringCatSheaf
          (PointAdaptedAffineCover.opens U (i default))).d 3 2) (Y := Y)),
      Q.val.map (homOfLE (le_top : U ≤ ⊤)).op s =
        fieldPointSectionRepresenterKoszulSection i (SheafOfModules.unit X.ringCatSheaf)
          V hV eV U hx q f qM ∧
      a₁ ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f =
        (sectionRepresenterCechChain X.ringCatSheaf
          (PointAdaptedAffineCover.opens U (i default))).d 1 0 ≫
          PointAdaptedAffineCover.onC₀ U (i default) ∧
      a₂ ≫ sectionRepresenterKoszulFirst X.ringCatSheaf U q f =
        (sectionRepresenterCechChain X.ringCatSheaf
          (PointAdaptedAffineCover.opens U (i default))).d 2 1 ≫ a₁ ∧
      (sectionRepresenterCechChain X.ringCatSheaf
          (PointAdaptedAffineCover.opens U (i default))).d 3 2 ≫ a₂ = 0 ∧
      z.1 = a₂ ≫ sectionRepresenterAugmentation X.ringCatSheaf U Y y ∧
      (Ext.mk₀ (C := X.Modules) ((sectionRepresenterCechTargetIsoTerminal X.ringCatSheaf
        (PointAdaptedAffineCover.opens U (i default)) ⊤ isTerminalTop).hom ≫
          sectionRepresenterAugmentation X.ringCatSheaf ⊤ Q s)).comp
        (fieldPointSectionRepresenterKoszulDegreeTwoClass i (SheafOfModules.unit X.ringCatSheaf)
          V hV eV U hx q f qM haway hqreg hfreg Y y) (zero_add 2) =
        PointAdaptedAffineCover.degreeTwoToExt U (i default) hx (fieldPoint_image_isClosed i) Y z := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  let T := SheafOfModules.unit X.ringCatSheaf
  let Q := (closedImmersionIdealTwistSequence i T).X₃
  let W := PointAdaptedAffineCover.opens U (i default)
  let C := sectionRepresenterCechChain X.ringCatSheaf W
  let P := PointAdaptedAffineCover.target U (i default)
  let B := sectionRepresenter X.ringCatSheaf U
  let B₁ := ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U
  let m := fieldPointSectionRepresenterKoszulSection i T V hV eV U hx q f qM
  let eta := sectionRepresenterKoszulAugmentation X.ringCatSheaf U Q m
  let e₁ := sectionRepresenterKoszulLast X.ringCatSheaf U q f
  let e₂ := sectionRepresenterKoszulFirst X.ringCatSheaf U q f
  let e₃ : (0 : X.Modules) ⟶ B := 0
  let eps := sectionRepresenterCechAugmentation X.ringCatSheaf W ⊤ isTerminalTop
  let hmq := sectionRepresenterPointKoszulTransportedSection_q_smul
    X U (i default) hx q f Q
    (fieldPointPushforwardTwist_skyscraperIso_of_coversTop_iso_unit i T V hV eV) qM
  let hmf := sectionRepresenterPointKoszulTransportedSection_f_smul
    X U (i default) hx q f Q
    (fieldPointPushforwardTwist_skyscraperIso_of_coversTop_iso_unit i T V hV eV) qM
  let k₁₀ := sectionRepresenterKoszulLast_comp_augmentation X.ringCatSheaf U q f Q m hmq hmf
  let k₂₁ := sectionRepresenterKoszul_comp_zero X.ringCatSheaf U q f (Commute.all q f)
  have kexact₀ := fieldPointSectionRepresenterKoszul_augmented_exact i T V hV eV U hx q f qM haway
  have kexact₁ := sectionRepresenterKoszul_exact_of_regularPairAtPoint
    X U q f (i default) hx hqreg hfreg haway
  letI : Mono e₂ := sectionRepresenterKoszulFirst_mono_of_regularPairAtPoint
    X U q f (i default) hx hqreg hfreg haway
  have kexact₂ := sectionRepresenterKoszul_zero_left_exact X.ringCatSheaf U q f
  letI : Epi eta := fieldPointSectionRepresenterKoszul_augmentation_epi i T V hV eV U hx q f qM
  let hc := fieldPoint_image_isClosed i
  letI : Epi eps := (PointAdaptedAffineCover.augmentation_exact_and_epi U (i default) hx hc).2
  obtain ⟨s, hs, haug⟩ := exists_fieldPointUnitKoszul_normalized_augmentation_square
    i V hV eV U hx q f qM
  obtain ⟨a₁, a₂, h₁, h₂, h₃⟩ := PointAdaptedAffineCover.exists_chain_comparison
    U hU (i default) hx q f hqreg hfreg haway
  let g : P ⟶ Q := (sectionRepresenterCechTargetIsoTerminal X.ringCatSheaf W ⊤ isTerminalTop).hom ≫
    sectionRepresenterAugmentation X.ringCatSheaf ⊤ Q s
  have haug' : eps ≫ g = PointAdaptedAffineCover.onC₀ U (i default) ≫ eta := haug
  let a₃ : C.X 3 ⟶ (0 : X.Modules) := 0
  have hthird : C.d 3 2 ≫ a₂ = a₃ ≫ e₃ := by
    change C.d 3 2 ≫ a₂ = (0 : C.X 3 ⟶ (0 : X.Modules)) ≫ (0 : (0 : X.Modules) ⟶ B)
    rw [zero_comp]
    exact h₃
  let t := sectionRepresenterKoszulDegreeTwoCocycle X.ringCatSheaf U Y y
  let z := DegreeTwoCocycle.precompAddHom (C.d 3 2) e₃ a₂ a₃ hthird t
  refine ⟨s, a₁, a₂, z, hs, h₁, h₂, h₃, rfl, ?_⟩
  have hn := augmentedChainDegreeTwoToExt_precomp
    P (C.X 0) (C.X 1) (C.X 2) (C.X 3) Q B B₁ B (0 : X.Modules) Y
    eps (C.d 1 0) (C.d 2 1) (C.d 3 2) eta e₁ e₂ e₃
    (sectionRepresenterCech_d_one_zero_comp_augmentation X.ringCatSheaf W ⊤ isTerminalTop)
    (C.d_comp_d 2 1 0) (C.d_comp_d 3 2 1) k₁₀ k₂₁ zero_comp
    (PointAdaptedAffineCover.augmentation_exact_and_epi U (i default) hx hc).1
    (PointAdaptedAffineCover.exact_one U (i default) hx hc)
    (PointAdaptedAffineCover.exact_two U (i default) hx hc)
    kexact₀ kexact₁ kexact₂ g (PointAdaptedAffineCover.onC₀ U (i default))
    a₁ a₂ a₃ haug' h₁.symm h₂.symm hthird t
  exact hn

end PfaffianDescent
