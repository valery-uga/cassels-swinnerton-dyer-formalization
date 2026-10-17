import PfaffianDescent.CechExtDegreeOne
import PfaffianDescent.SchemeCoverIntrinsicCohomology
import PfaffianDescent.ExtMapFixedSource

/-! Genuine degree-one Čech-to-Ext maps for actual scheme covers.
The actual covering augmentation derives exactness and epimorphy; these
are never supplied as comparison certificates. Local degree-zero Ext is
explicit only in the generic computation lemma.
STATUS: UNVERIFIED source only. Root owns compiler checks.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u
variable {X : Scheme.{u}} {ι : Type u}

set_option backward.isDefEq.respectTransparency false in
/-- The actual covering Hom cocycle determines its actual augmentation Ext¹
class through the internally proved image short exact sequence. -/
def schemeCoverDegreeOneToExtHom (U : ι → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U) [hExt : HasExt.{u} X.Modules]
    (Y : X.Modules) :
    DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1) (Y := Y) →+
      Ext (C := X.Modules)
        (sectionRepresenterCechAugmented X.ringCatSheaf U ⊤ isTerminalTop).right Y 1 := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  let C : ChainComplex X.Modules ℕ := sectionRepresenterCechChain X.ringCatSheaf U
  let eps := sectionRepresenterCechAugmentation X.ringCatSheaf U ⊤ isTerminalTop
  let hex := sectionRepresenterCech_augmentation_exact_and_epi_of_coversTop
    X.ringCatSheaf U hU ⊤ isTerminalTop
  letI : Epi eps := hex.2
  exact augmentedChainDegreeOneToExtHom Y eps (C.d 1 0) (C.d 2 1)
    (sectionRepresenterCech_d_one_zero_comp_augmentation X.ringCatSheaf U ⊤ isTerminalTop)
    (C.d_comp_d 2 1 0) hex.1 (schemeCoverCech_exact_one U hU)

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of the actual covering Ext¹ map consists precisely of the
actual covering degree-zero Hom boundaries, without local Ext assumptions. -/
theorem schemeCoverDegreeOneToExt_eq_zero_iff (U : ι → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U) [hExt : HasExt.{u} X.Modules]
    (Y : X.Modules)
    (z : DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1) (Y := Y)) :
    schemeCoverDegreeOneToExtHom U hU Y z = 0 ↔
      ∃ q : (sectionRepresenterCechChain X.ringCatSheaf U).X 0 ⟶ Y,
        (sectionRepresenterCechChain X.ringCatSheaf U).d 1 0 ≫ q = z.1 := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  let C : ChainComplex X.Modules ℕ := sectionRepresenterCechChain X.ringCatSheaf U
  let eps := sectionRepresenterCechAugmentation X.ringCatSheaf U ⊤ isTerminalTop
  let hex := sectionRepresenterCech_augmentation_exact_and_epi_of_coversTop
    X.ringCatSheaf U hU ⊤ isTerminalTop
  letI : Epi eps := hex.2
  exact augmentedChainDegreeOneToExt_eq_zero_iff Y eps (C.d 1 0) (C.d 2 1)
    (sectionRepresenterCech_d_one_zero_comp_augmentation X.ringCatSheaf U ⊤ isTerminalTop)
    (C.d_comp_d 2 1 0) hex.1 (schemeCoverCech_exact_one U hU) z

set_option backward.isDefEq.respectTransparency false in
/-- The generic cover map is surjective when its actual degree-zero term
has vanishing Ext¹. Actual normalization callers discharge this input. -/
theorem schemeCoverDegreeOneToExt_surjective (U : ι → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U) [hExt : HasExt.{u} X.Modules]
    (Y : X.Modules)
    [Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf U).X 0) Y 1)] :
    Function.Surjective (schemeCoverDegreeOneToExtHom U hU Y) := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  let C : ChainComplex X.Modules ℕ := sectionRepresenterCechChain X.ringCatSheaf U
  let eps := sectionRepresenterCechAugmentation X.ringCatSheaf U ⊤ isTerminalTop
  let hex := sectionRepresenterCech_augmentation_exact_and_epi_of_coversTop
    X.ringCatSheaf U hU ⊤ isTerminalTop
  letI : Epi eps := hex.2
  exact augmentedChainDegreeOneToExt_surjective Y eps (C.d 1 0) (C.d 2 1)
    (sectionRepresenterCech_d_one_zero_comp_augmentation X.ringCatSheaf U ⊤ isTerminalTop)
    (C.d_comp_d 2 1 0) hex.1 (schemeCoverCech_exact_one U hU)

set_option backward.isDefEq.respectTransparency false in
/-- The actual cover quotient computes actual intrinsic degree-one
scheme-module cohomology, after the genuine augmentation/unit isomorphism.
The generic local Ext condition is explicit; it is not a claimed finite
pushforward theorem or a supplied comparison isomorphism. -/
def schemeCoverDegreeOneQuotientEquivCohomologyOne (U : ι → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U) [HasExt.{u} X.Modules]
    (Y : X.Modules)
    [Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf U).X 0) Y 1)] :
    DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1) (Y := Y) ⧸
        (schemeCoverDegreeOneToExtHom U hU Y).ker ≃+
      schemeModuleCohomology X Y 1 :=
  (QuotientAddGroup.quotientKerEquivOfSurjective
    (schemeCoverDegreeOneToExtHom U hU Y)
    (schemeCoverDegreeOneToExt_surjective U hU Y)).trans
      (extPrecompIsoOfIso (schemeCoverCechTargetIsoUnit U))

end PfaffianDescent
