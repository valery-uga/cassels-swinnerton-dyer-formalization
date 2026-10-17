import Mathlib.Tactic.Trace
import PfaffianDescent.CechExtDegreeOne
import PfaffianDescent.SchemeCoverCechExtDegreeOne
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.LinearAlgebra.Quotient.Defs

/-! Linearity of the existing actual degree-one image connecting map.
Cocycle and quotient actions are the natural submodule/quotient actions of
the genuine Hom complex. They are not transported from Ext through an
equivalence. STATUS: UNVERIFIED source only; root owns compiler checks.
-/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u v w t
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type t} [CommRing R]
variable {A : Type u} [Category.{v} A] [Abelian A] [Linear R A] [HasExt.{w} A]

/-- Actual degree-one Hom cocycles form the kernel submodule of actual
linear precomposition by the next differential. This uses the existing
cocycle subtype; no new cocycles or replacement scalar action are chosen. -/
def degreeOneCocycleModuleOfLinear {C₁ C₂ Y : A} (d₂ : C₂ ⟶ C₁) :
    Module R (DegreeOneCocycle d₂ (Y := Y)) := by
  change Module R ↥(CategoryTheory.Linear.leftComp R Y d₂).ker
  infer_instance

/-- The natural actual kernel-module scalar is the original Hom scalar on
the actual cocycle value. -/
theorem degreeOneCocycleModuleOfLinear_smul_val
    {C₁ C₂ Y : A} (d₂ : C₂ ⟶ C₁) (c : R) (z : DegreeOneCocycle d₂ (Y := Y)) :
    letI : Module R (DegreeOneCocycle d₂ (Y := Y)) := degreeOneCocycleModuleOfLinear d₂
    (c • z).1 = c • z.1 := by
  letI : Module R (DegreeOneCocycle d₂ (Y := Y)) := degreeOneCocycleModuleOfLinear d₂
  rfl

/-- Actual cocycle descent to the actual image respects the original
Hom scalar, proved by cancelling the actual factor-through-image epi. -/
theorem degreeOneCocycleDesc_smul_of_linear
    {C₀ C₁ C₂ Y : A} (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (h₂₁ : d₂ ≫ d₁ = 0) (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    (c : R) (z : DegreeOneCocycle d₂ (Y := Y)) :
    letI : Module R (DegreeOneCocycle d₂ (Y := Y)) := degreeOneCocycleModuleOfLinear d₂
    degreeOneCocycleDesc d₁ d₂ h₂₁ hexact₁ (c • z) =
      c • degreeOneCocycleDesc d₁ d₂ h₂₁ hexact₁ z := by
  letI : Module R (DegreeOneCocycle d₂ (Y := Y)) := degreeOneCocycleModuleOfLinear d₂
  apply (cancel_epi (Abelian.factorThruImage d₁)).1
  rw [factorThruImage_comp_degreeOneCocycleDesc, Linear.comp_smul,
    factorThruImage_comp_degreeOneCocycleDesc]
  rfl

/-- The actual image-extension connecting map is linear for the installed
actual Ext module. Exactness is the ordinary generic chain input, not a
comparison or connecting-map compatibility certificate. -/
theorem augmentedChainDegreeOneToExtHom_smul_of_linear
    {P C₀ C₁ C₂ : A} (Y : A)
    (epsilon : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (h₁₀ : d₁ ≫ epsilon = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (hexact₀ : (ShortComplex.mk d₁ epsilon h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact) [Epi epsilon]
    (c : R) (z : DegreeOneCocycle d₂ (Y := Y)) :
    letI : Module R (DegreeOneCocycle d₂ (Y := Y)) := degreeOneCocycleModuleOfLinear d₂
    augmentedChainDegreeOneToExtHom Y epsilon d₁ d₂ h₁₀ h₂₁ hexact₀ hexact₁ (c • z) =
      c • augmentedChainDegreeOneToExtHom Y epsilon d₁ d₂ h₁₀ h₂₁ hexact₀ hexact₁ z := by
  letI : Module R (DegreeOneCocycle d₂ (Y := Y)) := degreeOneCocycleModuleOfLinear d₂
  let hS := augmentedChainDegreeOneShortComplex_shortExact epsilon d₁ h₁₀ hexact₀
  change hS.extClass.comp (Ext.mk₀ (degreeOneCocycleDesc d₁ d₂ h₂₁ hexact₁ (c • z)))
      (show 1 + 0 = 1 by rfl) =
    c • hS.extClass.comp (Ext.mk₀ (degreeOneCocycleDesc d₁ d₂ h₂₁ hexact₁ z))
      (show 1 + 0 = 1 by rfl)
  rw [degreeOneCocycleDesc_smul_of_linear, Ext.mk₀_smul, Ext.comp_smul]

/-- Ordinary scalar descent for an existing quotient action and additive map.
All native callers provide their actual representative map and certificates. -/
private def linearEquivOfRepresentativeLinearMap
    {C Q H : Type*} [AddCommGroup C] [AddCommGroup Q] [AddCommGroup H]
    [Module R C] [Module R Q] [Module R H]
    (mk : C → Q) (hmk : Function.Surjective mk)
    (hmk_smul : ∀ (c : R) (z : C), mk (c • z) = c • mk z)
    (E : Q ≃+ H) (f : C →ₗ[R] H) (heval : ∀ z, E (mk z) = f z) :
    Q ≃ₗ[R] H where
  toAddEquiv := E
  map_smul' c q := by
    obtain ⟨z, rfl⟩ := hmk q
    calc
      E (c • mk z) = E (mk (c • z)) := congrArg E (hmk_smul c z).symm
      _ = f (c • z) := heval (c • z)
      _ = c • f z := f.map_smul c z
      _ = c • E (mk z) := congrArg (fun w => c • w) (heval z).symm

section SchemeCover
variable {X : Scheme.{u}} {ι : Type u} [HasExt.{u} X.Modules] [Linear R X.Modules]

/-- The actual covering connecting AddHom from the prior packet is linear;
cover augmentation and image exactness are still discharged internally. -/
theorem schemeCoverDegreeOneToExtHom_smul_of_linear (U : ι → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U) (M : X.Modules)
    (c : R) (z : DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := M)) :
    letI : Module R (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := M)) := degreeOneCocycleModuleOfLinear _
    schemeCoverDegreeOneToExtHom U hU M (c • z) =
      c • schemeCoverDegreeOneToExtHom U hU M z := by
  letI : Module R (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
    (Y := M)) := degreeOneCocycleModuleOfLinear _
  let C : ChainComplex X.Modules ℕ := sectionRepresenterCechChain X.ringCatSheaf U
  let eps := sectionRepresenterCechAugmentation X.ringCatSheaf U ⊤ isTerminalTop
  let hex := sectionRepresenterCech_augmentation_exact_and_epi_of_coversTop
    X.ringCatSheaf U hU ⊤ isTerminalTop
  letI : Epi eps := hex.2
  exact augmentedChainDegreeOneToExtHom_smul_of_linear M eps (C.d 1 0) (C.d 2 1)
    (sectionRepresenterCech_d_one_zero_comp_augmentation X.ringCatSheaf U ⊤ isTerminalTop)
    (C.d_comp_d 2 1 0) hex.1 (schemeCoverCech_exact_one U hU) c z

/-- Linear packaging of the SAME actual cover connecting AddHom. -/
def schemeCoverDegreeOneToExtLinearMap (U : ι → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U) (M : X.Modules) :
    letI : Module R (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := M)) := degreeOneCocycleModuleOfLinear _
    DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1) (Y := M) →ₗ[R]
      Ext.{u} (C := X.Modules)
        (sectionRepresenterCechAugmented X.ringCatSheaf U ⊤ isTerminalTop).right M 1 := by
  letI : Module R (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
    (Y := M)) := degreeOneCocycleModuleOfLinear _
  exact
    { toAddHom := (schemeCoverDegreeOneToExtHom U hU M).toAddHom
      map_smul' := schemeCoverDegreeOneToExtHom_smul_of_linear U hU M }

/-- The original actual cocycle quotient has its natural K-module structure
as the quotient by the kernel of the SAME actual linear connecting map.
No action is pulled back from Ext through a quotient equivalence. -/
def schemeCoverDegreeOneQuotientModuleOfLinear (U : ι → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U) (M : X.Modules) :
    Module R
      (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1) (Y := M) ⧸
        (schemeCoverDegreeOneToExtHom U hU M).ker) := by
  letI : Module R (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
    (Y := M)) := degreeOneCocycleModuleOfLinear _
  change Module R (_ ⧸ (schemeCoverDegreeOneToExtLinearMap (R := R) U hU M).ker)
  infer_instance

/-- Evaluate the SAME actual additive quotient equivalence on a representative,
without unfolding its scalar action at the same time. -/
private theorem schemeCoverDegreeOneQuotientEquiv_mk
    (U : ι → X.Opens) (hU : (Opens.grothendieckTopology X).CoversTop U)
    (M : X.Modules)
    [Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf U).X 0) M 1)]
    (z : DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := M)) :
    let hExt : HasExt.{u} X.Modules := inferInstance
    letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
    schemeCoverDegreeOneQuotientEquivCohomologyOne U hU M (QuotientAddGroup.mk z) =
      (Ext.mk₀ (schemeCoverCechTargetIsoUnit U).inv).comp
        (schemeCoverDegreeOneToExtHom U hU M z) (zero_add 1) := by
  let hExt : HasExt.{u} X.Modules := inferInstance
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  rfl

/-- The SAME natural quotient Module acts on actual representatives by the
SAME natural cocycle scalar action. No action is transported from Ext. -/
private theorem schemeCoverDegreeOneQuotient_mk_smul
    (U : ι → X.Opens) (hU : (Opens.grothendieckTopology X).CoversTop U)
    (M : X.Modules) (c : R)
    (z : DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := M)) :
    letI : Module R (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := M)) := degreeOneCocycleModuleOfLinear _
    letI : Module R
      (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1) (Y := M) ⧸
        (schemeCoverDegreeOneToExtHom U hU M).ker) := schemeCoverDegreeOneQuotientModuleOfLinear U hU M
    (QuotientAddGroup.mk (c • z) :
      DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1) (Y := M) ⧸
        (schemeCoverDegreeOneToExtHom U hU M).ker) = c • QuotientAddGroup.mk z := by
  letI : Module R (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
    (Y := M)) := degreeOneCocycleModuleOfLinear _
  letI : Module R
      (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1) (Y := M) ⧸
        (schemeCoverDegreeOneToExtHom U hU M).ker) := schemeCoverDegreeOneQuotientModuleOfLinear U hU M
  rfl

/-- Linearity of the SAME actual quotient-to-intrinsic-Ext equivalence
from the prior packet. The explicit generic C₀ Ext input remains necessary
for computing Ext; normalization callers discharge it internally. -/
def schemeCoverDegreeOneQuotientLinearEquivCohomologyOne (U : ι → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U) (M : X.Modules)
    [Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf U).X 0) M 1)] :
    letI : Module R (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := M)) := degreeOneCocycleModuleOfLinear _
    letI : Module R
      (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1) (Y := M) ⧸
        (schemeCoverDegreeOneToExtHom U hU M).ker) := schemeCoverDegreeOneQuotientModuleOfLinear U hU M
    (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1) (Y := M) ⧸
        (schemeCoverDegreeOneToExtHom U hU M).ker) ≃ₗ[R]
      schemeModuleCohomology X M 1 := by
  trace "EXT008 P00 public proof entry"
  letI : Module R (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
    (Y := M)) := degreeOneCocycleModuleOfLinear _
  letI : Module R
      (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1) (Y := M) ⧸
        (schemeCoverDegreeOneToExtHom U hU M).ker) := schemeCoverDegreeOneQuotientModuleOfLinear U hU M
  trace "EXT008 P01 natural Modules installed / before native linear composition"
  let hExt : HasExt.{u} X.Modules := inferInstance
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  let nativeLinear : Linear R X.Modules := inferInstance
  letI : Linear R (SheafOfModules.{u} X.ringCatSheaf) := nativeLinear
  let E := schemeCoverDegreeOneQuotientEquivCohomologyOne U hU M
  let f := ((Ext.mk₀ (schemeCoverCechTargetIsoUnit U).inv).precompOfLinear R M
    (zero_add 1)).comp (schemeCoverDegreeOneToExtLinearMap (R := R) U hU M)
  trace "EXT008 P02 actual representative LinearMap formed / before eval certificate"
  have heval : ∀ z, E (QuotientAddGroup.mk z) = f z := by
    intro z
    exact schemeCoverDegreeOneQuotientEquiv_mk U hU M z
  trace "EXT008 P03 eval certificate formed / before generic scalar descent"
  exact linearEquivOfRepresentativeLinearMap QuotientAddGroup.mk
    (fun q => QuotientAddGroup.induction_on q (fun z => ⟨z, rfl⟩))
    (schemeCoverDegreeOneQuotient_mk_smul U hU M) E f heval
  trace "EXT008 P04 generic scalar descent complete"

end SchemeCover
end PfaffianDescent
