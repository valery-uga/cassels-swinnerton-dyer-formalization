import Mathlib.Tactic.Trace
import PfaffianDescent.CorayPushforwardCechGroundLinearity
import PfaffianDescent.CechExtDegreeOneLinearity
import PfaffianDescent.CorayNormalizationCohomologyOneComparison

/-! Linear upgrade of the SAME actual normalization H¹ comparison.
The actual pi and actual normalization composite induce the two category
actions; the installed Ext action and genuine kernel/quotient actions are
used. No comparison-linearity, QC or Ext-vanishing certificate is a premise
of either geometric endpoint. STATUS: UNVERIFIED source only.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {X Y : Scheme.{u}} {ι : Type u}

/-- The existing actual cocycle comparison preserves the actual original
field scalar actions on the genuine kernel submodules. -/
def schemeModulePushforwardCechOneCocycleLinearEquiv
    (pi : X ⟶ Spec (CommRingCat.of K)) (f : Y ⟶ X) (M : Y.Modules)
    (U : ι → X.Opens) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K Y.Modules := schemeModulesLinearOver (f ≫ pi)
    letI : Module K (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := (Scheme.Modules.pushforward f).obj M)) := degreeOneCocycleModuleOfLinear _
    letI : Module K (DegreeOneCocycle ((sectionRepresenterCechChain Y.ringCatSheaf
      (fun i => f ⁻¹ᵁ U i)).d 2 1) (Y := M)) := degreeOneCocycleModuleOfLinear _
    DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
        (Y := (Scheme.Modules.pushforward f).obj M) ≃ₗ[K]
      DegreeOneCocycle ((sectionRepresenterCechChain Y.ringCatSheaf
        (fun i => f ⁻¹ᵁ U i)).d 2 1) (Y := M) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K Y.Modules := schemeModulesLinearOver (f ≫ pi)
  letI : Module K (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
    (Y := (Scheme.Modules.pushforward f).obj M)) := degreeOneCocycleModuleOfLinear _
  letI : Module K (DegreeOneCocycle ((sectionRepresenterCechChain Y.ringCatSheaf
    (fun i => f ⁻¹ᵁ U i)).d 2 1) (Y := M)) := degreeOneCocycleModuleOfLinear _
  refine
    { toAddEquiv := schemeModulePushforwardCechOneCocycleAddEquiv f M U
      map_smul' := ?_ }
  intro c z
  apply Subtype.ext
  exact schemeModulePushforwardCechHomAddEquiv_smul pi f M U 1 c z.1

/-- Ordinary descent of representative scalar compatibility through two
existing quotient maps and an existing additive equivalence. -/
private def linearEquivOfQuotientRepresentatives
    {C D Q T : Type*} [AddCommGroup C] [AddCommGroup D]
    [AddCommGroup Q] [AddCommGroup T]
    [Module K C] [Module K D] [Module K Q] [Module K T]
    (mkX : C → Q) (hmkX : Function.Surjective mkX)
    (hX : ∀ (c : K) (z : C), mkX (c • z) = c • mkX z)
    (mkY : D → T) (hY : ∀ (c : K) (z : D), mkY (c • z) = c • mkY z)
    (E : Q ≃+ T) (F : C →ₗ[K] D)
    (heval : ∀ z, E (mkX z) = mkY (F z)) : Q ≃ₗ[K] T where
  toAddEquiv := E
  map_smul' c q := by
    obtain ⟨z, rfl⟩ := hmkX q
    calc
      E (c • mkX z) = E (mkX (c • z)) := congrArg E (hX c z).symm
      _ = mkY (F (c • z)) := heval (c • z)
      _ = mkY (c • F z) := congrArg mkY (F.map_smul c z)
      _ = c • mkY (F z) := hY c (F z)
      _ = c • E (mkX z) := congrArg (fun w => c • w) (heval z).symm

/-- Evaluate the SAME actual additive quotient transport on a representative.
This isolates quotient-map evaluation from all scalar-action computation. -/
private theorem schemeModulePushforwardCechOneQuotientAddEquiv_mk
    (f : Y ⟶ X) (M : Y.Modules) (U : ι → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules]
    (z : DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := (Scheme.Modules.pushforward f).obj M)) :
    schemeModulePushforwardCechOneQuotientAddEquiv f M U hU (QuotientAddGroup.mk z) =
      (QuotientAddGroup.mk (schemeModulePushforwardCechOneCocycleAddEquiv f M U z) :
        DegreeOneCocycle ((sectionRepresenterCechChain Y.ringCatSheaf
          (fun i => f ⁻¹ᵁ U i)).d 2 1) (Y := M) ⧸
          (schemeCoverDegreeOneToExtHom (fun i => f ⁻¹ᵁ U i)
            (schemeModulePushforward_preimageFamily_coversTop f U hU) M).ker) := by
  rfl

/-- The existing natural quotient action is evaluated on a representative.
The action is not transported through the additive equivalence. -/
private theorem schemeModuleNaturalCechOneQuotient_mk_smul
    (pi : X ⟶ Spec (CommRingCat.of K))
    (U : ι → X.Opens) (hU : (Opens.grothendieckTopology X).CoversTop U)
    (M : X.Modules) [HasExt.{u} X.Modules] (c : K)
    (z : DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := M)) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Module K (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := M)) := degreeOneCocycleModuleOfLinear _
    letI : Module K
      (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1) (Y := M) ⧸
        (schemeCoverDegreeOneToExtHom U hU M).ker) :=
      schemeCoverDegreeOneQuotientModuleOfLinear U hU M
    (QuotientAddGroup.mk (c • z) :
      DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1) (Y := M) ⧸
        (schemeCoverDegreeOneToExtHom U hU M).ker) = c • QuotientAddGroup.mk z := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Module K (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
    (Y := M)) := degreeOneCocycleModuleOfLinear _
  letI : Module K
    (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1) (Y := M) ⧸
      (schemeCoverDegreeOneToExtHom U hU M).ker) :=
    schemeCoverDegreeOneQuotientModuleOfLinear U hU M
  rfl

/-- The SAME actual two connecting-kernel quotients are linearly equivalent
for their natural quotient actions. Actual kernel transport was proved in
the frozen additive packet; scalar compatibility is proved on actual
representatives from actual cocycle compatibility. -/
def schemeModulePushforwardCechOneQuotientLinearEquiv
    (pi : X ⟶ Spec (CommRingCat.of K)) (f : Y ⟶ X) (M : Y.Modules)
    (U : ι → X.Opens) (hU : (Opens.grothendieckTopology X).CoversTop U)
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules] :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K Y.Modules := schemeModulesLinearOver (f ≫ pi)
    letI : Module K
      (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
          (Y := (Scheme.Modules.pushforward f).obj M) ⧸
        (schemeCoverDegreeOneToExtHom U hU ((Scheme.Modules.pushforward f).obj M)).ker) :=
      schemeCoverDegreeOneQuotientModuleOfLinear U hU ((Scheme.Modules.pushforward f).obj M)
    letI : Module K
      (DegreeOneCocycle ((sectionRepresenterCechChain Y.ringCatSheaf
          (fun i => f ⁻¹ᵁ U i)).d 2 1) (Y := M) ⧸
        (schemeCoverDegreeOneToExtHom (fun i => f ⁻¹ᵁ U i)
          (schemeModulePushforward_preimageFamily_coversTop f U hU) M).ker) :=
      schemeCoverDegreeOneQuotientModuleOfLinear (fun i => f ⁻¹ᵁ U i)
        (schemeModulePushforward_preimageFamily_coversTop f U hU) M
    (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
        (Y := (Scheme.Modules.pushforward f).obj M) ⧸
      (schemeCoverDegreeOneToExtHom U hU ((Scheme.Modules.pushforward f).obj M)).ker) ≃ₗ[K]
    (DegreeOneCocycle ((sectionRepresenterCechChain Y.ringCatSheaf
        (fun i => f ⁻¹ᵁ U i)).d 2 1) (Y := M) ⧸
      (schemeCoverDegreeOneToExtHom (fun i => f ⁻¹ᵁ U i)
        (schemeModulePushforward_preimageFamily_coversTop f U hU) M).ker) := by
  trace "NORM004 Q00 quotient proof entry"
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K Y.Modules := schemeModulesLinearOver (f ≫ pi)
  let hV := schemeModulePushforward_preimageFamily_coversTop f U hU
  let V : ι → Y.Opens := fun i => f ⁻¹ᵁ U i
  let P := (Scheme.Modules.pushforward f).obj M
  letI : Module K (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
    (Y := P)) := degreeOneCocycleModuleOfLinear _
  letI : Module K (DegreeOneCocycle ((sectionRepresenterCechChain Y.ringCatSheaf V).d 2 1)
    (Y := M)) := degreeOneCocycleModuleOfLinear _
  letI : Module K
      (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1) (Y := P) ⧸
        (schemeCoverDegreeOneToExtHom U hU P).ker) := schemeCoverDegreeOneQuotientModuleOfLinear U hU P
  letI : Module K
      (DegreeOneCocycle ((sectionRepresenterCechChain Y.ringCatSheaf V).d 2 1) (Y := M) ⧸
        (schemeCoverDegreeOneToExtHom V hV M).ker) := schemeCoverDegreeOneQuotientModuleOfLinear V hV M
  trace "NORM004 Q01 natural Modules installed"
  let E := schemeModulePushforwardCechOneQuotientAddEquiv f M U hU
  let F := (schemeModulePushforwardCechOneCocycleLinearEquiv pi f M U).toLinearMap
  trace "NORM004 Q02 original additive and cocycle linear maps formed"
  have heval : ∀ z, E (QuotientAddGroup.mk z) = QuotientAddGroup.mk (F z) := by
    intro z
    exact schemeModulePushforwardCechOneQuotientAddEquiv_mk f M U hU z
  trace "NORM004 Q03 representative evaluation certificate formed"
  exact linearEquivOfQuotientRepresentatives QuotientAddGroup.mk
    (fun q => QuotientAddGroup.induction_on q (fun z => ⟨z, rfl⟩))
    (schemeModuleNaturalCechOneQuotient_mk_smul pi U hU P)
    QuotientAddGroup.mk
    (schemeModuleNaturalCechOneQuotient_mk_smul (f ≫ pi) V hV M)
    E F heval
  trace "NORM004 Q04 generic scalar descent complete"

/-- Ordinary inverse with the scalar modules still abstract. -/
private def originalScalarLinearEquivInverse
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module K A] [Module K B] (E : A ≃ₗ[K] B) : B ≃ₗ[K] A :=
  E.symm

/-- Ordinary composition with the scalar modules still abstract. -/
private def originalScalarLinearEquivCompose
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C]
    (E : A ≃ₗ[K] B) (F : B ≃ₗ[K] C) : A ≃ₗ[K] C :=
  E.trans F

/-- The original cover comparison inverted at an abstract native scheme. -/
private def schemeModuleCechOneInverseLinearEquiv
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (U : ι → X.Opens) (hU : (Opens.grothendieckTopology X).CoversTop U)
    [HasExt.{u} X.Modules]
    [Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf U).X 0) M 1)] :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Module K
      (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1) (Y := M) ⧸
        (schemeCoverDegreeOneToExtHom U hU M).ker) :=
      schemeCoverDegreeOneQuotientModuleOfLinear U hU M
    schemeModuleCohomology X M 1 ≃ₗ[K]
      (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1) (Y := M) ⧸
        (schemeCoverDegreeOneToExtHom U hU M).ker) := by
  trace "NORM007 I00 native inverse entry"
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Module K
    (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1) (Y := M) ⧸
      (schemeCoverDegreeOneToExtHom U hU M).ker) :=
    schemeCoverDegreeOneQuotientModuleOfLinear U hU M
  exact originalScalarLinearEquivInverse
    (schemeCoverDegreeOneQuotientLinearEquivCohomologyOne (R := K) U hU M)
  trace "NORM007 I01 native inverse application complete"

/-- Actual quotient transport followed by the actual target cover comparison. -/
private def schemeModulePushforwardCechOneQuotientToCohomologyLinearEquiv
    (pi : X ⟶ Spec (CommRingCat.of K)) (f : Y ⟶ X) (M : Y.Modules)
    (U : ι → X.Opens) (hU : (Opens.grothendieckTopology X).CoversTop U)
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules]
    [Subsingleton (Ext.{u} (C := Y.Modules)
      (show Y.Modules from (sectionRepresenterCechChain Y.ringCatSheaf
        (fun i => f ⁻¹ᵁ U i)).X 0) M 1)] :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K Y.Modules := schemeModulesLinearOver (f ≫ pi)
    letI : Module K
      (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
          (Y := (Scheme.Modules.pushforward f).obj M) ⧸
        (schemeCoverDegreeOneToExtHom U hU ((Scheme.Modules.pushforward f).obj M)).ker) :=
      schemeCoverDegreeOneQuotientModuleOfLinear U hU ((Scheme.Modules.pushforward f).obj M)
    (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
        (Y := (Scheme.Modules.pushforward f).obj M) ⧸
      (schemeCoverDegreeOneToExtHom U hU ((Scheme.Modules.pushforward f).obj M)).ker) ≃ₗ[K]
      schemeModuleCohomology Y M 1 := by
  trace "NORM007 T00 quotient to target cohomology entry"
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K Y.Modules := schemeModulesLinearOver (f ≫ pi)
  let V : ι → Y.Opens := fun i => f ⁻¹ᵁ U i
  let hV := schemeModulePushforward_preimageFamily_coversTop f U hU
  let P := (Scheme.Modules.pushforward f).obj M
  letI : Module K (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := P) ⧸ (schemeCoverDegreeOneToExtHom U hU P).ker) :=
    schemeCoverDegreeOneQuotientModuleOfLinear U hU P
  letI : Module K (DegreeOneCocycle ((sectionRepresenterCechChain Y.ringCatSheaf V).d 2 1)
      (Y := M) ⧸ (schemeCoverDegreeOneToExtHom V hV M).ker) :=
    schemeCoverDegreeOneQuotientModuleOfLinear V hV M
  let EN := schemeCoverDegreeOneQuotientLinearEquivCohomologyOne (R := K) V hV M
  let EQ := schemeModulePushforwardCechOneQuotientLinearEquiv pi f M U hU
  trace "NORM007 T01 actual EQ and EN formed"
  exact originalScalarLinearEquivCompose EQ EN
  trace "NORM007 T02 quotient to target composition complete"

/-- Ordinary actual cover composition with the scheme morphism still abstract.
Normalization callers construct both local Ext inputs internally. -/
private def schemeModulePushforwardCechOneCohomologyLinearEquiv
    (pi : X ⟶ Spec (CommRingCat.of K)) (f : Y ⟶ X) (M : Y.Modules)
    (U : ι → X.Opens) (hU : (Opens.grothendieckTopology X).CoversTop U)
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules]
    [Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf U).X 0)
      ((Scheme.Modules.pushforward f).obj M) 1)]
    [Subsingleton (Ext.{u} (C := Y.Modules)
      (show Y.Modules from (sectionRepresenterCechChain Y.ringCatSheaf
        (fun i => f ⁻¹ᵁ U i)).X 0) M 1)] :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K Y.Modules := schemeModulesLinearOver (f ≫ pi)
    schemeModuleCohomology X ((Scheme.Modules.pushforward f).obj M) 1 ≃ₗ[K]
      schemeModuleCohomology Y M 1 := by
  trace "NORM007 A00 final abstract cover assembly entry"
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K Y.Modules := schemeModulesLinearOver (f ≫ pi)
  let P := (Scheme.Modules.pushforward f).obj M
  letI : Module K (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := P) ⧸ (schemeCoverDegreeOneToExtHom U hU P).ker) :=
    schemeCoverDegreeOneQuotientModuleOfLinear U hU P
  let invEX := schemeModuleCechOneInverseLinearEquiv pi P U hU
  trace "NORM007 A01 opaque native inverse formed"
  let EQEN := schemeModulePushforwardCechOneQuotientToCohomologyLinearEquiv pi f M U hU
  trace "NORM007 A02 opaque native quotient to target map formed"
  exact originalScalarLinearEquivCompose invEX EQEN
  trace "NORM007 A03 final opaque composition complete"

/-- Actual K-linear normalization H¹ comparison with only ordinary original
CharZero finite-type integral geometry. Every scalar, cover, local QC/Ext
and degree-zero Ext input is constructed internally. The underlying map is
the previous actual additive comparison, as proved below. -/
def genericNormalizationPushforwardUnit_cohomologyOneLinearEquiv
    [CharZero K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
    schemeModuleCohomology X
        ((Scheme.Modules.pushforward ν).obj (SheafOfModules.unit N.ringCatSheaf)) 1 ≃ₗ[K]
      schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1 := by
  trace "NORM006 N00 actual normalization proof entry"
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
  letI : IsFinite ν := integralScheme_genericNormalization_isFinite X pi
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pi
  letI : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian ν
  let U : X.affineOpens → X.Opens := fun i => i.1
  let V : X.affineOpens → N.Opens := fun i => ν ⁻¹ᵁ i.1
  let M : N.Modules := SheafOfModules.unit N.ringCatSheaf
  let P : X.Modules := (Scheme.Modules.pushforward ν).obj M
  let hU := genericNormalization_affineOpenFamily_coversTop X
  let hV := genericNormalization_preimageAffineOpenFamily_coversTop X
  letI : Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf U).X 0) P 1) :=
    genericNormalizationPushforwardUnit_affineFamily_degreeZeroExt_one_subsingleton U (fun i => i.2)
  letI : ∀ i, Subsingleton (Ext.{u} (C := N.Modules)
      (show N.Modules from sectionRepresenter N.ringCatSheaf (V i)) M 1) := fun i =>
    (sectionRepresenter_ext_one_and_two_subsingleton_of_isAffineOpen_of_restrict
      (V i) (i.2.preimage ν) M
      (schemeModuleUnit_restrictFromSpec_isQuasicoherent N (V i) (i.2.preimage ν))).1
  letI : Subsingleton (Ext.{u} (C := N.Modules)
      (show N.Modules from (sectionRepresenterCechChain N.ringCatSheaf V).X 0) M 1) :=
    schemeCover_degree_zero_ext_one_subsingleton V M
  trace "NORM006 N01 actual local Ext inputs installed / before abstract assembly"
  exact schemeModulePushforwardCechOneCohomologyLinearEquiv pi ν M U hU
  trace "NORM006 N02 actual assembly application complete"

/-- This upgrades the SAME actual additive normalization comparison from
the frozen packet, rather than choosing an unrelated linear identification. -/
theorem genericNormalizationPushforwardUnit_cohomologyOneLinearEquiv_toAddEquiv
    [CharZero K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
    (genericNormalizationPushforwardUnit_cohomologyOneLinearEquiv X pi).toAddEquiv =
      genericNormalizationPushforwardUnit_cohomologyOneAddEquiv X pi := by
  rfl

/-- Literal original homogeneous p/q caller with the original field action
and the actual normalization composite action. No linearity/vanishing
certificate is supplied; all geometry and scalar construction is internal. -/
def projectiveIntersection_genericNormalizationPushforwardUnit_cohomologyOneLinearEquiv
    [CharZero K] (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hq : q.IsHomogeneous n)
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver (toBase I)
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ toBase I)
    schemeModuleCohomology X
        ((Scheme.Modules.pushforward ν).obj (SheafOfModules.unit N.ringCatSheaf)) 1 ≃ₗ[K]
      schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1 := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : LocallyOfFiniteType (toBase I) := inferInstance
  exact genericNormalizationPushforwardUnit_cohomologyOneLinearEquiv X (toBase I)

end PfaffianDescent.Coray
