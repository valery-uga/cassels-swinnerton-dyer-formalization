import PfaffianDescent.CorayNormalizationCohomologyOneLinearComparison
import PfaffianDescent.CorayPerfectFiniteSchemeGenericNormalization

/-! SOURCE ONLY / UNVERIFIED. Perfect-field upgrade of SAME actual native
normalization H1 LINEAR comparison. Original pi and nu>>pi independently
induce category/Ext actions. Existing representative and quotient maps are
reused literally; no module action is transported through an equivalence.
No finite-H1, constants, genus, support or comparison premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {X Y : Scheme.{u}} {ι : Type u}

/-- Ordinary inverse with the scalar modules still abstract. -/
private def perfectField_originalScalarLinearEquivInverse
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module K A] [Module K B] (E : A ≃ₗ[K] B) : B ≃ₗ[K] A :=
  E.symm

/-- Ordinary composition with the scalar modules still abstract. -/
private def perfectField_originalScalarLinearEquivCompose
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C]
    (E : A ≃ₗ[K] B) (F : B ≃ₗ[K] C) : A ≃ₗ[K] C :=
  E.trans F

/-- The original cover comparison inverted at an abstract native scheme. -/
private def perfectField_schemeModuleCechOneInverseLinearEquiv
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
  exact perfectField_originalScalarLinearEquivInverse
    (schemeCoverDegreeOneQuotientLinearEquivCohomologyOne (R := K) U hU M)
  trace "NORM007 I01 native inverse application complete"

/-- Actual quotient transport followed by the actual target cover comparison. -/
private def perfectField_schemeModulePushforwardCechOneQuotientToCohomologyLinearEquiv
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
  exact perfectField_originalScalarLinearEquivCompose EQ EN
  trace "NORM007 T02 quotient to target composition complete"

/-- Ordinary actual cover composition with the scheme morphism still abstract.
Normalization callers construct both local Ext inputs internally. -/
private def perfectField_schemeModulePushforwardCechOneCohomologyLinearEquiv
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
  let invEX := perfectField_schemeModuleCechOneInverseLinearEquiv pi P U hU
  trace "NORM007 A01 opaque native inverse formed"
  let EQEN := perfectField_schemeModulePushforwardCechOneQuotientToCohomologyLinearEquiv pi f M U hU
  trace "NORM007 A02 opaque native quotient to target map formed"
  exact perfectField_originalScalarLinearEquivCompose invEX EQEN
  trace "NORM007 A03 final opaque composition complete"

/-- Actual K-linear normalization H¹ comparison with only ordinary original
PerfectField finite-type integral geometry. Every scalar, cover, local QC/Ext
and degree-zero Ext input is constructed internally. The representative and quotient comparison maps are the SAME already
constructed literal original-scalar maps, composed in the same order. -/
def perfectField_genericNormalizationPushforwardUnit_cohomologyOneLinearEquiv
    [PerfectField K] (X : Scheme.{u}) [IsIntegral X]
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
  letI : IsFinite ν := perfectField_integralScheme_genericNormalization_isFinite X pi
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
  exact perfectField_schemeModulePushforwardCechOneCohomologyLinearEquiv pi ν M U hU
  trace "NORM006 N02 actual assembly application complete"

/-- Ordinary literal identity on the CharZero overlap, not an assumption. -/
private theorem perfectField_normalizationLinearComparison_eq_charZero
    [PerfectField K] [CharZero K] (X : Scheme.{u}) [IsIntegral X]
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
    perfectField_genericNormalizationPushforwardUnit_cohomologyOneLinearEquiv X pi =
      genericNormalizationPushforwardUnit_cohomologyOneLinearEquiv X pi := by
  rfl

end PfaffianDescent.Coray
