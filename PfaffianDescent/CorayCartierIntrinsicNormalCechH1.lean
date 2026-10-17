import PfaffianDescent.CorayCartierIntrinsicNormalPushforwardQuasicoherent
import PfaffianDescent.CorayNormalizationCohomologyOneLinearComparison

/-! Actual Cartier intrinsic/ambient H1 comparison through the original affine
cover and original section-representer cocycles. QC and acyclicity are derived
internally. This does NOT identify the comparison with the canonical
right-adjoint Ext map; that additional naturality equality remains open.
SOURCE ONLY / UNVERIFIED. Root owns all compiler checks. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace
universe u
variable {K : Type u} [Field K] {X Y : Scheme.{u}} {ι : Type u}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Ordinary inverse with the scalar modules still abstract. -/
private def cartierOriginalScalarLinearEquivInverse
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module K A] [Module K B] (E : A ≃ₗ[K] B) : B ≃ₗ[K] A :=
  E.symm

/-- Ordinary composition with the scalar modules still abstract. -/
private def cartierOriginalScalarLinearEquivCompose
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C]
    (E : A ≃ₗ[K] B) (F : B ≃ₗ[K] C) : A ≃ₗ[K] C :=
  E.trans F

/-- The original cover comparison inverted at an abstract native scheme. -/
private def cartierSchemeModuleCechOneInverseLinearEquiv
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
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Module K
    (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1) (Y := M) ⧸
      (schemeCoverDegreeOneToExtHom U hU M).ker) :=
    schemeCoverDegreeOneQuotientModuleOfLinear U hU M
  exact cartierOriginalScalarLinearEquivInverse
    (schemeCoverDegreeOneQuotientLinearEquivCohomologyOne (R := K) U hU M)

/-- Actual quotient transport followed by the actual target cover comparison. -/
private def cartierSchemeModulePushforwardCechOneQuotientToCohomologyLinearEquiv
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
  exact cartierOriginalScalarLinearEquivCompose EQ EN

/-- Ordinary actual cover composition with the scheme morphism still abstract.
Normalization callers construct both local Ext inputs internally. -/
private def cartierSchemeModulePushforwardCechOneCohomologyLinearEquiv
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
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K Y.Modules := schemeModulesLinearOver (f ≫ pi)
  let P := (Scheme.Modules.pushforward f).obj M
  letI : Module K (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := P) ⧸ (schemeCoverDegreeOneToExtHom U hU P).ker) :=
    schemeCoverDegreeOneQuotientModuleOfLinear U hU P
  let invEX := cartierSchemeModuleCechOneInverseLinearEquiv pi P U hU
  let EQEN := cartierSchemeModulePushforwardCechOneQuotientToCohomologyLinearEquiv pi f M U hU
  exact cartierOriginalScalarLinearEquivCompose invEX EQEN


private theorem cartierAffineFamilyDegreeZeroExtOne
    (M : X.Modules) [IsLocallyNoetherian X] [HasExt.{u} X.Modules]
    [M.IsQuasicoherent] :
    Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf
        (fun a : X.affineOpens => a.1)).X 0) M 1) := by
  let U : X.affineOpens → X.Opens := fun a => a.1
  letI : ∀ a, Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from sectionRepresenter X.ringCatSheaf (U a)) M 1) := fun a =>
    (sectionRepresenter_ext_one_and_two_subsingleton_of_isAffineOpen (U a) a.2 M).1
  exact schemeCover_degree_zero_ext_one_subsingleton U M

private theorem cartierPreimageAffineFamilyDegreeZeroExtOne
    (f : Y ⟶ X) [IsClosedImmersion f] (M : Y.Modules)
    [IsLocallyNoetherian Y] [HasExt.{u} Y.Modules] [M.IsQuasicoherent] :
    Subsingleton (Ext.{u} (C := Y.Modules)
      (show Y.Modules from (sectionRepresenterCechChain Y.ringCatSheaf
        (fun a : X.affineOpens => f ⁻¹ᵁ a.1)).X 0) M 1) := by
  let V : X.affineOpens → Y.Opens := fun a => f ⁻¹ᵁ a.1
  letI : ∀ a, Subsingleton (Ext.{u} (C := Y.Modules)
      (show Y.Modules from sectionRepresenter Y.ringCatSheaf (V a)) M 1) := fun a =>
    (sectionRepresenter_ext_one_and_two_subsingleton_of_isAffineOpen
      (V a) (a.2.preimage f) M).1
  exact schemeCover_degree_zero_ext_one_subsingleton V M

/-- Original affine-cover comparison for the actual intrinsic normal
coefficient. Both QC and every degree-zero Ext vanishing input come from
OWN regular geometry, not supplied comparison or acyclicity hypotheses. -/
def RegularPrincipalImmersion.actualIntrinsicNormal_cohomologyOneCechLinearEquiv
    (pi : X ⟶ Spec (CommRingCat.of K)) (i : Y ⟶ X) [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules] :
    let D := schemeModuleTensor ((Scheme.Modules.pullback i).obj W)
      (SchemeModuleInternalHom.dual (actualClosedImmersionConormalModule i))
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K Y.Modules := schemeModulesLinearOver (i ≫ pi)
    schemeModuleCohomology X ((Scheme.Modules.pushforward i).obj D) 1 ≃ₗ[K]
      schemeModuleCohomology Y D 1 := by
  let D := schemeModuleTensor ((Scheme.Modules.pullback i).obj W)
    (SchemeModuleInternalHom.dual (actualClosedImmersionConormalModule i))
  let P := (Scheme.Modules.pushforward i).obj D
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K Y.Modules := schemeModulesLinearOver (i ≫ pi)
  have hQC := H.actualIntrinsicNormalCoefficient_and_pushforward_isQuasicoherent W hW
  letI : D.IsQuasicoherent := hQC.1
  letI : P.IsQuasicoherent := hQC.2
  let U : X.affineOpens → X.Opens := fun a => a.1
  letI : Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf U).X 0) P 1) :=
    cartierAffineFamilyDegreeZeroExtOne P
  letI : Subsingleton (Ext.{u} (C := Y.Modules)
      (show Y.Modules from (sectionRepresenterCechChain Y.ringCatSheaf
        (fun a : X.affineOpens => i ⁻¹ᵁ a.1)).X 0) D 1) :=
    cartierPreimageAffineFamilyDegreeZeroExtOne i D
  exact cartierSchemeModulePushforwardCechOneCohomologyLinearEquiv pi i D U
    (genericNormalization_affineOpenFamily_coversTop X)

private theorem cartierLinearEquivRepresentativeTransport
    {A B C D : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup D]
    [Module K A] [Module K B] [Module K C] [Module K D]
    (E : A ≃ₗ[K] B) (F : A ≃ₗ[K] C) (G : C ≃ₗ[K] D) (a : A) :
    cartierOriginalScalarLinearEquivCompose
      (cartierOriginalScalarLinearEquivInverse E)
      (cartierOriginalScalarLinearEquivCompose F G) (E a) = G (F a) := by
  change G (F (E.symm (E a))) = G (F a)
  rw [LinearEquiv.symm_apply_apply]

private theorem cartierCechH1RepresentativeTransport
    (pi : X ⟶ Spec (CommRingCat.of K)) (f : Y ⟶ X) (M : Y.Modules)
    (U : ι → X.Opens) (hU : (Opens.grothendieckTopology X).CoversTop U)
    [hExtX : HasExt.{u} X.Modules] [hExtY : HasExt.{u} Y.Modules]
    [Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf U).X 0)
      ((Scheme.Modules.pushforward f).obj M) 1)]
    [Subsingleton (Ext.{u} (C := Y.Modules)
      (show Y.Modules from (sectionRepresenterCechChain Y.ringCatSheaf
        (fun a => f ⁻¹ᵁ U a)).X 0) M 1)]
    (z : DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := (Scheme.Modules.pushforward f).obj M)) :
    letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExtX
    letI : HasExt.{u} (SheafOfModules.{u} Y.ringCatSheaf) := hExtY
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K Y.Modules := schemeModulesLinearOver (f ≫ pi)
    cartierSchemeModulePushforwardCechOneCohomologyLinearEquiv pi f M U hU
      ((Ext.mk₀ (C := X.Modules) (schemeCoverCechTargetIsoUnit U).inv).comp
        (schemeCoverDegreeOneToExtHom U hU ((Scheme.Modules.pushforward f).obj M) z)
          (zero_add 1)) =
      (Ext.mk₀ (C := Y.Modules) (schemeCoverCechTargetIsoUnit (fun a => f ⁻¹ᵁ U a)).inv).comp
        (schemeCoverDegreeOneToExtHom (fun a => f ⁻¹ᵁ U a)
          (schemeModulePushforward_preimageFamily_coversTop f U hU) M
          (schemeModulePushforwardCechOneCocycleAddEquiv f M U z)) (zero_add 1) := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExtX
  letI : HasExt.{u} (SheafOfModules.{u} Y.ringCatSheaf) := hExtY
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K Y.Modules := schemeModulesLinearOver (f ≫ pi)
  let V : ι → Y.Opens := fun a => f ⁻¹ᵁ U a
  let hV := schemeModulePushforward_preimageFamily_coversTop f U hU
  let P := (Scheme.Modules.pushforward f).obj M
  letI : Module K (DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := P) ⧸ (schemeCoverDegreeOneToExtHom U hU P).ker) :=
    schemeCoverDegreeOneQuotientModuleOfLinear U hU P
  letI : Module K (DegreeOneCocycle ((sectionRepresenterCechChain Y.ringCatSheaf V).d 2 1)
      (Y := M) ⧸ (schemeCoverDegreeOneToExtHom V hV M).ker) :=
    schemeCoverDegreeOneQuotientModuleOfLinear V hV M
  let EX := schemeCoverDegreeOneQuotientLinearEquivCohomologyOne (R := K) U hU P
  let EQ := schemeModulePushforwardCechOneQuotientLinearEquiv pi f M U hU
  let EN := schemeCoverDegreeOneQuotientLinearEquivCohomologyOne (R := K) V hV M
  have he := cartierLinearEquivRepresentativeTransport EX EQ EN (QuotientAddGroup.mk z)
  change cartierSchemeModulePushforwardCechOneCohomologyLinearEquiv pi f M U hU
    (EX (QuotientAddGroup.mk z)) = EN (EQ (QuotientAddGroup.mk z)) at he
  exact he

/-- Literal transport of an ORIGINAL cocycle representative and its actual
unit-precomposed Ext class. This fixes the actual map beyond an abstract
existence of a K-linear identification. Canonical right-adjoint Ext
compatibility is a separate result, not asserted by this equation. -/
theorem RegularPrincipalImmersion.actualIntrinsicNormal_cohomologyOneCechLinearEquiv_representative
    (pi : X ⟶ Spec (CommRingCat.of K)) (i : Y ⟶ X) [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [hExtX : HasExt.{u} X.Modules] [hExtY : HasExt.{u} Y.Modules]
    (z : DegreeOneCocycle
      ((sectionRepresenterCechChain X.ringCatSheaf (fun a : X.affineOpens => a.1)).d 2 1)
      (Y := (Scheme.Modules.pushforward i).obj
        (schemeModuleTensor ((Scheme.Modules.pullback i).obj W)
          (SchemeModuleInternalHom.dual (actualClosedImmersionConormalModule i))))) :
    let D := schemeModuleTensor ((Scheme.Modules.pullback i).obj W)
      (SchemeModuleInternalHom.dual (actualClosedImmersionConormalModule i))
    let U : X.affineOpens → X.Opens := fun a => a.1
    let hU := genericNormalization_affineOpenFamily_coversTop X
    letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExtX
    letI : HasExt.{u} (SheafOfModules.{u} Y.ringCatSheaf) := hExtY
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K Y.Modules := schemeModulesLinearOver (i ≫ pi)
    PfaffianDescent.Coray.RegularPrincipalImmersion.actualIntrinsicNormal_cohomologyOneCechLinearEquiv pi i H W hW
      ((Ext.mk₀ (C := X.Modules) (schemeCoverCechTargetIsoUnit U).inv).comp
        (schemeCoverDegreeOneToExtHom U hU ((Scheme.Modules.pushforward i).obj D) z)
          (zero_add 1)) =
      (Ext.mk₀ (C := Y.Modules) (schemeCoverCechTargetIsoUnit (fun a => i ⁻¹ᵁ U a)).inv).comp
        (schemeCoverDegreeOneToExtHom (fun a => i ⁻¹ᵁ U a)
          (schemeModulePushforward_preimageFamily_coversTop i U hU) D
          (schemeModulePushforwardCechOneCocycleAddEquiv i D U z)) (zero_add 1) := by
  let D := schemeModuleTensor ((Scheme.Modules.pullback i).obj W)
    (SchemeModuleInternalHom.dual (actualClosedImmersionConormalModule i))
  let P := (Scheme.Modules.pushforward i).obj D
  let U : X.affineOpens → X.Opens := fun a => a.1
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExtX
  letI : HasExt.{u} (SheafOfModules.{u} Y.ringCatSheaf) := hExtY
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K Y.Modules := schemeModulesLinearOver (i ≫ pi)
  have hQC := H.actualIntrinsicNormalCoefficient_and_pushforward_isQuasicoherent W hW
  letI : D.IsQuasicoherent := hQC.1
  letI : P.IsQuasicoherent := hQC.2
  letI : Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf U).X 0) P 1) :=
    cartierAffineFamilyDegreeZeroExtOne P
  letI : Subsingleton (Ext.{u} (C := Y.Modules)
      (show Y.Modules from (sectionRepresenterCechChain Y.ringCatSheaf
        (fun a : X.affineOpens => i ⁻¹ᵁ a.1)).X 0) D 1) :=
    cartierPreimageAffineFamilyDegreeZeroExtOne i D
  exact cartierCechH1RepresentativeTransport pi i D U
    (genericNormalization_affineOpenFamily_coversTop X) z

end PfaffianDescent.Coray
end
