import PfaffianDescent.SchemeModuleInternalHomPrecompose
import PfaffianDescent.SchemeModuleInternalHomRankOneTargetEvaluation
import PfaffianDescent.CorayCartierPullbackIntrinsicDual
import PfaffianDescent.ActualClosedPointConormalNativeTensorFiber

/-! Actual Hom/precomposition presentation of the OWN Cartier residue.
This is a native Hom cokernel, not a proved global dualizing/Serre property.
SOURCE ONLY / UNVERIFIED. Root owns compilers and acceptance. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Canonical W ~= internalHom(O,W), by currying the original unitor. -/
def SchemeModuleInternalHom.unitTensorHomIso
    {X : Scheme.{u}} (W : X.Modules) :
    W ≅ SchemeModuleInternalHom.sheaf (SheafOfModules.unit X.ringCatSheaf) W := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let hO : schemeModuleLocallyRankOne O := by
    intro x
    exact ⟨⊤, by trivial, ⟨Iso.refl _⟩⟩
  let p := (schemeModuleTensorUnitLeftIso W).hom
  let hp : IsIso p := (schemeModuleTensorUnitLeftIso W).isIso_hom
  let hg : IsIso (SchemeModuleInternalHom.tensorCurry O W W p) :=
    @SchemeModuleInternalHom.tensorCurry_isIso_of_locallyRankOne X O W W hO p hp
  exact @asIso X.Modules (inferInstance : Category X.Modules) _ _
    (SchemeModuleInternalHom.tensorCurry O W W p) hg

/-- The actual residue increment evaluates to the literal ideal inclusion
on W. Monicity is derived from the genuine OWN short exact residue sequence. -/
theorem RegularPrincipalImmersion.actualCartierResidueIncrement_evaluation
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W) :
    schemeModuleTensorMap (𝟙 (IdealSheafDataModule.closedImmersionModule i))
        (schemeModuleRankOneTensorDualIncrement
          (IdealSheafDataModule.closedImmersionModuleToUnit i) W) ≫
      schemeModuleRankOneDualKernelMap (IdealSheafDataModule.closedImmersionModule i)
        W H.inverseCartierTwist_locallyRankOne =
    schemeModuleTensorMap (IdealSheafDataModule.closedImmersionModuleToUnit i) (𝟙 W) ≫
      (schemeModuleTensorUnitLeftIso W).hom := by
  let I := IdealSheafDataModule.closedImmersionModule i
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let j := IdealSheafDataModule.closedImmersionModuleToUnit i
  let T := schemeModuleTensor W (SchemeModuleInternalHom.dual I)
  let delta := schemeModuleRankOneTensorDualIncrement j W
  let K := schemeModuleRankOneDualKernelIso I W H.inverseCartierTwist_locallyRankOne
  let lW := schemeModuleTensorUnitLeftIso W
  let lT := schemeModuleTensorUnitLeftIso T
  letI : Mono delta := (H.actualCartierResidueSequence_shortExact W hW).mono_f
  have hK : K.hom ≫ delta = schemeModuleTensorMap j (𝟙 T) ≫ lT.hom :=
    schemeModuleRankOneDualKernelIso_action j W H.inverseCartierTwist_locallyRankOne
  have h1 : schemeModuleTensorMap (𝟙 I) delta ≫ schemeModuleTensorMap j (𝟙 T) =
      schemeModuleTensorMap j delta :=
    (schemeModuleTensorMap_comp (𝟙 I) delta j (𝟙 T)).trans
      (congrArg₂ (fun (a : I ⟶ O) (b : W ⟶ T) => schemeModuleTensorMap a b)
        (Category.id_comp j) (Category.comp_id delta))
  have h2 : schemeModuleTensorMap j (𝟙 W) ≫ schemeModuleTensorMap (𝟙 O) delta =
      schemeModuleTensorMap j delta :=
    (schemeModuleTensorMap_comp j (𝟙 W) (𝟙 O) delta).trans
      (congrArg₂ (fun (a : I ⟶ O) (b : W ⟶ T) => schemeModuleTensorMap a b)
        (Category.comp_id j) (Category.id_comp delta))
  have hn : schemeModuleTensorMap (𝟙 O) delta ≫ lT.hom = lW.hom ≫ delta :=
    schemeModuleTensorUnitLeftIso_naturality delta
  change schemeModuleTensorMap (𝟙 I) delta ≫ K.hom =
    schemeModuleTensorMap j (𝟙 W) ≫ lW.hom
  apply (cancel_mono delta).mp
  calc
    (schemeModuleTensorMap (𝟙 I) delta ≫ K.hom) ≫ delta =
        schemeModuleTensorMap (𝟙 I) delta ≫ (K.hom ≫ delta) := Category.assoc _ _ _
    _ = schemeModuleTensorMap (𝟙 I) delta ≫
        (schemeModuleTensorMap j (𝟙 T) ≫ lT.hom) :=
      congrArg (fun a => schemeModuleTensorMap (𝟙 I) delta ≫ a) hK
    _ = (schemeModuleTensorMap (𝟙 I) delta ≫ schemeModuleTensorMap j (𝟙 T)) ≫ lT.hom :=
      (Category.assoc _ _ _).symm
    _ = schemeModuleTensorMap j delta ≫ lT.hom := congrArg (fun a => a ≫ lT.hom) h1
    _ = (schemeModuleTensorMap j (𝟙 W) ≫ schemeModuleTensorMap (𝟙 O) delta) ≫ lT.hom :=
      congrArg (fun a => a ≫ lT.hom) h2.symm
    _ = schemeModuleTensorMap j (𝟙 W) ≫
        (schemeModuleTensorMap (𝟙 O) delta ≫ lT.hom) := Category.assoc _ _ _
    _ = schemeModuleTensorMap j (𝟙 W) ≫ (lW.hom ≫ delta) :=
      congrArg (fun a => schemeModuleTensorMap j (𝟙 W) ≫ a) hn
    _ = (schemeModuleTensorMap j (𝟙 W) ≫ lW.hom) ≫ delta := (Category.assoc _ _ _).symm

/-- Literal precomposition by the OWN inclusion is the SAME actual residue
increment in canonical native tensor/Hom coordinates. -/
theorem RegularPrincipalImmersion.actualCartierResidueIncrement_hom_square
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W) :
    schemeModuleRankOneTensorDualIncrement
        (IdealSheafDataModule.closedImmersionModuleToUnit i) W ≫
      (SchemeModuleInternalHom.rankOneTensorHomIso
        (IdealSheafDataModule.closedImmersionModule i) W H.inverseCartierTwist_locallyRankOne).hom =
    (SchemeModuleInternalHom.unitTensorHomIso W).hom ≫
      SchemeModuleInternalHom.precompose
        (IdealSheafDataModule.closedImmersionModuleToUnit i) W := by
  let I := IdealSheafDataModule.closedImmersionModule i
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let j := IdealSheafDataModule.closedImmersionModuleToUnit i
  let T := schemeModuleTensor W (SchemeModuleInternalHom.dual I)
  let delta := schemeModuleRankOneTensorDualIncrement j W
  let K := schemeModuleRankOneDualKernelMap I W H.inverseCartierTwist_locallyRankOne
  let L := (schemeModuleTensorUnitLeftIso W).hom
  have hB := SchemeModuleInternalHom.tensorCurry_map_right I delta W K
  have hEval : schemeModuleTensorMap (𝟙 I) delta ≫ K = schemeModuleTensorMap j (𝟙 W) ≫ L :=
    H.actualCartierResidueIncrement_evaluation W hW
  have hJ := SchemeModuleInternalHom.tensorCurry_precompose j W W L
  change delta ≫ SchemeModuleInternalHom.tensorCurry I T W K =
    SchemeModuleInternalHom.tensorCurry O W W L ≫ SchemeModuleInternalHom.precompose j W
  exact hB.symm.trans
    ((congrArg (SchemeModuleInternalHom.tensorCurry I W W) hEval).trans hJ)

/-- Actual arrow Iso between the residue increment and original Hom
precomposition. The square is derived internally from OWN regular geometry. -/
def RegularPrincipalImmersion.actualCartierResidueHomArrowIso
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W) :
    Arrow.mk (H.actualCartierResidueSequence W).f ≅
      Arrow.mk (SchemeModuleInternalHom.precompose
        (IdealSheafDataModule.closedImmersionModuleToUnit i) W) :=
  Arrow.isoMk (SchemeModuleInternalHom.unitTensorHomIso W)
    (SchemeModuleInternalHom.rankOneTensorHomIso
      (IdealSheafDataModule.closedImmersionModule i) W H.inverseCartierTwist_locallyRankOne)
    (H.actualCartierResidueIncrement_hom_square W hW).symm

/-- The canonical cokernel of original Hom precomposition is the actual
residue quotient, through its OWN genuine short-exact cofork. -/
def RegularPrincipalImmersion.actualCartierResidueHomCokernelIso
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W) :
    cokernel (SchemeModuleInternalHom.precompose
      (IdealSheafDataModule.closedImmersionModuleToUnit i) W) ≅
      (H.actualCartierResidueSequence W).X₃ :=
  CokernelCofork.mapIsoOfIsColimit (cokernelIsCokernel _)
    (H.actualCartierResidueSequence_shortExact W hW).gIsCokernel
    (H.actualCartierResidueHomArrowIso W hW).symm

/-- The actual quotient hom retains the ORIGINAL cokernel projection
and actual residue restriction in native Hom coordinates. -/
theorem RegularPrincipalImmersion.actualCartierResidueHomCokernelIso_projection
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W) :
    cokernel.π (SchemeModuleInternalHom.precompose
        (IdealSheafDataModule.closedImmersionModuleToUnit i) W) ≫
      (H.actualCartierResidueHomCokernelIso W hW).hom =
    (SchemeModuleInternalHom.rankOneTensorHomIso
      (IdealSheafDataModule.closedImmersionModule i) W H.inverseCartierTwist_locallyRankOne).inv ≫
      (H.actualCartierResidueSequence W).g := by
  exact CokernelCofork.π_mapOfIsColimit (cokernelIsCokernel _)
    (CokernelCofork.ofπ (H.actualCartierResidueSequence W).g
      (H.actualCartierResidueSequence W).zero)
    (H.actualCartierResidueHomArrowIso W hW).symm.hom

/-- The intrinsic-normal residue tensor is the cokernel of the SAME
original Hom inclusion. This constructs no global Serre/dualizing property. -/
def RegularPrincipalImmersion.actualCartierHomCokernelIntrinsicNormalIso
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W) :
    cokernel (SchemeModuleInternalHom.precompose
      (IdealSheafDataModule.closedImmersionModuleToUnit i) W) ≅
      (Scheme.Modules.pushforward i).obj
        (schemeModuleTensor ((Scheme.Modules.pullback i).obj W)
          (SchemeModuleInternalHom.dual (actualClosedImmersionConormalModule i))) :=
  H.actualCartierResidueHomCokernelIso W hW ≪≫
    H.actualCartierResidueIntrinsicNormalTensorIso W hW

end PfaffianDescent
end
