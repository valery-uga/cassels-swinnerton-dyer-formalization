import PfaffianDescent.ActualOriginalGlobalCanonicalQuadraticPhiNativeCoefficient
import PfaffianDescent.ActualOriginalGlobalCanonicalQuadraticPhiLinear

/- SOURCE ONLY / UNVERIFIED. WHOLE genuine ambient H0 map equality
with the literal native quadratic differential, rather than chosen section
agreement or a definitional H0 surrogate. All comparison laws derive from
the actual original ideal and globally defined Phi. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def actualOriginalGlobalPhiNativeWholeLeftPointProposition118
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) : Prop :=
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let E2 := (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (hypersurfaceToBase p hp))
          (positiveSheafOfModules (grading I) 2)))
    letI : Module K E2 := Module.compHom E2 (algebraMap K L)
    letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
    letI : Module K ((moduleSpecΓFunctor
        (R := .of ((hypersurface p hp).residueField P.1))).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (toBase (equationIdeal p hp)))
          (positiveSheafOfModules (grading (equationIdeal p hp)) 2)))) :=
      Module.compHom _ (algebraMap K ((hypersurface p hp).residueField P.1))
    letI : IsScalarTower K ((hypersurface p hp).residueField P.1)
      ((moduleSpecΓFunctor
        (R := .of ((hypersurface p hp).residueField P.1))).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (toBase (equationIdeal p hp)))
          (positiveSheafOfModules (grading (equationIdeal p hp)) 2)))) :=
      IsScalarTower.of_compHom K ((hypersurface p hp).residueField P.1) _
    (((actualOriginalPositiveTwoContractedNativeDifferentialMap p hp P hP).restrictScalars K).comp
      (actualOriginalGlobalCanonicalQuadraticPhiLinearMap p hp P)) s =
    actualOriginalPositiveTwoContractedNativeDifferentialMap p hp P hP
      (actualOriginalGlobalCanonicalQuadraticPhi p hp P s)

meta section
open Lean Meta Elab Term

private def phiNativeWholeNoRecovery118 (value : Expr) : TermElabM Expr := do
  Term.synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  if value.hasMVar || value.hasLevelMVar || value.hasLooseBVars || value.hasSorry then
    throwError "Native118 unresolved or recovery value/type."
  return value

/-- Apply only the installed composition evaluation law on the exact21
arguments already stored in the original whole-map application. -/
elab "phi_native_whole_left_comp118% " supplied:term : term => do
  let proposition ← phiNativeWholeNoRecovery118
    (← Term.elabTerm supplied none (catchExPostpone := false))
  unless proposition.getAppFn.isConstOf
      ``actualOriginalGlobalPhiNativeWholeLeftPointProposition118 &&
      proposition.getAppArgs.size == 8 do
    throwError "Native118 requires only the original whole-left factory/eight-vector."
  let propositionType ← phiNativeWholeNoRecovery118 (← inferType proposition)
  unless propositionType.consumeMData.equal (mkSort Level.zero) do
    throwError "Native118 original factory did not return Prop."
  let literal ← phiNativeWholeNoRecovery118 (← whnf proposition)
  let some (_, left, _) := literal.consumeMData.headBeta.eq?
    | throwError "Native118 original left factory did not reduce to Eq3."
  let endpoint := left.consumeMData.headBeta
  let endpointArgs := endpoint.getAppArgs
  unless endpoint.getAppFn.isConstOf ``DFunLike.coe && endpointArgs.size == 6 do
    throwError "Native118 expected original whole-map evaluation coe6."
  let composite := endpointArgs[4]!.consumeMData.headBeta
  let compositeArgs := composite.getAppArgs
  let .const compositeName compositeLevels := composite.getAppFn
    | throwError "Native118 actual composite head is not a constant."
  unless compositeName == ``LinearMap.comp && compositeArgs.size == 21 do
    throwError "Native118 actual whole-map composition is not LinearMap.comp21."
  let compInfo ← getConstInfo ``LinearMap.comp
  let lawInfo ← getConstInfo ``LinearMap.comp_apply
  unless compInfo.levelParams.length == compositeLevels.length &&
      lawInfo.levelParams.length == compositeLevels.length do
    throwError "Native118 comp/comp_apply actual universe counts differ."
  let mut compType := compInfo.instantiateTypeLevelParams compositeLevels
  let mut lawType := lawInfo.instantiateTypeLevelParams compositeLevels
  for i in [:21] do
    let .forallE _ compDomain compBody compBinder := compType
      | throwError "Native118 original comp prefix ended at {i}."
    let .forallE _ lawDomain lawBody lawBinder := lawType
      | throwError "Native118 ordinary comp_apply prefix ended at {i}."
    unless compBinder == lawBinder && compDomain.consumeMData.equal lawDomain.consumeMData do
      throwError "Native118 comp/comp_apply stored binder differs at {i}."
    compType := compBody.instantiate1 compositeArgs[i]!
    lawType := lawBody.instantiate1 compositeArgs[i]!
  let .forallE _ pointDomain _ _ := lawType
    | throwError "Native118 ordinary comp_apply lacks original point binder."
  let pointType ← phiNativeWholeNoRecovery118 (← inferType endpointArgs[5]!)
  unless pointDomain.consumeMData.equal endpointArgs[1]!.consumeMData &&
      pointDomain.consumeMData.equal pointType.consumeMData do
    logInfo m!"Native118 exact point joins: law/coercion={pointDomain.consumeMData.equal endpointArgs[1]!.consumeMData}, law/point={pointDomain.consumeMData.equal pointType.consumeMData}."
    logInfo m!"Native118 original law point type: {pointDomain}; original coercion domain: {endpointArgs[1]!}; original point type: {pointType}."
    throwError "Native118 refuses different original composition point carrier."
  let proof ← phiNativeWholeNoRecovery118
    (mkAppN (mkConst ``LinearMap.comp_apply compositeLevels)
      (compositeArgs.push endpointArgs[5]!))
  let proofType ← phiNativeWholeNoRecovery118 (← whnf (← inferType proof))
  let some (_, actualLeft, _) := proofType.consumeMData.headBeta.eq?
    | throwError "Native118 installed exact-vector comp_apply did not return Eq3."
  unless actualLeft.consumeMData.equal left.consumeMData do
    logInfo m!"Native118 stored law LHS: {actualLeft}; original factory LHS: {left}."
    throwError "Native118 installed composition law changed original left endpoint."
  logInfo m!"Native118 comp_apply22 emitted on exact original composition21/point; all21 binder domains and binderInfo raw match, law/coercion/point raw join, actual full LHS raw unchanged. No restriction/Phi/coefficient conversion."
  return proof

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholeLeftCompApplyOwn118    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_whole_left_comp118%
      (actualOriginalGlobalPhiNativeWholeLeftPointProposition118 p hp P hP s)) :=
  phi_native_whole_left_comp118%
      (actualOriginalGlobalPhiNativeWholeLeftPointProposition118 p hp P hP s)

meta section
open Lean Meta Elab Term

/-- Read ONLY the actual RHS of the independently passed original composition
application; apply the installed restriction law on that exact stored vector. -/
elab "phi_native_whole_left_restrict119% " supplied:term : term => do
  let source ← phiNativeWholeNoRecovery118
    (← Term.elabTerm supplied none (catchExPostpone := false))
  unless source.getAppFn.isConstOf
      ``actualOriginalGlobalPhiNativeWholeLeftCompApplyOwn118 &&
      source.getAppArgs.size == 8 do
    throwError "Native119 requires only checked original own composition118/eight-vector."
  let sourceType ← phiNativeWholeNoRecovery118 (← whnf (← inferType source))
  let some (_, _, right) := sourceType.consumeMData.headBeta.eq?
    | throwError "Native119 original comp_apply118 did not expose Eq3."
  let endpoint := right.consumeMData.headBeta
  let endpointArgs := endpoint.getAppArgs
  unless endpoint.getAppFn.isConstOf ``DFunLike.coe && endpointArgs.size == 6 do
    throwError "Native119 expected original restriction evaluation coe6."
  let restriction := endpointArgs[4]!.consumeMData.headBeta
  let restrictionArgs := restriction.getAppArgs
  let .const restrictionName restrictionLevels := restriction.getAppFn
    | throwError "Native119 original restriction is not a constant application."
  unless restrictionName == ``LinearMap.restrictScalars do
    throwError "Native119 refuses another original map head {restrictionName}."
  let restrictInfo ← getConstInfo ``LinearMap.restrictScalars
  let lawInfo ← getConstInfo ``LinearMap.restrictScalars_apply
  unless restrictInfo.levelParams.length == restrictionLevels.length &&
      lawInfo.levelParams.length == restrictionLevels.length do
    throwError "Native119 restrictScalars/law actual universe counts differ."
  let mut restrictType := restrictInfo.instantiateTypeLevelParams restrictionLevels
  let mut lawType := lawInfo.instantiateTypeLevelParams restrictionLevels
  for i in [:restrictionArgs.size] do
    let .forallE _ restrictDomain restrictBody restrictBinder := restrictType
      | throwError "Native119 restriction prefix ended at {i}."
    let .forallE _ lawDomain lawBody lawBinder := lawType
      | throwError "Native119 restriction law prefix ended at {i}."
    unless restrictBinder == lawBinder &&
        restrictDomain.consumeMData.equal lawDomain.consumeMData do
      throwError "Native119 original restriction/law stored binder differs at {i}."
    restrictType := restrictBody.instantiate1 restrictionArgs[i]!
    lawType := lawBody.instantiate1 restrictionArgs[i]!
  unless restrictType.consumeMData.headBeta.getAppFn.isConstOf ``LinearMap &&
      restrictType.consumeMData.headBeta.getAppArgs.size == 11 do
    throwError "Native119 original restriction vector is not exactly saturated LinearMap11."
  let .forallE _ pointDomain _ _ := lawType
    | throwError "Native119 restriction law lacks its final original point binder."
  let pointType ← phiNativeWholeNoRecovery118 (← inferType endpointArgs[5]!)
  unless pointDomain.consumeMData.equal endpointArgs[1]!.consumeMData &&
      pointDomain.consumeMData.equal pointType.consumeMData do
    logInfo m!"Native119 restriction point raw joins: law/coercion={pointDomain.consumeMData.equal endpointArgs[1]!.consumeMData}, law/actual point type={pointDomain.consumeMData.equal pointType.consumeMData}."
    logInfo m!"Native119 exact law point domain: {pointDomain}; original RHS coercion domain: {endpointArgs[1]!}; actual original PhiLinear point type: {pointType}."
    throwError "Native119 refuses different original restriction point carriers."
  let proof ← phiNativeWholeNoRecovery118
    (mkAppN (mkConst ``LinearMap.restrictScalars_apply restrictionLevels)
      (restrictionArgs.push endpointArgs[5]!))
  let proofType ← phiNativeWholeNoRecovery118 (← whnf (← inferType proof))
  let some (_, actualLeft, _) := proofType.consumeMData.headBeta.eq?
    | throwError "Native119 exact restriction law did not return Eq3."
  unless actualLeft.consumeMData.equal right.consumeMData do
    logInfo m!"Native119 actual restriction-law LHS: {actualLeft}; checked comp118 RHS: {right}."
    throwError "Native119 restriction law changed original composition118 RHS."
  logInfo m!"Native119 restrictScalars_apply emitted on all{restrictionArgs.size} exact stored restriction arguments/original PhiLinear point; every binder/type/point and complete118 RHS raw join. No Phi/coefficient/header conversion."
  return proof

/-- Infer a supplied ordinary law on its own exact type; reject all recovery
and unresolved values in both proof and inferred proposition. -/
elab "phi_native_whole_own119% " supplied:term : term => do
  let proof ← phiNativeWholeNoRecovery118
    (← Term.elabTerm supplied none (catchExPostpone := false))
  let _ ← phiNativeWholeNoRecovery118 (← inferType proof)
  return proof

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholeLeftRestrictApplyOwn119
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_whole_left_restrict119%
      (actualOriginalGlobalPhiNativeWholeLeftCompApplyOwn118 p hp P hP s)) :=
  phi_native_whole_left_restrict119%
      (actualOriginalGlobalPhiNativeWholeLeftCompApplyOwn118 p hp P hP s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_whole_own119% (
      letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
      congrArg (actualOriginalPositiveTwoContractedNativeDifferentialMap p hp P hP)
        (actualOriginalGlobalCanonicalQuadraticPhiLinearMap_apply p hp P s))) :=
  phi_native_whole_own119% (
      letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
      congrArg (actualOriginalPositiveTwoContractedNativeDifferentialMap p hp P hP)
        (actualOriginalGlobalCanonicalQuadraticPhiLinearMap_apply p hp P s))

meta section
open Lean Meta Elab Term

private def phiNativeWholeCarrierPair121 (restriction phi : Expr) :
    TermElabM (Expr × Expr) := do
  let restriction ← phiNativeWholeNoRecovery118 restriction
  let phi ← phiNativeWholeNoRecovery118 phi
  unless restriction.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholeLeftRestrictApplyOwn119 &&
      phi.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 &&
      restriction.getAppArgs.size == 8 && phi.getAppArgs.size == 8 do
    throwError "Native121 requires only actual restriction/Phi119 own eight-vectors."
  for i in [:8] do
    unless restriction.getAppArgs[i]!.consumeMData.equal phi.getAppArgs[i]!.consumeMData do
      throwError "Native121 original restriction/Phi parameter vectors differ at {i}."
  let restrictionType ← phiNativeWholeNoRecovery118 (← whnf (← inferType restriction))
  let phiType ← phiNativeWholeNoRecovery118 (← whnf (← inferType phi))
  let some (left, _, _) := restrictionType.consumeMData.headBeta.eq?
    | throwError "Native121 restriction119 has no stored Eq carrier."
  let some (right, _, _) := phiType.consumeMData.headBeta.eq?
    | throwError "Native121 Phi119 has no stored Eq carrier."
  return (left, right)

private def phiNativeWholeProofPair121 (left right : Expr) : TermElabM (Expr × Expr) := do
  let mut left := left.consumeMData
  let mut right := right.consumeMData
  let names := #[``TensorProduct, ``CommRing.toCommSemiring,
    ``HomogeneousLocalization.homogeneousLocalizationCommRing, ``Submodule,
    ``Submodule.Quotient.addCommMonoid, ``HomogeneousIdeal.toIdeal]
  let arities := #[8, 2, 11, 5, 6, 11]
  let indices := #[1, 1, 2, 3, 5, 5]
  for i in [:6] do
    unless left.getAppFn.isConstOf names[i]! && right.getAppFn.isConstOf names[i]! &&
        left.getAppArgs.size == arities[i]! && right.getAppArgs.size == arities[i]! do
      throwError "Native121 diagnosed original carrier path changed at layer{i}."
    left := left.getAppArgs[indices[i]!]!.consumeMData
    right := right.getAppArgs[indices[i]!]!.consumeMData
  let .const leftName _ := left.getAppFn
    | throwError "Native121 original left class proof is not a constant."
  let .const rightName _ := right.getAppFn
    | throwError "Native121 original right class proof is not a constant."
  unless leftName.getPrefix == ``actualOriginalGlobalPhiNativeWholeLeftPointProposition118 &&
      leftName == (``actualOriginalGlobalPhiNativeWholeLeftPointProposition118).str "_proof_1" && left.getAppArgs.size == 2 &&
      rightName.getPrefix == ``CoordinateRing && rightName == (``CoordinateRing).str "_proof_1" &&
      right.getAppArgs.size == 3 do
    throwError "Native121 refuses different diagnosed original class proof constants."
  let leftType ← phiNativeWholeNoRecovery118 (← inferType left)
  let rightType ← phiNativeWholeNoRecovery118 (← inferType right)
  unless (← isProp leftType) && (← isProp rightType) do
    throwError "Native121 diagnosed class endpoints are not both genuine proofs."
  logInfo m!"Native121 exact installed original class proof types: left={leftType}; right={rightType}. Both inferred proposition tests passed; no Type-valued action dictionary is replaced."
  return (left, right)

elab "phi_native_whole_carrier121% " mode:num restriction:term " and " phi:term : term => do
  unless mode.getNat < 2 do
    throwError "Native121 requires exact left0/right1 carrier mode."
  let (left, right) ← phiNativeWholeCarrierPair121
    (← Term.elabTerm restriction none (catchExPostpone := false))
    (← Term.elabTerm phi none (catchExPostpone := false))
  let _ ← phiNativeWholeProofPair121 left right
  if mode.getNat == 0 then return left
  return right

elab "phi_native_whole_proof_irrel121% " restriction:term " and " phi:term : term => do
  let (leftCarrier, rightCarrier) ← phiNativeWholeCarrierPair121
    (← Term.elabTerm restriction none (catchExPostpone := false))
    (← Term.elabTerm phi none (catchExPostpone := false))
  let (left, right) ← phiNativeWholeProofPair121 leftCarrier rightCarrier
  let leftType ← phiNativeWholeNoRecovery118 (← inferType left)
  let rightType ← phiNativeWholeNoRecovery118 (← inferType right)
  let proof ← phiNativeWholeNoRecovery118
    (mkAppN (mkConst ``proof_irrel_heq) #[leftType, rightType, left, right])
  let proofType ← phiNativeWholeNoRecovery118 (← whnf (← inferType proof))
  let some (actualLeftType, actualLeft, actualRightType, actualRight) :=
      proofType.consumeMData.headBeta.heq?
    | throwError "Native121 ordinary proof irrelevance did not produce HEq4."
  unless actualLeftType.consumeMData.equal leftType.consumeMData &&
      actualRightType.consumeMData.equal rightType.consumeMData &&
      actualLeft.consumeMData.equal left.consumeMData &&
      actualRight.consumeMData.equal right.consumeMData do
    throwError "Native121 ordinary proof irrelevance changed original class proof endpoints."
  logInfo m!"Native121 ordinary proof_irrel_heq on exact original four-vector; both source proposition/carrier/action contexts retained."
  return proof

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholeLeftClassProofHEqOwn121
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_whole_proof_irrel121%
      (actualOriginalGlobalPhiNativeWholeLeftRestrictApplyOwn119 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 p hp P hP s)) :=
  phi_native_whole_proof_irrel121%
      (actualOriginalGlobalPhiNativeWholeLeftRestrictApplyOwn119 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 p hp P hP s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholeLeftCarrierEq121
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    (phi_native_whole_carrier121% 0
      (actualOriginalGlobalPhiNativeWholeLeftRestrictApplyOwn119 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 p hp P hP s)) =
    (phi_native_whole_carrier121% 1
      (actualOriginalGlobalPhiNativeWholeLeftRestrictApplyOwn119 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 p hp P hP s)) := by
  basis_full_exact142 (rfl : (phi_native_whole_carrier121% 0
      (actualOriginalGlobalPhiNativeWholeLeftRestrictApplyOwn119 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 p hp P hP s)) = (phi_native_whole_carrier121% 0
      (actualOriginalGlobalPhiNativeWholeLeftRestrictApplyOwn119 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 p hp P hP s)))

universe wNativeWhole122

private theorem phiNativeWholeCarrierCastEquality122 {A B : Sort wNativeWhole122}
    (h : A = B) (x y : B) (p : x = y) : cast h.symm x = cast h.symm y := by
  cases p
  rfl

meta section
open Lean Meta Elab Term

private def phiNativeWholePointPair122 (restriction phi : Expr) :
    TermElabM (Expr × Expr × Expr × Expr) := do
  let restriction ← phiNativeWholeNoRecovery118 restriction
  let phi ← phiNativeWholeNoRecovery118 phi
  let (a, b) ← phiNativeWholeCarrierPair121 restriction phi
  let restrictionType ← phiNativeWholeNoRecovery118 (← whnf (← inferType restriction))
  let phiType ← phiNativeWholeNoRecovery118 (← whnf (← inferType phi))
  let some (actualA, _, leftPoint) := restrictionType.consumeMData.headBeta.eq?
    | throwError "Native122 restriction119 lost original Eq endpoints."
  let some (actualB, rightPoint, _) := phiType.consumeMData.headBeta.eq?
    | throwError "Native122 Phi119 lost original Eq endpoints."
  unless actualA.consumeMData.equal a.consumeMData && actualB.consumeMData.equal b.consumeMData do
    throwError "Native122 actual middle-point carriers changed from checked121 pair."
  return (a, leftPoint, b, rightPoint)

elab "phi_native_whole_middle122% " mode:num restriction:term " and " phi:term : term => do
  unless mode.getNat < 4 do
    throwError "Native122 requires original carrierA0/pointA1/carrierB2/pointB3."
  let (a, x, b, y) ← phiNativeWholePointPair122
    (← Term.elabTerm restriction none (catchExPostpone := false))
    (← Term.elabTerm phi none (catchExPostpone := false))
  if mode.getNat == 0 then return a
  if mode.getNat == 1 then return x
  if mode.getNat == 2 then return b
  return y

elab "phi_native_whole_cast_phi122% " carrierProof:term " and " phi:term : term => do
  let carrierProof ← phiNativeWholeNoRecovery118
    (← Term.elabTerm carrierProof none (catchExPostpone := false))
  let phi ← phiNativeWholeNoRecovery118
    (← Term.elabTerm phi none (catchExPostpone := false))
  unless carrierProof.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholeLeftCarrierEq121 &&
      phi.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 &&
      carrierProof.getAppArgs.size == 8 && phi.getAppArgs.size == 8 do
    throwError "Native122 requires only checked actual carrier121/Phi119 eight-vectors."
  for i in [:8] do
    unless carrierProof.getAppArgs[i]!.consumeMData.equal phi.getAppArgs[i]!.consumeMData do
      throwError "Native122 original carrier/Phi parameters differ at {i}."
  let carrierType ← phiNativeWholeNoRecovery118 (← whnf (← inferType carrierProof))
  let phiType ← phiNativeWholeNoRecovery118 (← whnf (← inferType phi))
  let some (carrierSort, a, b) := carrierType.consumeMData.headBeta.eq?
    | throwError "Native122 carrier121 has no exact stored type equality."
  let some (actualB, x, y) := phiType.consumeMData.headBeta.eq?
    | throwError "Native122 Phi119 has no exact stored point equality."
  let .const phiName phiLevels := phiType.consumeMData.headBeta.getAppFn
    | throwError "Native122 original Phi Eq lacks its constant level vector."
  unless phiName == ``Eq && phiLevels.length == 1 &&
      actualB.consumeMData.equal b.consumeMData &&
      carrierSort.consumeMData.equal (mkSort phiLevels[0]!) do
    throwError "Native122 actual carrier121 does not join exact Phi119 carrier/universe."
  let arguments := #[a, b, carrierProof, x, y, phi]
  let expectedDomains := #[carrierSort, carrierSort, carrierType, b, b, phiType]
  let info ← getConstInfo ``phiNativeWholeCarrierCastEquality122
  unless info.levelParams.length == phiLevels.length do
    throwError "Native122 ordinary cast-equality level count differs."
  let mut lawType := info.instantiateTypeLevelParams phiLevels
  for i in [:6] do
    let .forallE _ domain body _ := lawType
      | throwError "Native122 ordinary cast-equality prefix ended at {i}."
    unless domain.consumeMData.equal expectedDomains[i]!.consumeMData do
      logInfo m!"Native122 cast-equality actual binder{i}: {domain}; stored original expected: {expectedDomains[i]!}."
      throwError "Native122 refuses different ordinary cast-equality binder{i}."
    lawType := body.instantiate1 arguments[i]!
  let proof ← phiNativeWholeNoRecovery118
    (mkAppN (mkConst ``phiNativeWholeCarrierCastEquality122 phiLevels) arguments)
  let proofType ← phiNativeWholeNoRecovery118 (← whnf (← inferType proof))
  let some (actualA, _, _) := proofType.consumeMData.headBeta.eq?
    | throwError "Native122 ordinary transport did not return Eq3."
  unless actualA.consumeMData.equal a.consumeMData &&
      proofType.consumeMData.equal lawType.consumeMData do
    throwError "Native122 ordinary carrier transport changed exact carrier/statement."
  logInfo m!"Native122 ordinary six-vector carrier transport consumes exact121 type equality and119 Phi point equality; all original parameter/target carrier/universe/binder/final statement raw joins true. Internal cast only, no new scalar action/map."
  return proof

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholeLeftPhiCarrierTransportOwn122
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_whole_cast_phi122%
      (actualOriginalGlobalPhiNativeWholeLeftCarrierEq121 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 p hp P hP s)) :=
  phi_native_whole_cast_phi122%
      (actualOriginalGlobalPhiNativeWholeLeftCarrierEq121 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 p hp P hP s)


meta section
open Lean Meta Elab Term

private def phiNativeWholeLocalLawName124 (n : Name) : Bool :=
  match n with
  | .str _ s => s == "actualIdealChartLocalBasisLaw"
  | _ => false

/-- Only the already diagnosed predicate and identity/scheme aliases are
expanded. Native factories, choice and residue wrappers stay opaque. -/
private partial def phiNativeWholeMapView124 (e : Expr) (fuel : Nat) : MetaM Expr := do
  -- LocalDecl.value? can contain assigned expression/universe metavariables.
  -- Resolve them again after every existing bounded let or delta step.
  let e ← instantiateMVars e
  if e.hasMVar || e.hasLevelMVar then
    throwError "BasisStructural105 unresolved normalization input: expression metavariables={e.hasMVar}, level metavariables={e.hasLevelMVar}."
  let e := e.consumeMData.headBeta
  if fuel == 0 then return e
  if let .fvar id := e.getAppFn then
    if let some value := (← id.getDecl).value? then
      return ← phiNativeWholeMapView124 (mkAppN value e.getAppArgs) (fuel - 1)
  if let .letE _ _ val body _ := e then
    return ← phiNativeWholeMapView124 (body.instantiate1 val) (fuel - 1)
  let allowed := match e.getAppFn with
    | .const n _ => phiNativeWholeLocalLawName124 n ||
      n == ``AllCharacteristics.HomogeneousProjective.hypersurface ||
      n == ``PfaffianDescent.closedImmersionIdealTwist ||
      n == ``ModuleCat.Hom.hom || n == ``id
    | _ => false
  if !allowed then return e
  let some e' ← delta? e (fun n => phiNativeWholeLocalLawName124 n ||
    n == ``AllCharacteristics.HomogeneousProjective.hypersurface ||
      n == ``PfaffianDescent.closedImmersionIdealTwist ||
      n == ``ModuleCat.Hom.hom || n == ``id)
    | return e
  phiNativeWholeMapView124 e' (fuel - 1)


/- Follow only the actual747 middle-point path. This uses the frozen head view
(fuel8, identical whitelist); no structural-map alias is unfolded by the view. -/
private def phiNativeWholeOriginalMapPair124 (restriction phi : Expr) :
    TermElabM (Expr × Expr) := do
  let (_, leftPoint, _, rightPoint) ← phiNativeWholePointPair122 restriction phi
  let path : Array Nat := #[5, 0, 6, 2, 5, 5, 1, 3]
  let mut left := leftPoint
  let mut right := rightPoint
  for i in path do
    left ← phiNativeWholeMapView124 left 8
    right ← phiNativeWholeMapView124 right 8
    let la := left.getAppArgs
    let ra := right.getAppArgs
    unless left.getAppFn.equal right.getAppFn && la.size == ra.size do
      logInfo m!"Native124 actual original map path boundary at arg{i}: left={left}; right={right}."
      throwError "Native124 refuses a different actual diagnosed middle-point path."
    unless i < la.size do
      throwError "Native124 actual diagnosed middle-point path exceeds original arity at {i}."
    left := la[i]!
    right := ra[i]!
  left ← phiNativeWholeMapView124 left 8
  right ← phiNativeWholeMapView124 right 8
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless left.getAppFn.isConstOf ``AllCharacteristics.HomogeneousProjective.toBase &&
      right.getAppFn.isConstOf ``AllCharacteristics.HomogeneousProjective.hypersurfaceToBase &&
      la.size == 4 && ra.size == 6 do
    logInfo m!"Native124 actual map endpoints: left={left}; right={right}."
    throwError "Native124 requires exact original toBase4/hypersurfaceToBase6 endpoints."
  for i in [:3] do
    unless la[i]!.consumeMData.equal ra[i]!.consumeMData do
      logInfo m!"Native124 map common parameter{i}: left={la[i]!}; right={ra[i]!}."
      throwError "Native124 refuses different original map ring/variable/class parameters."
  let ideal := la[3]!.consumeMData
  unless ideal.getAppFn.isConstOf ``AllCharacteristics.HomogeneousProjective.equationIdeal &&
      ideal.getAppArgs.size == 6 do
    logInfo m!"Native124 original source ideal vector: {ideal}."
    throwError "Native124 requires the original equationIdeal6 argument."
  for i in [:6] do
    unless ideal.getAppArgs[i]!.consumeMData.equal ra[i]!.consumeMData do
      logInfo m!"Native124 source ideal/hypersurface parameter{i}: left={ideal.getAppArgs[i]!}; right={ra[i]!}."
      throwError "Native124 refuses a different original equationIdeal/hypersurface vector."
  logInfo m!"Native124 exact original map pair: toBase4 and hypersurfaceToBase6; same first3 class parameters and all6 equationIdeal/hypersurface parameters raw join."
  return (left, right)

elab "phi_native_whole_original_map124% " mode:num restriction:term " and " phi:term : term => do
  unless mode.getNat < 4 do
    throwError "Native124 requires leftType0/leftMap1/rightType2/rightMap3."
  let (left, right) ← phiNativeWholeOriginalMapPair124
    (← Term.elabTerm restriction none (catchExPostpone := false))
    (← Term.elabTerm phi none (catchExPostpone := false))
  if mode.getNat == 0 then return ← phiNativeWholeNoRecovery118 (← inferType left)
  if mode.getNat == 1 then return left
  if mode.getNat == 2 then return ← phiNativeWholeNoRecovery118 (← inferType right)
  return right

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholeLeftOriginalMapHEq124
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    @HEq (phi_native_whole_original_map124% 0
      (actualOriginalGlobalPhiNativeWholeLeftRestrictApplyOwn119 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 p hp P hP s))
      (phi_native_whole_original_map124% 1
      (actualOriginalGlobalPhiNativeWholeLeftRestrictApplyOwn119 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 p hp P hP s))
      (phi_native_whole_original_map124% 2
      (actualOriginalGlobalPhiNativeWholeLeftRestrictApplyOwn119 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 p hp P hP s))
      (phi_native_whole_original_map124% 3
      (actualOriginalGlobalPhiNativeWholeLeftRestrictApplyOwn119 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 p hp P hP s)) := by
  rfl

end PfaffianDescent

namespace NativeWholeOriginalMapSeed124Engine

namespace CasselsFullDiamond145
universe u

/- These are two projections of the SAME commutative-ring structure.
The actual caller parents are compared separately by ordinary congruence. -/
private theorem commRing_semiring_eq {R : Type u} (c : CommRing R) :
    @Ring.toSemiring R (@CommRing.toRing R c) =
      @CommSemiring.toSemiring R (@CommRing.toCommSemiring R c) := by
  rfl

end CasselsFullDiamond145

namespace CasselsFullDiamond146
universe u

/- Compare exactly the diagnosed semiring projections of ONE field. Native
field/ring parents at the actual frontier are proved compatible separately. -/
private theorem field_semiring_eq {R : Type u} (c : Field R) :
    @DivisionSemiring.toSemiring R
      (@Semifield.toDivisionSemiring R (@Field.toSemifield R c)) =
      @CommSemiring.toSemiring R
        (@CommRing.toCommSemiring R (@Field.toCommRing R c)) := by
  rfl

/- The newly diagnosed endpoint uses the Ring projection of the SAME field,
rather than its CommSemiring projection. Actual ring parents are certified
separately by the bounded dispatcher; this lemma assumes no parent equality. -/
private theorem field_ring_semiring_eq152 {R : Type u} (c : Field R) :
    @DivisionSemiring.toSemiring R
      (@Semifield.toDivisionSemiring R (@Field.toSemifield R c)) =
      @Ring.toSemiring R (@CommRing.toRing R (@Field.toCommRing R c)) := by
  rfl

end CasselsFullDiamond146

namespace CasselsFullDiamond150
universe u v

/- The two additive-monoid structures are projections of the SAME actual
submodule and additive-group parent. Actual parent data is compared separately. -/
private theorem submodule_addCommMonoid_eq
    (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) :
    @Submodule.addCommMonoid R M
      (@Ring.toSemiring R inferInstance)
      (@AddCommGroup.toAddCommMonoid M inferInstance) inferInstance p =
    @AddCommGroup.toAddCommMonoid _
      (@Submodule.addCommGroup R M inferInstance inferInstance inferInstance p) := by
  rfl

end CasselsFullDiamond150

namespace CasselsFullDiamond153
universe u

/- The two diagnosed additive-monoid-with-one paths come from ONE ring.
The actual caller's ring/semiring parents remain separately certified. -/
private theorem ring_addMonoidWithOne_eq {R : Type u} (c : Ring R) :
    @AddGroupWithOne.toAddMonoidWithOne R (@Ring.toAddGroupWithOne R c) =
      @AddCommMonoidWithOne.toAddMonoidWithOne R
        (@NonAssocSemiring.toAddCommMonoidWithOne R
          (@Semiring.toNonAssocSemiring R (@Ring.toSemiring R c))) := by
  rfl

end CasselsFullDiamond153

namespace CasselsFullDiamond154
universe u

/- These are the two actual Ring parents of ONE Field. Caller carrier and
native CommRing parent compatibility are proved independently below. -/
private theorem field_ring_eq {R : Type u} (c : Field R) :
    @DivisionRing.toRing R (@Field.toDivisionRing R c) =
      @CommRing.toRing R (@Field.toCommRing R c) := by
  rfl

end CasselsFullDiamond154

namespace CasselsFullCoercion142
open CategoryTheory
universe u v

/- The diagnosed ModuleCat wrapper is precisely its declared concrete hom.
This is a genuine ordinary data equality, checked by the enclosing kernel. -/
private theorem module_hom_eq_concrete
    {R : Type u} [Ring R] {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    f.hom = ConcreteCategory.hom (C := ModuleCat.{v} R) f := by
  rfl

end CasselsFullCoercion142

noncomputable section
namespace CasselsFullResidue142
open AlgebraicGeometry
universe u

private theorem native_commRing_eq (S : Scheme.{u}) (x : S) :
    @Field.toCommRing (CommRingCat.carrier (S.residueField x))
      (Scheme.instFieldCarrierResidueField S x) =
    @CommRingCat.instCommRingObjForgetRingHomCarrier (S.residueField x) := by
  rfl

private theorem native_bundle_eq (S : Scheme.{u}) (x : S) :
    @CommRingCat.of (CommRingCat.carrier (S.residueField x))
      (@Field.toCommRing (CommRingCat.carrier (S.residueField x))
        (Scheme.instFieldCarrierResidueField S x)) = S.residueField x := by
  rfl

private theorem native_carrier_eq (S : Scheme.{u}) (x : S) :
    CommRingCat.carrier (S.residueField x) =
      @IsLocalRing.ResidueField (CommRingCat.carrier (S.presheaf.stalk x))
        (@CommRingCat.instCommRingObjForgetRingHomCarrier (S.presheaf.stalk x))
        (inferInstance : IsLocalRing (S.presheaf.stalk x)) := by
  rfl

private theorem native_field_heq (S : Scheme.{u}) (x : S) :
    HEq (Scheme.instFieldCarrierResidueField S x)
      (@IsLocalRing.ResidueField.field (CommRingCat.carrier (S.presheaf.stalk x))
        (@CommRingCat.instCommRingObjForgetRingHomCarrier (S.presheaf.stalk x))
        (inferInstance : IsLocalRing (S.presheaf.stalk x))) := by
  rfl

/-- The native bundled-ring carrier/instance roundtrip. -/
private theorem native_standard_bundle_eq (S : Scheme.{u}) (x : S) :
    @CommRingCat.of (CommRingCat.carrier (S.residueField x))
      (@CommRingCat.instCommRingObjForgetRingHomCarrier (S.residueField x)) =
      S.residueField x := by
  rfl

end CasselsFullResidue142
end

namespace CasselsFullStructural142

universe u v

/-- Congruence for dependent function types with separate domains. -/
private theorem pi_eq
    {A A' : Sort u} (B : A → Sort v) (B' : A' → Sort v)
    (hA : A = A')
    (hB : ∀ a a', HEq a a' → B a = B' a') :
    (∀ a, B a) = (∀ a', B' a') := by
  cases hA
  have h : B = B' := funext fun a => hB a a (HEq.refl a)
  cases h
  rfl

/-- Congruence for functions with separate domains and dependent ranges. -/
private theorem lambda_heq
    {A A' : Sort u} {B : A → Sort v} {B' : A' → Sort v}
    (f : ∀ a, B a) (f' : ∀ a', B' a')
    (hA : A = A')
    (hB : ∀ a a', HEq a a' → B a = B' a')
    (hf : ∀ a a', HEq a a' → HEq (f a) (f' a')) : HEq f f' := by
  cases hA
  have h : B = B' := funext fun a => hB a a (HEq.refl a)
  cases h
  exact heq_of_eq (funext fun a => eq_of_heq (hf a a (HEq.refl a)))

end CasselsFullStructural142

meta section
namespace CasselsFullStructural142
open Lean Meta Elab Tactic

private def isLocalLawName (n : Name) : Bool :=
  match n with
  | .str _ s => s == "actualIdealChartLocalBasisLaw"
  | _ => false

/-- Only the already diagnosed predicate and identity/scheme aliases are
expanded. Native factories, choice and residue wrappers stay opaque. -/
private partial def normalizeHead (e : Expr) (fuel : Nat) : MetaM Expr := do
  -- LocalDecl.value? can contain assigned expression/universe metavariables.
  -- Resolve them again after every existing bounded let or delta step.
  let e ← instantiateMVars e
  if e.hasMVar || e.hasLevelMVar then
    throwError "BasisStructural105 unresolved normalization input: expression metavariables={e.hasMVar}, level metavariables={e.hasLevelMVar}."
  let e := e.consumeMData.headBeta
  if fuel == 0 then return e
  if let .fvar id := e.getAppFn then
    if let some value := (← id.getDecl).value? then
      return ← normalizeHead (mkAppN value e.getAppArgs) (fuel - 1)
  if let .letE _ _ val body _ := e then
    return ← normalizeHead (body.instantiate1 val) (fuel - 1)
  let allowed := match e.getAppFn with
    | .const n _ => isLocalLawName n ||
      n == ``AllCharacteristics.HomogeneousProjective.hypersurface ||
      n == ``PfaffianDescent.closedImmersionIdealTwist ||
      n == ``ModuleCat.Hom.hom || n == ``id
    | _ => false
  if !allowed then return e
  let some e' ← delta? e (fun n => isLocalLawName n ||
    n == ``AllCharacteristics.HomogeneousProjective.hypersurface ||
      n == ``PfaffianDescent.closedImmersionIdealTwist ||
      n == ``ModuleCat.Hom.hom || n == ``id)
    | return e
  normalizeHead e' (fuel - 1)

/-- Turn a projection head into its declared projection function. No value
of the projected structure is unfolded. -/
private def projectionAsApplication (e : Expr) : MetaM Expr := do
  let .proj structName idx major := e.getAppFn | return e
  let some info := getStructureInfo? (← getEnv) structName
    | throwError "BasisStructural093 cannot recover structure metadata for {structName}."
  let some projName := info.getProjFn? idx
    | throwError "BasisStructural093 cannot recover projection {structName}[{idx}]."
  let ty ← instantiateMVars (← whnfD (← inferType major))
  if ty.hasMVar || ty.hasLevelMVar then
    throwError "BasisStructural105 unresolved projection type."
  let .const typeName levels := ty.getAppFn
    | throwError "BasisStructural093 projection source has no structure type."
  unless typeName == structName do
    throwError "BasisStructural093 projection source structure differs: {structName} / {typeName}."
  let .inductInfo ind ← getConstInfo structName
    | throwError "BasisStructural093 projection source is not inductive."
  let params := ty.getAppArgs.extract 0 ind.numParams
  return mkAppN (mkApp (mkAppN (mkConst projName levels) params) major) e.getAppArgs

private def diagnosticBool093 : LBool → String
  | .true => "true"
  | .false => "false"
  | .undef => "undef"

private def diagnosticHead093 (e : Expr) : String :=
  let e := e.consumeMData
  let label := match e.getAppFn with
    | .const n levels => s!"const {n}; levels={reprStr levels}"
    | .fvar id => s!"fvar {id.name}"
    | .bvar i => s!"bvar {i}"
    | .proj n i _ => s!"projection {n}[{i}]"
    | .lam .. => "lambda"
    | .forallE .. => "forall"
    | .letE .. => "let"
    | _ => "other"
  s!"{label}; arguments={e.getAppArgs.size}"

private def diagnosticArguments093 (e : Expr) : String :=
  let args := e.getAppArgs
  if args.isEmpty then "none"
  else if args.size == 1 then s!"arg[0]={diagnosticHead093 args[0]!}"
  else s!"arg[0]={diagnosticHead093 args[0]!}; arg[1]={diagnosticHead093 args[1]!}"

private def diagnosticLocal093 (e : Expr) : MetaM String := do
  let .fvar id := e.getAppFn | return "no local head"
  let decl ← id.getDecl
  let value := match decl.value? with
    | some value => diagnosticHead093 value
    | none => "none"
  return s!"user name={decl.userName}; type head={diagnosticHead093 decl.type}; let value head={value}"

/-- Recognize only the diagnosed native residue-field ring boundary.
The returned certificate is an ordinary S/x equality, and its actual inferred
endpoints must match this boundary. No arbitrary ring instances are identified. -/
private def nativeRingLeaf117? (left right : Expr) : MetaM (Option Expr) := do
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless left.getAppFn.isConstOf ``Field.toCommRing && la.size == 2 &&
      right.getAppFn.isConstOf ``CommRingCat.instCommRingObjForgetRingHomCarrier &&
      ra.size == 1 do return none
  let .const fieldName levels := la[1]!.getAppFn | return none
  let fieldArgs := la[1]!.getAppArgs
  unless fieldName == ``AlgebraicGeometry.Scheme.instFieldCarrierResidueField &&
      fieldArgs.size == 2 && levels.length == 1 do return none
  let proof := mkAppN (mkConst ``CasselsFullResidue142.native_commRing_eq levels) fieldArgs
  let ty ← instantiateMVars (← inferType proof)
  let some (_, oldRing, newRing) := ty.eq?
    | throwError "NativeRing117 ordinary leaf did not infer an equality."
  let oldRing ← normalizeHead oldRing 8
  let newRing ← normalizeHead newRing 8
  unless oldRing.equal left && newRing.equal right do
    logInfo m!"NativeRing117 refused a different residue boundary: raw left match={oldRing.equal left}, raw right match={newRing.equal right}."
    return none
  return some (← mkHEqOfEq proof)

/- The diagnosed native Field remains exact, while carrier/bundle aliases
can occur at BOTH ordinary ring endpoints. The dispatcher separately proves
both complete actual endpoint vectors against the ordinary native theorem. -/
private def nativeRingNestedLeaf149? (left right : Expr) :
    MetaM (Option (Expr × Expr × Expr)) := do
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless left.getAppFn.isConstOf ``Field.toCommRing && la.size == 2 &&
      right.getAppFn.isConstOf ``CommRingCat.instCommRingObjForgetRingHomCarrier &&
      ra.size == 1 do return none
  let actualBundle := ra[0]!
  unless actualBundle.getAppFn.isConstOf ``CommRingCat.of &&
      actualBundle.getAppArgs.size == 2 do return none
  let .const fieldName levels := la[1]!.getAppFn | return none
  let fieldArgs := la[1]!.getAppArgs
  unless fieldName == ``AlgebraicGeometry.Scheme.instFieldCarrierResidueField &&
      fieldArgs.size == 2 && levels.length == 1 do return none
  let proof := mkAppN (mkConst ``CasselsFullResidue142.native_commRing_eq levels) fieldArgs
  let ty ← instantiateMVars (← inferType proof)
  let some (_, ordinaryLeft, ordinaryRight) := ty.eq?
    | throwError "NativeRing149 ordinary native leaf did not infer an equality."
  let ordinaryLeft ← normalizeHead ordinaryLeft 8
  let ordinaryRight ← normalizeHead ordinaryRight 8
  let ola := ordinaryLeft.getAppArgs
  unless ordinaryLeft.getAppFn.equal left.getAppFn && ola.size == la.size &&
      ola[1]!.equal la[1]! && ordinaryRight.getAppFn.equal right.getAppFn &&
      ordinaryRight.getAppArgs.size == ra.size do
    logInfo m!"NativeRing155 refused another native Field/vector: exact left head={ordinaryLeft.getAppFn.equal left.getAppFn}, exact native Field={ola.size == 2 && ola[1]!.equal la[1]!}, exact RHS head={ordinaryRight.getAppFn.equal right.getAppFn}."
    return none
  logInfo m!"NativeRing155 exact native Field with BOTH ordinary endpoints separately certified: raw left={ordinaryLeft.equal left}, left carrier raw={ola[0]!.equal la[0]!}, raw right={ordinaryRight.equal right}, actual left carrier={diagnosticHead093 la[0]!}, ordinary left carrier={diagnosticHead093 ola[0]!}, actual bundle={diagnosticHead093 actualBundle}."
  return some ((← mkHEqOfEq proof), ordinaryLeft, ordinaryRight)

/-- Only the diagnosed bundled native residue-field roundtrip is recognized.
Both actual inferred endpoints of its ordinary S/x equality must match. -/
private def nativeBundleLeaf118? (left right : Expr) : MetaM (Option Expr) := do
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless left.getAppFn.isConstOf ``CommRingCat.of && la.size == 2 &&
      right.getAppFn.isConstOf ``AlgebraicGeometry.Scheme.residueField &&
      ra.size == 2 do return none
  let .const _ levels := right.getAppFn | return none
  unless levels.length == 1 do return none
  let proof := mkAppN (mkConst ``CasselsFullResidue142.native_bundle_eq levels) ra
  let ty ← instantiateMVars (← inferType proof)
  let some (_, oldBundle, newBundle) := ty.eq?
    | throwError "NativeBundle118 ordinary leaf did not infer an equality."
  let oldBundle ← normalizeHead oldBundle 8
  let newBundle ← normalizeHead newBundle 8
  unless oldBundle.equal left && newBundle.equal right do
    logInfo m!"NativeBundle118 refused a different residue boundary: raw left match={oldBundle.equal left}, raw right match={newBundle.equal right}."
    return none
  return some (← mkHEqOfEq proof)

/-- Recognize only the diagnosed native residue-field/stalk carrier alias.
The native endpoint must match exactly. Return the ordinary leaf together with
its explicit stalk endpoint, which is separately certified against the actual
three-argument ResidueField expression below; no data equality is assumed. -/
private def nativeCarrierLeaf120? (left right : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless left.getAppFn.isConstOf ``CommRingCat.carrier && la.size == 1 &&
      right.getAppFn.isConstOf ``IsLocalRing.ResidueField && ra.size == 3 do
    return none
  let .const nativeName levels := la[0]!.getAppFn | return none
  let nativeArgs := la[0]!.getAppArgs
  unless nativeName == ``AlgebraicGeometry.Scheme.residueField &&
      nativeArgs.size == 2 && levels.length == 1 do return none
  let proof := mkAppN (mkConst ``CasselsFullResidue142.native_carrier_eq levels) nativeArgs
  let ty ← instantiateMVars (← inferType proof)
  let some (_, nativeCarrier, stalkCarrier) := ty.eq?
    | throwError "NativeCarrier119 ordinary leaf did not infer an equality."
  let nativeCarrier ← normalizeHead nativeCarrier 8
  let stalkCarrier ← normalizeHead stalkCarrier 8
  unless nativeCarrier.equal left && stalkCarrier.getAppFn.equal right.getAppFn &&
      stalkCarrier.getAppArgs.size == ra.size do
    logInfo m!"NativeCarrier120 refused a different native endpoint or explicit stalk head: raw left match={nativeCarrier.equal left}, raw stalk head match={stalkCarrier.getAppFn.equal right.getAppFn}."
    return none
  if !stalkCarrier.equal right then
    let ordinaryArgs := stalkCarrier.getAppArgs
    for i in [:ra.size] do
      let ordinaryProof ← isProofQuick ordinaryArgs[i]!
      let actualProof ← isProofQuick ra[i]!
      logInfo m!"NativeCarrier120 explicit RHS argument[{i}]: raw match={ordinaryArgs[i]!.equal ra[i]!}; ordinary head={diagnosticHead093 ordinaryArgs[i]!}; actual head={diagnosticHead093 ra[i]!}; proofQuick ordinary={diagnosticBool093 ordinaryProof}, actual={diagnosticBool093 actualProof}."
  return some ((← mkHEqOfEq proof), stalkCarrier)

/-- Only the diagnosed native field structure and explicit stalk residue-field
structure are compared. The exact native endpoint must match; its explicit RHS
is separately certified against the actual RHS using bounded congruence. -/
private def nativeFieldLeaf121? (left right : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless left.getAppFn.isConstOf ``AlgebraicGeometry.Scheme.instFieldCarrierResidueField &&
      la.size == 2 && right.getAppFn.isConstOf ``IsLocalRing.ResidueField.field &&
      ra.size == 3 do return none
  let .const _ levels := left.getAppFn | return none
  unless levels.length == 1 do return none
  let proof := mkAppN (mkConst ``CasselsFullResidue142.native_field_heq levels) la
  let ty ← instantiateMVars (← inferType proof)
  unless ty.getAppFn.isConstOf ``HEq && ty.getAppArgs.size == 4 do
    throwError "NativeField121 ordinary leaf did not infer an HEq."
  let nativeField ← normalizeHead ty.getAppArgs[1]! 8
  let stalkField ← normalizeHead ty.getAppArgs[3]! 8
  unless nativeField.equal left && stalkField.getAppFn.equal right.getAppFn &&
      stalkField.getAppArgs.size == ra.size do
    logInfo m!"NativeField121 refused a different native endpoint or explicit stalk-field head: raw left match={nativeField.equal left}, raw stalk head match={stalkField.getAppFn.equal right.getAppFn}."
    return none
  if !stalkField.equal right then
    let ordinaryArgs := stalkField.getAppArgs
    for i in [:ra.size] do
      let ordinaryProof ← isProofQuick ordinaryArgs[i]!
      let actualProof ← isProofQuick ra[i]!
      logInfo m!"NativeField121 explicit RHS argument[{i}]: raw match={ordinaryArgs[i]!.equal ra[i]!}; ordinary head={diagnosticHead093 ordinaryArgs[i]!}; actual head={diagnosticHead093 ra[i]!}; proofQuick ordinary={diagnosticBool093 ordinaryProof}, actual={diagnosticBool093 actualProof}."
  return some (proof, stalkField)

/-- Recognize only the native bundled-ring roundtrip with its exact native
right endpoint. The actual two-argument bundle is separately certified against
the ordinary equality's left endpoint below; no ring/carrier data is assumed. -/
private def nativeStandardBundleLeaf124? (left right : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless left.getAppFn.isConstOf ``CommRingCat.of && la.size == 2 &&
      right.getAppFn.isConstOf ``AlgebraicGeometry.Scheme.residueField &&
      ra.size == 2 do return none
  let .const _ levels := right.getAppFn | return none
  unless levels.length == 1 do return none
  let proof := mkAppN (mkConst ``CasselsFullResidue142.native_standard_bundle_eq levels) ra
  let ty ← instantiateMVars (← inferType proof)
  let some (_, oldBundle, newBundle) := ty.eq?
    | throwError "NativeStandardBundle123 ordinary leaf did not infer an equality."
  let oldBundle ← normalizeHead oldBundle 8
  let newBundle ← normalizeHead newBundle 8
  unless newBundle.equal right && oldBundle.getAppFn.equal left.getAppFn &&
      oldBundle.getAppArgs.size == la.size do
    logInfo m!"NativeStandardBundle124 refused a different native endpoint or bundle head: raw right match={newBundle.equal right}, raw bundle head match={oldBundle.getAppFn.equal left.getAppFn}."
    return none
  if !oldBundle.equal left then
    let ordinaryArgs := oldBundle.getAppArgs
    for i in [:la.size] do
      let ordinaryProof ← isProofQuick ordinaryArgs[i]!
      let actualProof ← isProofQuick la[i]!
      logInfo m!"NativeStandardBundle124 explicit LHS argument[{i}]: raw match={ordinaryArgs[i]!.equal la[i]!}; ordinary head={diagnosticHead093 ordinaryArgs[i]!}; actual head={diagnosticHead093 la[i]!}; proofQuick ordinary={diagnosticBool093 ordinaryProof}, actual={diagnosticBool093 actualProof}."
      logInfo m!"NativeStandardBundle124 argument[{i}] first arguments: ordinary={diagnosticArguments093 ordinaryArgs[i]!}; actual={diagnosticArguments093 la[i]!}."
  return some ((← mkHEqOfEq proof), oldBundle)

/- Inspect declared projection metadata before converting a projection spine;
this avoids inferring unrelated geometric projection types at every node. -/
private def declaredHead145 (e : Expr) (name : Name) : MetaM Bool := do
  match e.consumeMData.getAppFn with
  | .const actual _ => return actual == name
  | .proj structName index _ =>
    let some info := getStructureInfo? (← getEnv) structName | return false
    return info.getProjFn? index == some name
  | _ => return false

private def commRingSemiringLeaf145? (left right : Expr) :
    MetaM (Option (Expr × Expr × Expr)) := do
  unless (← declaredHead145 left ``Ring.toSemiring) &&
      (← declaredHead145 right ``CommSemiring.toSemiring) do return none
  let left ← projectionAsApplication left
  let right ← projectionAsApplication right
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless la.size == 2 && ra.size == 2 do return none
  unless (← declaredHead145 la[1]! ``CommRing.toRing) &&
      (← declaredHead145 ra[1]! ``CommRing.toCommSemiring) do return none
  let leftParent ← projectionAsApplication la[1]!
  let rightParent ← projectionAsApplication ra[1]!
  let lpa := leftParent.getAppArgs
  let rpa := rightParent.getAppArgs
  unless lpa.size == 2 && rpa.size == 2 do return none
  let .const _ levels := leftParent.getAppFn | return none
  unless levels.length == 1 do return none
  let proof := mkAppN (mkConst ``CasselsFullDiamond145.commRing_semiring_eq levels) lpa
  let ty ← instantiateMVars (← inferType proof)
  let some (_, ordinaryLeft, ordinaryRight) := ty.eq?
    | throwError "Semiring145 ordinary diamond leaf did not infer an equality."
  let ordinaryLeft ← normalizeHead ordinaryLeft 8
  let ordinaryRight ← normalizeHead ordinaryRight 8
  let ordinaryLeft ← projectionAsApplication ordinaryLeft
  let ordinaryRight ← projectionAsApplication ordinaryRight
  unless ordinaryLeft.getAppFn.equal left.getAppFn &&
      ordinaryRight.getAppFn.equal right.getAppFn &&
      ordinaryLeft.getAppArgs.size == la.size &&
      ordinaryRight.getAppArgs.size == ra.size do
    throwError "Semiring145 ordinary diamond does not have the diagnosed projection heads."
  logInfo m!"Semiring145 exact projection diamond: left carrier/parent raw match={la[0]!.equal lpa[0]!}, actual parent carriers raw match={lpa[0]!.equal rpa[0]!}, actual CommRing parents raw match={lpa[1]!.equal rpa[1]!}."
  return some ((← mkHEqOfEq proof), ordinaryLeft, ordinaryRight)

private def fieldSemiringLeaf146? (left right : Expr) :
    MetaM (Option (Expr × Expr × Expr)) := do
  let rightIsRing ← declaredHead145 right ``Ring.toSemiring
  unless (← declaredHead145 left ``DivisionSemiring.toSemiring) &&
      (rightIsRing || (← declaredHead145 right ``CommSemiring.toSemiring)) do
    return none
  let left ← projectionAsApplication left
  let right ← projectionAsApplication right
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless la.size == 2 && ra.size == 2 do return none
  let rightParentName := if rightIsRing then ``CommRing.toRing
    else ``CommRing.toCommSemiring
  unless (← declaredHead145 la[1]! ``Semifield.toDivisionSemiring) &&
      (← declaredHead145 ra[1]! rightParentName) do return none
  let divisionParent ← projectionAsApplication la[1]!
  let ringParent ← projectionAsApplication ra[1]!
  let dpa := divisionParent.getAppArgs
  let rpa := ringParent.getAppArgs
  unless dpa.size == 2 && rpa.size == 2 do return none
  unless (← declaredHead145 dpa[1]! ``Field.toSemifield) do
    logInfo m!"FieldSemiring146 refused another semifield parent: {diagnosticHead093 dpa[1]!}."
    return none
  let fieldParent ← projectionAsApplication dpa[1]!
  let fpa := fieldParent.getAppArgs
  unless fpa.size == 2 do return none
  let .const _ levels := fieldParent.getAppFn | return none
  unless levels.length == 1 do return none
  let diamondName := if rightIsRing then
      ``CasselsFullDiamond146.field_ring_semiring_eq152
    else ``CasselsFullDiamond146.field_semiring_eq
  let proof := mkAppN (mkConst diamondName levels) fpa
  let ty ← instantiateMVars (← inferType proof)
  let some (_, ordinaryLeft, ordinaryRight) := ty.eq?
    | throwError "FieldSemiring146 ordinary field diamond did not infer an equality."
  let ordinaryLeft ← normalizeHead ordinaryLeft 8
  let ordinaryRight ← normalizeHead ordinaryRight 8
  let ordinaryLeft ← projectionAsApplication ordinaryLeft
  let ordinaryRight ← projectionAsApplication ordinaryRight
  unless ordinaryLeft.getAppFn.equal left.getAppFn &&
      ordinaryRight.getAppFn.equal right.getAppFn &&
      ordinaryLeft.getAppArgs.size == la.size &&
      ordinaryRight.getAppArgs.size == ra.size do
    throwError "FieldSemiring146 ordinary diamond does not have the diagnosed projection heads."
  logInfo m!"FieldSemiring146 exact field projection diamond: left carrier/field raw match={la[0]!.equal fpa[0]!}, actual parent carriers raw match={fpa[0]!.equal rpa[0]!}, actual ring parent={diagnosticHead093 rpa[1]!}."
  return some ((← mkHEqOfEq proof), ordinaryLeft, ordinaryRight)

private def submoduleAdditiveLeaf150? (left right : Expr) :
    MetaM (Option (Expr × Expr × Expr)) := do
  unless left.getAppFn.isConstOf ``Submodule.addCommMonoid &&
      left.getAppArgs.size == 6 &&
      (← declaredHead145 right ``AddCommGroup.toAddCommMonoid) do return none
  let right ← projectionAsApplication right
  let ra := right.getAppArgs
  unless ra.size == 2 && ra[1]!.getAppFn.isConstOf ``Submodule.addCommGroup &&
      ra[1]!.getAppArgs.size == 6 do return none
  let groupParent := ra[1]!
  let ga := groupParent.getAppArgs
  let .const _ levels := groupParent.getAppFn | return none
  unless levels.length == 2 do return none
  let proof := mkAppN (mkConst ``CasselsFullDiamond150.submodule_addCommMonoid_eq levels) ga
  let ty ← instantiateMVars (← inferType proof)
  let some (_, ordinaryLeft, ordinaryRight) := ty.eq?
    | throwError "Submodule150 ordinary additive diamond did not infer an equality."
  let ordinaryLeft ← normalizeHead ordinaryLeft 8
  let ordinaryRight ← normalizeHead ordinaryRight 8
  let ordinaryRight ← projectionAsApplication ordinaryRight
  unless ordinaryLeft.getAppFn.equal left.getAppFn &&
      ordinaryLeft.getAppArgs.size == left.getAppArgs.size &&
      ordinaryRight.getAppFn.equal right.getAppFn &&
      ordinaryRight.getAppArgs.size == ra.size do
    throwError "Submodule150 ordinary diamond does not have the diagnosed instance heads."
  let la := left.getAppArgs
  logInfo m!"Submodule150 exact additive instance diamond: base carrier raw={la[0]!.equal ga[0]!}, ambient carrier raw={la[1]!.equal ga[1]!}, submodule raw={la[5]!.equal ga[5]!}, ordinary group endpoint raw={ordinaryRight.equal right}."
  return some ((← mkHEqOfEq proof), ordinaryLeft, ordinaryRight)

private def ringAddMonoidWithOneLeaf153? (left right : Expr) :
    MetaM (Option (Expr × Expr × Expr)) := do
  unless (← declaredHead145 left ``AddGroupWithOne.toAddMonoidWithOne) &&
      (← declaredHead145 right ``AddCommMonoidWithOne.toAddMonoidWithOne) do
    return none
  let left ← projectionAsApplication left
  let right ← projectionAsApplication right
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless la.size == 2 && ra.size == 2 do return none
  unless (← declaredHead145 la[1]! ``Ring.toAddGroupWithOne) &&
      (← declaredHead145 ra[1]! ``NonAssocSemiring.toAddCommMonoidWithOne) do
    return none
  let ringParent ← projectionAsApplication la[1]!
  let nonAssocParent ← projectionAsApplication ra[1]!
  let rpa := ringParent.getAppArgs
  let npa := nonAssocParent.getAppArgs
  unless rpa.size == 2 && npa.size == 2 do return none
  let .const _ levels := ringParent.getAppFn | return none
  unless levels.length == 1 do return none
  let proof := mkAppN
    (mkConst ``CasselsFullDiamond153.ring_addMonoidWithOne_eq levels) rpa
  let ty ← instantiateMVars (← inferType proof)
  let some (_, ordinaryLeft, ordinaryRight) := ty.eq?
    | throwError "AddMonoidOne153 ordinary ring diamond did not infer an equality."
  let ordinaryLeft ← normalizeHead ordinaryLeft 8
  let ordinaryRight ← normalizeHead ordinaryRight 8
  let ordinaryLeft ← projectionAsApplication ordinaryLeft
  let ordinaryRight ← projectionAsApplication ordinaryRight
  unless ordinaryLeft.getAppFn.equal left.getAppFn &&
      ordinaryRight.getAppFn.equal right.getAppFn &&
      ordinaryLeft.getAppArgs.size == la.size &&
      ordinaryRight.getAppArgs.size == ra.size do
    throwError "AddMonoidOne153 ordinary leaf does not have the diagnosed projection heads."
  logInfo m!"AddMonoidOne153 exact ring projection diamond: left carrier/ring raw={la[0]!.equal rpa[0]!}, actual parent carriers raw={rpa[0]!.equal npa[0]!}, actual nonassociative semiring parent={diagnosticHead093 npa[1]!}."
  return some ((← mkHEqOfEq proof), ordinaryLeft, ordinaryRight)

private def fieldRingLeaf154? (left right : Expr) :
    MetaM (Option (Expr × Expr × Expr)) := do
  unless (← declaredHead145 left ``DivisionRing.toRing) &&
      (← declaredHead145 right ``CommRing.toRing) do return none
  let left ← projectionAsApplication left
  let right ← projectionAsApplication right
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless la.size == 2 && ra.size == 2 do return none
  unless (← declaredHead145 la[1]! ``Field.toDivisionRing) do return none
  let fieldParent ← projectionAsApplication la[1]!
  let fpa := fieldParent.getAppArgs
  unless fpa.size == 2 do return none
  let .const _ levels := fieldParent.getAppFn | return none
  unless levels.length == 1 do return none
  let proof := mkAppN (mkConst ``CasselsFullDiamond154.field_ring_eq levels) fpa
  let ty ← instantiateMVars (← inferType proof)
  let some (_, ordinaryLeft, ordinaryRight) := ty.eq?
    | throwError "FieldRing154 ordinary field ring diamond did not infer an equality."
  let ordinaryLeft ← normalizeHead ordinaryLeft 8
  let ordinaryRight ← normalizeHead ordinaryRight 8
  let ordinaryLeft ← projectionAsApplication ordinaryLeft
  let ordinaryRight ← projectionAsApplication ordinaryRight
  unless ordinaryLeft.getAppFn.equal left.getAppFn &&
      ordinaryRight.getAppFn.equal right.getAppFn &&
      ordinaryLeft.getAppArgs.size == la.size &&
      ordinaryRight.getAppArgs.size == ra.size do
    throwError "FieldRing154 ordinary leaf does not have the diagnosed ring projection heads."
  logInfo m!"FieldRing154 exact same-field ring diamond: left carrier/field raw={la[0]!.equal fpa[0]!}, actual carrier raw={fpa[0]!.equal ra[0]!}, actual CommRing parent={diagnosticHead093 ra[1]!}."
  return some ((← mkHEqOfEq proof), ordinaryLeft, ordinaryRight)

private structure CertificateState where
  remaining : Nat := 1024
  pairs : Array (Expr × Expr × Expr) := #[]
  congruences : Array (Expr × Nat × CongrTheorem) := #[]
  proofLeaves : Nat := 0
  congrSteps : Nat := 0
  binderSteps : Nat := 0
  fallbackProofLeaves : Nat := 0
  wrapperLeaves : Nat := 0

private abbrev CertificateM := StateT CertificateState MetaM

private def cache (left right certificate : Expr) : CertificateM Expr := do
  modify fun s => { s with pairs := s.pairs.push (left, right, certificate) }
  return certificate

private def congruenceFor (head : Expr) (arity : Nat) : CertificateM CongrTheorem := do
  if let some (_, _, thm) := (← get).congruences.find? fun (f, n, _) =>
      f.equal head && n == arity then
    return thm
  let thm ← mkHCongrWithArity head arity
  modify fun s => { s with congruences := s.congruences.push (head, arity, thm) }
  return thm

private abbrev StructuralRecursor147 :=
  Expr → Expr → Nat → Array (Expr × Expr × Expr) → String → CertificateM Expr

/- Keep this ordinary meta helper separate from the recursive definition.
Both orientations use exactly the same existing certificates, shared state,
depth decrement, cache endpoints and diagnostic path suffixes. -/
private def dispatchDiamond147
    (recognize : Expr → Expr → MetaM (Option (Expr × Expr × Expr)))
    (recurse : StructuralRecursor147) (label : String)
    (left0 right0 left right : Expr) (depth : Nat)
    (locals : Array (Expr × Expr × Expr)) (path : String) :
    CertificateM (Option Expr) := do
  if let some (diamond, ordinaryLeft, ordinaryRight) ← recognize left right then
    modify fun s => { s with wrapperLeaves := s.wrapperLeaves + 1 }
    let actualLeft ← recurse left ordinaryLeft (depth - 1) locals
      (path ++ "." ++ label ++ "Left")
    let actualRight ← recurse ordinaryRight right (depth - 1) locals
      (path ++ "." ++ label ++ "Right")
    let result ← mkHEqTrans (← mkHEqTrans actualLeft diamond) actualRight
    return some (← cache left0 right0 result)
  if let some (diamond, ordinaryLeft, ordinaryRight) ← recognize right left then
    modify fun s => { s with wrapperLeaves := s.wrapperLeaves + 1 }
    let actualLeft ← recurse right ordinaryLeft (depth - 1) locals
      (path ++ "." ++ label ++ "Left")
    let actualRight ← recurse ordinaryRight left (depth - 1) locals
      (path ++ "." ++ label ++ "Right")
    let reverse ← mkHEqTrans (← mkHEqTrans actualLeft diamond) actualRight
    return some (← cache left0 right0 (← mkHEqSymm reverse))
  return none

/-- Each nontrivial step has a proof: a proof_irrel_heq leaf, a generated
abstract congruence lambda, or the ordinary pi/lambda theorem above.
Generated congruence lambdas are part of the final kernel checked term. -/
private partial def structuralHEq (left0 right0 : Expr) (depth : Nat)
    (locals : Array (Expr × Expr × Expr)) (path : String := "root") : CertificateM Expr := do
  let left0 ← instantiateMVars left0
  let right0 ← instantiateMVars right0
  if left0.hasMVar || left0.hasLevelMVar || right0.hasMVar || right0.hasLevelMVar then
    throwError "BasisStructural105 unresolved comparison input at {path}."
  if left0.equal right0 then return ← mkHEqRefl left0
  if let some (_, _, h) := locals.find? fun (l, r, _) =>
      l.equal left0 && r.equal right0 then
    return h
  if let some (_, _, h) := (← get).pairs.find? fun (l, r, _) =>
      l.equal left0 && r.equal right0 then
    return h
  if depth == 0 || (← get).remaining == 0 then
    throwError "BasisStructural093 certificate traversal exhausted its explicit bound."
  modify fun s => { s with remaining := s.remaining - 1 }
  let left ← normalizeHead left0 8
  let right ← normalizeHead right0 8
  if left.equal right then return ← cache left0 right0 (← mkHEqRefl left)
  let lp ← isProofQuick left
  let rp ← isProofQuick right
  if lp == .true && rp == .true then
    let p ← inferType left
    let q ← inferType right
    let h := mkAppN (mkConst ``proof_irrel_heq) #[p, q, left, right]
    modify fun s => { s with proofLeaves := s.proofLeaves + 1 }
    return ← cache left0 right0 h
  -- The quick classifier can be undecided for applied proof constants.
  -- Confirm both exact inferred types are propositions before proof irrelevance.
  if lp != .false && rp != .false then
    let p ← instantiateMVars (← inferType left)
    let q ← instantiateMVars (← inferType right)
    if p.hasMVar || p.hasLevelMVar || q.hasMVar || q.hasLevelMVar then
      throwError "BasisStructural108 unresolved fallback proof type at {path}."
    if (← isProp p) && (← isProp q) then
      let h := mkAppN (mkConst ``proof_irrel_heq) #[p, q, left, right]
      modify fun s => { s with proofLeaves := s.proofLeaves + 1, fallbackProofLeaves := s.fallbackProofLeaves + 1 }
      logInfo m!"BasisStructural108 confirmed Prop fallback at {path}."
      return ← cache left0 right0 h
  if let some h ← dispatchDiamond147 commRingSemiringLeaf145?
      (fun l r d ls p => structuralHEq l r d ls p)
      "semiringDiamond" left0 right0 left right depth locals path then
    return h
  if let some h ← dispatchDiamond147 fieldSemiringLeaf146?
      (fun l r d ls p => structuralHEq l r d ls p)
      "fieldSemiring" left0 right0 left right depth locals path then
    return h
  if let some h ← dispatchDiamond147 fieldRingLeaf154?
      (fun l r d ls p => structuralHEq l r d ls p)
      "fieldRing" left0 right0 left right depth locals path then
    return h
  if let some h ← dispatchDiamond147 ringAddMonoidWithOneLeaf153?
      (fun l r d ls p => structuralHEq l r d ls p)
      "ringAddMonoidOne" left0 right0 left right depth locals path then
    return h
  if let some h ← dispatchDiamond147 submoduleAdditiveLeaf150?
      (fun l r d ls p => structuralHEq l r d ls p)
      "submoduleAdditive" left0 right0 left right depth locals path then
    return h
  if let some h ← nativeRingLeaf117? left right then
    modify fun s => { s with wrapperLeaves := s.wrapperLeaves + 1 }
    return ← cache left0 right0 h
  if let some h ← nativeRingLeaf117? right left then
    modify fun s => { s with wrapperLeaves := s.wrapperLeaves + 1 }
    return ← cache left0 right0 (← mkHEqSymm h)
  if let some h ← dispatchDiamond147 nativeRingNestedLeaf149?
      (fun l r d ls p => structuralHEq l r d ls p)
      "nativeRingNested" left0 right0 left right depth locals path then
    return h
  if let some h ← nativeBundleLeaf118? left right then
    modify fun s => { s with wrapperLeaves := s.wrapperLeaves + 1 }
    return ← cache left0 right0 h
  if let some h ← nativeBundleLeaf118? right left then
    modify fun s => { s with wrapperLeaves := s.wrapperLeaves + 1 }
    return ← cache left0 right0 (← mkHEqSymm h)
  if let some (nativeLeaf, nativeRight) ← nativeCarrierLeaf120? left right then
    modify fun s => { s with wrapperLeaves := s.wrapperLeaves + 1 }
    let actualRhs ← structuralHEq nativeRight right (depth - 1) locals
      (path ++ ".nativeCarrierRhs")
    return ← cache left0 right0 (← mkHEqTrans nativeLeaf actualRhs)
  if let some (nativeLeaf, nativeRight) ← nativeCarrierLeaf120? right left then
    modify fun s => { s with wrapperLeaves := s.wrapperLeaves + 1 }
    let actualRhs ← structuralHEq nativeRight left (depth - 1) locals
      (path ++ ".nativeCarrierRhs")
    let reverse ← mkHEqTrans nativeLeaf actualRhs
    return ← cache left0 right0 (← mkHEqSymm reverse)
  if let some (nativeLeaf, nativeRight) ← nativeFieldLeaf121? left right then
    modify fun s => { s with wrapperLeaves := s.wrapperLeaves + 1 }
    let actualRhs ← structuralHEq nativeRight right (depth - 1) locals
      (path ++ ".nativeFieldRhs")
    return ← cache left0 right0 (← mkHEqTrans nativeLeaf actualRhs)
  if let some (nativeLeaf, nativeRight) ← nativeFieldLeaf121? right left then
    modify fun s => { s with wrapperLeaves := s.wrapperLeaves + 1 }
    let actualRhs ← structuralHEq nativeRight left (depth - 1) locals
      (path ++ ".nativeFieldRhs")
    let reverse ← mkHEqTrans nativeLeaf actualRhs
    return ← cache left0 right0 (← mkHEqSymm reverse)
  if let some (nativeLeaf, nativeLeft) ← nativeStandardBundleLeaf124? left right then
    modify fun s => { s with wrapperLeaves := s.wrapperLeaves + 1 }
    let actualLhs ← structuralHEq left nativeLeft (depth - 1) locals
      (path ++ ".nativeStandardBundleLhs")
    return ← cache left0 right0 (← mkHEqTrans actualLhs nativeLeaf)
  if let some (nativeLeaf, nativeLeft) ← nativeStandardBundleLeaf124? right left then
    modify fun s => { s with wrapperLeaves := s.wrapperLeaves + 1 }
    let actualLhs ← structuralHEq right nativeLeft (depth - 1) locals
      (path ++ ".nativeStandardBundleLhs")
    let reverse ← mkHEqTrans actualLhs nativeLeaf
    return ← cache left0 right0 (← mkHEqSymm reverse)
  match left, right with
  | .forallE n A B bi, .forallE _ A' B' _ =>
    let hA ← mkEqOfHEq (← structuralHEq A A' (depth - 1) locals (path ++ ".binderType"))
    let u ← getLevel A
    let leftFamily ← withLocalDecl n bi A fun a => do
      mkLambdaFVars #[a] (B.instantiate1 a)
    let rightFamily ← withLocalDecl n bi A' fun a' => do
      mkLambdaFVars #[a'] (B'.instantiate1 a')
    let v ← withLocalDecl n bi A fun a => getLevel (B.instantiate1 a)
    let hB ← withLocalDecl n bi A fun a => do
      withLocalDecl (n.appendAfter "'") bi A' fun a' => do
        withLocalDeclD `h (← mkHEq a a') fun h => do
          let bodyEq ← mkEqOfHEq (← structuralHEq
            (B.instantiate1 a) (B'.instantiate1 a') (depth - 1)
            (locals.push (a, a', h)) (path ++ ".body"))
          mkLambdaFVars #[a, a', h] bodyEq
    let eq := mkAppN (mkConst ``pi_eq [u, v])
      #[A, A', leftFamily, rightFamily, hA, hB]
    modify fun s => { s with binderSteps := s.binderSteps + 1 }
    return ← cache left0 right0 (← mkHEqOfEq eq)
  | .lam n A body bi, .lam _ A' body' _ =>
    let hA ← mkEqOfHEq (← structuralHEq A A' (depth - 1) locals (path ++ ".binderType"))
    let u ← getLevel A
    let B ← withLocalDecl n bi A fun a => do
      mkLambdaFVars #[a] (← inferType (body.instantiate1 a))
    let B' ← withLocalDecl n bi A' fun a' => do
      mkLambdaFVars #[a'] (← inferType (body'.instantiate1 a'))
    let v ← withLocalDecl n bi A fun a => do getLevel (← inferType (body.instantiate1 a))
    let (hB, hf) ← withLocalDecl n bi A fun a => do
      withLocalDecl (n.appendAfter "'") bi A' fun a' => do
        withLocalDeclD `h (← mkHEq a a') fun h => do
          let l := body.instantiate1 a
          let r := body'.instantiate1 a'
          let locals := locals.push (a, a', h)
          let typeEq ← mkEqOfHEq (← structuralHEq (← inferType l) (← inferType r)
            (depth - 1) locals (path ++ ".lambdaType"))
          let valueHEq ← structuralHEq l r (depth - 1) locals (path ++ ".lambdaBody")
          return (← mkLambdaFVars #[a, a', h] typeEq,
            ← mkLambdaFVars #[a, a', h] valueHEq)
    let h := mkAppN (mkConst ``lambda_heq [u, v])
      #[A, A', B, B', left, right, hA, hB, hf]
    modify fun s => { s with binderSteps := s.binderSteps + 1 }
    return ← cache left0 right0 h
  | _, _ => pure ()
  let left ← projectionAsApplication left
  let right ← projectionAsApplication right
  let lh := left.getAppFn
  let rh := right.getAppFn
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless lh.equal rh && la.size == ra.size && !la.isEmpty do
    logInfo m!"BasisStructural093 unsupported path: {path}"
    logInfo m!"BasisStructural093 left boundary: {diagnosticHead093 left}"
    logInfo m!"BasisStructural093 right boundary: {diagnosticHead093 right}"
    logInfo m!"BasisStructural093 left first arguments: {diagnosticArguments093 left}"
    logInfo m!"BasisStructural093 right first arguments: {diagnosticArguments093 right}"
    logInfo m!"BasisStructural093 left local: {← diagnosticLocal093 left}"
    logInfo m!"BasisStructural093 right local: {← diagnosticLocal093 right}"
    logInfo m!"BasisStructural093 proofQuick: left={diagnosticBool093 lp}, right={diagnosticBool093 rp}"
    throwError "BasisStructural093 found an unsupported non-proof head boundary at {path}."
  let thm ← congruenceFor lh la.size
  let mut args := #[]
  for i in [:la.size] do
    let h ← structuralHEq la[i]! ra[i]! (depth - 1) locals (path ++ s!".arg[{i}]")
    let h ← match thm.argKinds[i]! with
      | .eq => mkEqOfHEq h
      | .heq => pure h
      | _ => throwError "BasisStructural093 unexpected abstract congruence argument kind."
    args := args ++ #[la[i]!, ra[i]!, h]
  modify fun s => { s with congrSteps := s.congrSteps + 1 }
  cache left0 right0 (mkAppN thm.proof args)

end CasselsFullStructural142
end


end NativeWholeOriginalMapSeed124Engine

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open scoped TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra


meta section
open Lean Meta Elab Tactic

/- Cache only the exact independently checked map124 endpoints and reverse.
The copied structural dispatcher above is byte-identical to the accepted one. -/
elab "phi_native_whole_map_seeded_exact124 " supplied:term " using " suppliedSeed:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← phiNativeWholeNoRecovery118
      (← Term.elabTerm supplied none (catchExPostpone := false))
    let sourceType ← phiNativeWholeNoRecovery118 (← inferType source)
    let target ← phiNativeWholeNoRecovery118 (← goal.getType)
    let seed ← phiNativeWholeNoRecovery118
      (← Term.elabTerm suppliedSeed none (catchExPostpone := false))
    unless seed.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholeLeftOriginalMapHEq124 &&
        seed.getAppArgs.size == 8 do
      throwError "Native124 requires only the exact original map124 eight-vector certificate."
    let a := seed.getAppArgs
    let restriction := mkAppN
      (mkConst ``actualOriginalGlobalPhiNativeWholeLeftRestrictApplyOwn119 seed.getAppFn.constLevels!) a
    let phi := mkAppN
      (mkConst ``actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 seed.getAppFn.constLevels!) a
    let (expectedLeft, expectedRight) ← phiNativeWholeOriginalMapPair124 restriction phi
    let seedType ← phiNativeWholeNoRecovery118 (← whnf (← inferType seed))
    let some (seedLeftType, seedLeft, seedRightType, seedRight) := seedType.consumeMData.headBeta.heq?
      | throwError "Native124 map certificate must have its own stored HEq4."
    unless seedLeft.consumeMData.equal expectedLeft.consumeMData &&
        seedRight.consumeMData.equal expectedRight.consumeMData &&
        seedLeftType.consumeMData.equal (← inferType expectedLeft).consumeMData &&
        seedRightType.consumeMData.equal (← inferType expectedRight).consumeMData do
      throwError "Native124 refuses map seed on different original maps/types."
    let (leftCarrier, leftPoint, rightCarrier, rightPoint) ←
      phiNativeWholePointPair122 restriction phi
    let some (ta, tx, tb, ty) := target.consumeMData.headBeta.heq?
      | throwError "Native124 requires the exact original middle-point HEq4 target."
    unless ta.consumeMData.equal leftCarrier.consumeMData &&
        tx.consumeMData.equal leftPoint.consumeMData &&
        tb.consumeMData.equal rightCarrier.consumeMData &&
        ty.consumeMData.equal rightPoint.consumeMData do
      throwError "Native124 refuses a different original middle-point target/vector."
    let reverseSeed ← mkHEqSymm seed
    let (heq, state) ←
      (NativeWholeOriginalMapSeed124Engine.CasselsFullStructural142.structuralHEq
        sourceType target 96 #[] "full142").run
          { pairs := #[(seedLeft, seedRight, seed), (seedRight, seedLeft, reverseSeed)] }
    let typeProof ← mkEqOfHEq heq
    let proof ← phiNativeWholeNoRecovery118
      (mkAppN (mkConst ``Eq.mp [Level.zero]) #[sourceType, target, typeProof, source])
    logInfo m!"Native124 ordinary map-seeded compatibility: native={state.wrapperLeaves}, proof={state.proofLeaves}, fallback={state.fallbackProofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}."
    goal.assign proof
    replaceMainGoal []

end


meta section
open Lean Meta Elab Term

/- Build the complete HEq in ONE stored-vector extraction. The four separate
term getters previously incurred expected-type conversions before the tactic. -/
private def phiNativeWholeMiddleVectors125 (restriction phi : Expr) :
    TermElabM (Expr × Expr × Expr × Expr × List Level) := do
  let restriction ← phiNativeWholeNoRecovery118 restriction
  let phi ← phiNativeWholeNoRecovery118 phi
  let (a, x, b, y) ← phiNativeWholePointPair122 restriction phi
  -- Both passed own119 statements are stored Eq propositions. Do not whnf their
  -- carrier types or reconstruct point types under a HEq expected-type telescope.
  let rt ← phiNativeWholeNoRecovery118 (← inferType restriction)
  let pt ← phiNativeWholeNoRecovery118 (← inferType phi)
  let .const rn rl := rt.consumeMData.headBeta.getAppFn
    | throwError "Native125 original restriction own-type lacks its stored Eq head."
  let .const pn pl := pt.consumeMData.headBeta.getAppFn
    | throwError "Native125 original Phi own-type lacks its stored Eq head."
  unless rn == ``Eq && pn == ``Eq && rl.length == 1 && pl.length == 1 && rl == pl do
    logInfo m!"Native125 original Eq universe vectors: restriction={rl}; Phi={pl}."
    throwError "Native125 refuses different actual point Eq universe vectors."
  let some (ra, _, rx) := rt.consumeMData.headBeta.eq?
    | throwError "Native125 restriction statement is not its own literal Eq3."
  let some (pb, py, _) := pt.consumeMData.headBeta.eq?
    | throwError "Native125 Phi statement is not its own literal Eq3."
  unless ra.consumeMData.equal a.consumeMData && rx.consumeMData.equal x.consumeMData &&
      pb.consumeMData.equal b.consumeMData && py.consumeMData.equal y.consumeMData do
    throwError "Native125 refuses different raw original carrier/point endpoints."
  return (a, x, b, y, rl)

elab "phi_native_whole_middle_vector125% " mode:num restriction:term " and " phi:term : term => do
  unless mode.getNat < 2 do
    throwError "Native125 requires original HEq proposition0/reflexivity proof1."
  let (a, x, b, y, levels) ← phiNativeWholeMiddleVectors125
    (← Term.elabTerm restriction none (catchExPostpone := false))
    (← Term.elabTerm phi none (catchExPostpone := false))
  if mode.getNat == 0 then
    logInfo m!"Native125 original HEq4 target emitted in one stored-vector call; own119 Eq levels raw join, all four carrier/point endpoints raw unchanged."
    return ← phiNativeWholeNoRecovery118 (mkAppN (mkConst ``HEq levels) #[a, x, b, y])
  let sourceType := mkAppN (mkConst ``HEq levels) #[a, x, a, x]
  let proof ← phiNativeWholeNoRecovery118 (mkAppN (mkConst ``HEq.refl levels) #[a, x])
  let actualType ← phiNativeWholeNoRecovery118 (← inferType proof)
  unless actualType.consumeMData.equal sourceType.consumeMData do
    throwError "Native125 exact original reflexivity proof changed stored carrier/point/type."
  logInfo m!"Native125 source HEq.refl emitted using exact original carrier/point/levels without an expected-type endpoint reconstruction."
  return proof

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def actualOriginalGlobalPhiNativeWholeLeftMiddlePointProposition125
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) : Prop :=
    phi_native_whole_middle_vector125% 0
      (actualOriginalGlobalPhiNativeWholeLeftRestrictApplyOwn119 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 p hp P hP s)


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholeLeftMiddlePointHEq125
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    phi_native_whole_middle_vector125% 0
      (actualOriginalGlobalPhiNativeWholeLeftRestrictApplyOwn119 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 p hp P hP s) := by
  phi_native_whole_map_seeded_exact124
    (phi_native_whole_middle_vector125% 1
      (actualOriginalGlobalPhiNativeWholeLeftRestrictApplyOwn119 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 p hp P hP s)) using
    (actualOriginalGlobalPhiNativeWholeLeftOriginalMapHEq124 p hp P hP s)


universe wNativeWhole127

private theorem phiNativeWholeFourLinkHEq127 {A B : Sort wNativeWhole127}
    (x0 x1 x2 : A) (y0 y1 : B)
    (h01 : x0 = x1) (h12 : x1 = x2) (hxy : HEq x2 y0) (hy : y0 = y1) :
    HEq x0 y1 := by
  cases h01
  cases h12
  cases hy
  exact hxy

meta section
open Lean Meta Elab Term

private structure PhiNativeWholeEqualityVector127 where
  carrier : Expr
  left : Expr
  right : Expr
  levels : List Level
  proof : Expr
  proposition : Expr

private def phiNativeWholeEqualityVector127 (proof : Expr) :
    TermElabM PhiNativeWholeEqualityVector127 := do
  let proof ← phiNativeWholeNoRecovery118 proof
  let proposition ← phiNativeWholeNoRecovery118 (← inferType proof)
  let some (carrier, left, right) := proposition.consumeMData.headBeta.eq?
    | throwError "Native127 requires the exact component's stored literal Eq3."
  let .const name levels := proposition.consumeMData.headBeta.getAppFn
    | throwError "Native127 stored Eq lacks its actual constant universe vector."
  unless name == ``Eq && levels.length == 1 do
    throwError "Native127 requires the original singleton Eq level vector."
  return { carrier, left, right, levels, proof, proposition }

private def phiNativeWholeRawJoin127 (label : String) (left right : Expr) :
    TermElabM Unit := do
  unless left.consumeMData.equal right.consumeMData do
    let mut l := left.consumeMData
    let mut r := right.consumeMData
    let mut path := label
    for _ in [:8] do
      if l.equal r then break
      let la := l.getAppArgs
      let ra := r.getAppArgs
      logInfo m!"Native127 raw join boundary {path}: left head={l.getAppFn}, arity={la.size}; right head={r.getAppFn}, arity={ra.size}."
      if la.size > 0 && la.size == ra.size && l.getAppFn.equal r.getAppFn then
        let mut differing : Option Nat := none
        for i in [:la.size] do
          if differing.isNone && !(la[i]!.consumeMData.equal ra[i]!.consumeMData) then
            differing := some i
        match differing with
        | some i =>
          l := la[i]!.consumeMData
          r := ra[i]!.consumeMData
          path := path ++ s!".arg[{i}]"
        | none => break
      else
        break
    throwError "Native127 refuses different original {label}; no carrier/point guard bypass."

elab "phi_native_whole_left_four_link127% " first:term " and " second:term
    " and " middle:term " and " last:term : term => do
  let first ← phiNativeWholeNoRecovery118
    (← Term.elabTerm first none (catchExPostpone := false))
  let second ← phiNativeWholeNoRecovery118
    (← Term.elabTerm second none (catchExPostpone := false))
  let middle ← phiNativeWholeNoRecovery118
    (← Term.elabTerm middle none (catchExPostpone := false))
  let last ← phiNativeWholeNoRecovery118
    (← Term.elabTerm last none (catchExPostpone := false))
  unless first.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholeLeftCompApplyOwn118 &&
      second.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholeLeftRestrictApplyOwn119 &&
      middle.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholeLeftMiddlePointHEq125 &&
      last.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 &&
      first.getAppArgs.size == 8 && second.getAppArgs.size == 8 &&
      middle.getAppArgs.size == 8 && last.getAppArgs.size == 8 do
    throwError "Native127 requires exact original Comp118/Restrict119/Middle125/Phi119 eight-vectors."
  for component in #[second, middle, last] do
    for i in [:8] do
      phiNativeWholeRawJoin127 s!"component original argument{i}"
        first.getAppArgs[i]! component.getAppArgs[i]!
  let h01 ← phiNativeWholeEqualityVector127 first
  let h12 ← phiNativeWholeEqualityVector127 second
  let hy ← phiNativeWholeEqualityVector127 last
  let hp ← phiNativeWholeNoRecovery118 (← inferType middle)
  let some (a, x, b, y) := hp.consumeMData.headBeta.heq?
    | throwError "Native127 middle125 lost its exact original stored HEq4."
  let .const hn hl := hp.consumeMData.headBeta.getAppFn
    | throwError "Native127 middle HEq lacks the stored actual constant universe vector."
  unless hn == ``HEq && hl == h01.levels && h01.levels == h12.levels &&
      h01.levels == hy.levels do
    throwError "Native127 component original Eq/HEq universe vectors differ."
  phiNativeWholeRawJoin127 "first/second carrier" h01.carrier h12.carrier
  phiNativeWholeRawJoin127 "second/middle LEFT carrier" h12.carrier a
  phiNativeWholeRawJoin127 "middle RIGHT/last carrier" b hy.carrier
  phiNativeWholeRawJoin127 "first.right/second.left" h01.right h12.left
  phiNativeWholeRawJoin127 "second.right/middle.left" h12.right x
  phiNativeWholeRawJoin127 "middle.right/last.left" y hy.left
  let arguments := #[a, b, h01.left, h01.right, h12.right, hy.left, hy.right,
    first, second, middle, last]
  let sort := mkSort h01.levels[0]!
  let expectedDomains := #[sort, sort, a, a, a, b, b,
    h01.proposition, h12.proposition, hp, hy.proposition]
  let info ← getConstInfo ``phiNativeWholeFourLinkHEq127
  unless info.levelParams.length == h01.levels.length do
    throwError "Native127 ordinary four-link theorem has a different level count."
  let mut lawType := info.instantiateTypeLevelParams h01.levels
  for i in [:11] do
    let .forallE _ domain body _ := lawType
      | throwError "Native127 ordinary four-link prefix ended at {i}."
    phiNativeWholeRawJoin127 s!"four-link exact binder{i}" domain expectedDomains[i]!
    lawType := body.instantiate1 arguments[i]!
  let proof ← phiNativeWholeNoRecovery118
    (mkAppN (mkConst ``phiNativeWholeFourLinkHEq127 h01.levels) arguments)
  let actualType ← phiNativeWholeNoRecovery118 (← inferType proof)
  let expectedType := mkAppN (mkConst ``HEq h01.levels)
    #[h01.carrier, h01.left, hy.carrier, hy.right]
  phiNativeWholeRawJoin127 "four-link exact complete type" actualType expectedType
  phiNativeWholeRawJoin127 "four-link own final proposition" actualType lawType
  logInfo m!"Native127 ordinary four-link/11-vector HEq assembly: all original8 parameters, both carrier sides, three intermediate points, every binder, complete endpoints/universe/proposition raw join. Original composition/restriction/Phi maps and actions unchanged."
  return proof

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholeLeftAssemblyHEqOwn127
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_whole_left_four_link127%
      (actualOriginalGlobalPhiNativeWholeLeftCompApplyOwn118 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftRestrictApplyOwn119 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftMiddlePointHEq125 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 p hp P hP s)) :=
    phi_native_whole_left_four_link127%
      (actualOriginalGlobalPhiNativeWholeLeftCompApplyOwn118 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftRestrictApplyOwn119 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftMiddlePointHEq125 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 p hp P hP s)


meta section
open Lean Meta Elab Tactic Term

private def phiNativeWholeOriginalFactoryEquality128 (factory : Expr) :
    TermElabM (Expr × Expr × Expr × List Level) := do
  let factory ← phiNativeWholeNoRecovery118 factory
  unless factory.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholeLeftPointProposition118 &&
      factory.getAppArgs.size == 8 do
    throwError "Native128 requires only the exact original left factory118 eight-vector."
  let proposition ← phiNativeWholeNoRecovery118 (← whnf factory)
  let some (a, x, y) := proposition.consumeMData.headBeta.eq?
    | throwError "Native128 original factory118 body is not its literal Eq3."
  let .const name levels := proposition.consumeMData.headBeta.getAppFn
    | throwError "Native128 original factory Eq lacks its exact universe vector."
  unless name == ``Eq && levels.length == 1 do
    throwError "Native128 requires the original factory singleton Eq universe."
  return (a, x, y, levels)

elab "phi_native_whole_factory_heq128% " factory:term : term => do
  let (a, x, y, levels) ← phiNativeWholeOriginalFactoryEquality128
    (← Term.elabTerm factory none (catchExPostpone := false))
  return ← phiNativeWholeNoRecovery118 (mkAppN (mkConst ``HEq levels) #[a, x, a, y])

elab "phi_native_whole_literal_seeded128 " supplied:term " using " carrierSeed:term
    " and " mapSeed:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← phiNativeWholeNoRecovery118
      (← Term.elabTerm supplied none (catchExPostpone := false))
    let carrierSeed ← phiNativeWholeNoRecovery118
      (← Term.elabTerm carrierSeed none (catchExPostpone := false))
    let mapSeed ← phiNativeWholeNoRecovery118
      (← Term.elabTerm mapSeed none (catchExPostpone := false))
    unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholeLeftAssemblyHEqOwn127 &&
        carrierSeed.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholeLeftCarrierEq121 &&
        mapSeed.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholeLeftOriginalMapHEq124 &&
        source.getAppArgs.size == 8 && carrierSeed.getAppArgs.size == 8 && mapSeed.getAppArgs.size == 8 do
      throwError "Native128 requires only exact own127/carrier121/map124 eight-vectors."
    let arguments := source.getAppArgs
    for component in #[carrierSeed, mapSeed] do
      for i in [:8] do
        phiNativeWholeRawJoin127 s!"literal adapter original parameter{i}"
          arguments[i]! component.getAppArgs[i]!
    let levels := source.getAppFn.constLevels!
    let factory := mkAppN
      (mkConst ``actualOriginalGlobalPhiNativeWholeLeftPointProposition118 levels) arguments
    let (factoryCarrier, factoryLeft, factoryRight, factoryLevels) ←
      phiNativeWholeOriginalFactoryEquality128 factory
    let target ← phiNativeWholeNoRecovery118 (← goal.getType)
    let expectedTarget := mkAppN (mkConst ``HEq factoryLevels)
      #[factoryCarrier, factoryLeft, factoryCarrier, factoryRight]
    phiNativeWholeRawJoin127 "literal complete original factory target" target expectedTarget
    let sourceType ← phiNativeWholeNoRecovery118 (← inferType source)
    let some (sourceA, sourceLeft, sourceB, _) := sourceType.consumeMData.headBeta.heq?
      | throwError "Native128 own127 lacks its stored complete HEq4."
    let carrierType ← phiNativeWholeNoRecovery118 (← inferType carrierSeed)
    let some (_, seedA, seedB) := carrierType.consumeMData.headBeta.eq?
      | throwError "Native128 carrier121 lacks its genuine complete stored type equality."
    phiNativeWholeRawJoin127 "literal source LEFT/factory carrier" sourceA factoryCarrier
    phiNativeWholeRawJoin127 "literal original source/factory LEFT point" sourceLeft factoryLeft
    phiNativeWholeRawJoin127 "literal source LEFT/carrier-seed LEFT" sourceA seedA
    phiNativeWholeRawJoin127 "literal source RIGHT/carrier-seed RIGHT" sourceB seedB
    let mapType ← phiNativeWholeNoRecovery118 (← inferType mapSeed)
    let some (_, mapLeft, _, mapRight) := mapType.consumeMData.headBeta.heq?
      | throwError "Native128 map124 lacks its genuine original stored HEq4."
    let restriction := mkAppN
      (mkConst ``actualOriginalGlobalPhiNativeWholeLeftRestrictApplyOwn119 levels) arguments
    let phi := mkAppN
      (mkConst ``actualOriginalGlobalPhiNativeWholeLeftPhiApplyLiftOwn119 levels) arguments
    let (actualMapLeft, actualMapRight) ← phiNativeWholeOriginalMapPair124 restriction phi
    phiNativeWholeRawJoin127 "literal original map seed LEFT" mapLeft actualMapLeft
    phiNativeWholeRawJoin127 "literal original map seed RIGHT" mapRight actualMapRight
    let typeHEq ← phiNativeWholeNoRecovery118 (← mkHEqOfEq carrierSeed)
    let reverseType ← phiNativeWholeNoRecovery118 (← mkHEqSymm typeHEq)
    let reverseMap ← phiNativeWholeNoRecovery118 (← mkHEqSymm mapSeed)
    let (heq, state) ←
      (NativeWholeOriginalMapSeed124Engine.CasselsFullStructural142.structuralHEq
        sourceType target 96 #[] "full142").run
          { pairs := #[(seedA, seedB, typeHEq), (seedB, seedA, reverseType),
            (mapLeft, mapRight, mapSeed), (mapRight, mapLeft, reverseMap)] }
    let typeProof ← mkEqOfHEq heq
    let proof ← phiNativeWholeNoRecovery118
      (mkAppN (mkConst ``Eq.mp [Level.zero]) #[sourceType, target, typeProof, source])
    logInfo m!"Native128 literal factory compatibility consumes only complete carrier121/map124 ordinary exact seeds: native={state.wrapperLeaves}, proof={state.proofLeaves}, fallback={state.fallbackProofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}."
    goal.assign proof
    replaceMainGoal []

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholeLeftLiteralHEq128
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    phi_native_whole_factory_heq128%
      (actualOriginalGlobalPhiNativeWholeLeftPointProposition118 p hp P hP s) := by
  phi_native_whole_literal_seeded128
    (actualOriginalGlobalPhiNativeWholeLeftAssemblyHEqOwn127 p hp P hP s) using
    (actualOriginalGlobalPhiNativeWholeLeftCarrierEq121 p hp P hP s) and
    (actualOriginalGlobalPhiNativeWholeLeftOriginalMapHEq124 p hp P hP s)


meta section
open Lean Meta Elab Term

elab "phi_native_whole_literal_eq128% " supplied:term : term => do
  let proof ← phiNativeWholeNoRecovery118
    (← Term.elabTerm supplied none (catchExPostpone := false))
  unless proof.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholeLeftLiteralHEq128 &&
      proof.getAppArgs.size == 8 do
    throwError "Native128 requires the original literal HEq128 eight-vector."
  let proposition ← phiNativeWholeNoRecovery118 (← inferType proof)
  let some (a, x, b, y) := proposition.consumeMData.headBeta.heq?
    | throwError "Native128 literal certificate lacks its stored HEq4."
  phiNativeWholeRawJoin127 "literal homogeneous LEFT/RIGHT carrier" a b
  let .const name levels := proposition.consumeMData.headBeta.getAppFn
    | throwError "Native128 literal HEq lacks its universe head."
  unless name == ``HEq && levels.length == 1 do
    throwError "Native128 literal HEq singleton universe differs."
  let info ← getConstInfo ``eq_of_heq
  unless info.levelParams.length == levels.length do
    throwError "Native128 eq_of_heq universe count differs."
  let arguments := #[a, x, y, proof]
  let expectedDomains := #[mkSort levels[0]!, a, a, proposition]
  let mut lawType := info.instantiateTypeLevelParams levels
  for i in [:4] do
    let .forallE _ domain body _ := lawType
      | throwError "Native128 ordinary eq_of_heq prefix ended at {i}."
    phiNativeWholeRawJoin127 s!"literal eq_of_heq exact binder{i}" domain expectedDomains[i]!
    lawType := body.instantiate1 arguments[i]!
  let result ← phiNativeWholeNoRecovery118
    (mkAppN (mkConst ``eq_of_heq levels) arguments)
  let actualType ← phiNativeWholeNoRecovery118 (← inferType result)
  let expectedType := mkAppN (mkConst ``Eq levels) #[a, x, y]
  phiNativeWholeRawJoin127 "literal whole Eq exact endpoint/type" actualType expectedType
  phiNativeWholeRawJoin127 "literal whole Eq law proposition" actualType lawType
  logInfo m!"Native128 ordinary eq_of_heq uses all four exact stored vectors; both carriers and complete factory endpoints raw unchanged."
  return result

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholeLeftLiteralEqOwn128
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_whole_literal_eq128%
      (actualOriginalGlobalPhiNativeWholeLeftLiteralHEq128 p hp P hP s)) :=
    phi_native_whole_literal_eq128%
      (actualOriginalGlobalPhiNativeWholeLeftLiteralHEq128 p hp P hP s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholeLinearLeftPoint128
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let E2 := (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (hypersurfaceToBase p hp))
          (positiveSheafOfModules (grading I) 2)))
    letI : Module K E2 := Module.compHom E2 (algebraMap K L)
    letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
    letI : Module K ((moduleSpecΓFunctor
        (R := .of ((hypersurface p hp).residueField P.1))).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (toBase (equationIdeal p hp)))
          (positiveSheafOfModules (grading (equationIdeal p hp)) 2)))) :=
      Module.compHom _ (algebraMap K ((hypersurface p hp).residueField P.1))
    letI : IsScalarTower K ((hypersurface p hp).residueField P.1)
      ((moduleSpecΓFunctor
        (R := .of ((hypersurface p hp).residueField P.1))).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (toBase (equationIdeal p hp)))
          (positiveSheafOfModules (grading (equationIdeal p hp)) 2)))) :=
      IsScalarTower.of_compHom K ((hypersurface p hp).residueField P.1) _
    (((actualOriginalPositiveTwoContractedNativeDifferentialMap p hp P hP).restrictScalars K).comp
      (actualOriginalGlobalCanonicalQuadraticPhiLinearMap p hp P)) s =
    actualOriginalPositiveTwoContractedNativeDifferentialMap p hp P hP
      (actualOriginalGlobalCanonicalQuadraticPhi p hp P s) := by
  intro C I R L E2
  basis_full_exact142 (actualOriginalGlobalPhiNativeWholeLeftLiteralEqOwn128 p hp P hP s)

universe wNativeWhole128

private theorem phiNativeWholeThreeEqualityLinks128 {A : Sort wNativeWhole128}
    (x0 x1 x2 x3 : A) (h01 : x0 = x1) (h12 : x1 = x2) (h23 : x2 = x3) :
    x0 = x3 := h01.trans (h12.trans h23)

meta section
open Lean Meta Elab Term

private structure PhiNativeWholeEq128 where
  carrier : Expr
  left : Expr
  right : Expr
  levels : List Level
  proof : Expr
  proposition : Expr

private def phiNativeWholeEqVector128 (proof : Expr) : TermElabM PhiNativeWholeEq128 := do
  let proof ← phiNativeWholeNoRecovery118 proof
  let proposition ← phiNativeWholeNoRecovery118 (← whnf (← inferType proof))
  let some (carrier, left, right) := proposition.consumeMData.headBeta.eq?
    | throwError "Native128 component is not a stored Eq3."
  let .const name levels := proposition.consumeMData.headBeta.getAppFn
    | throwError "Native128 Eq component lacks its constant universe vector."
  unless name == ``Eq && levels.length == 1 do
    throwError "Native128 Eq component has a different universe head."
  return { carrier, left, right, levels, proof, proposition }

private def phiNativeWholeJoin128 (label : String) (left right : Expr) : TermElabM Unit := do
  unless left.consumeMData.equal right.consumeMData do
    let mut l := left.consumeMData
    let mut r := right.consumeMData
    let mut path := label
    for _ in [:8] do
      if l.equal r then break
      let la := l.getAppArgs
      let ra := r.getAppArgs
      logInfo m!"Native128 first raw join boundary {path}: left head={l.getAppFn}, arity={la.size}; right head={r.getAppFn}, arity={ra.size}."
      if la.size > 0 && la.size == ra.size && l.getAppFn.equal r.getAppFn then
        let mut differing : Option Nat := none
        for i in [:la.size] do
          if differing.isNone && !(la[i]!.consumeMData.equal ra[i]!.consumeMData) then
            differing := some i
        match differing with
        | some i =>
          l := la[i]!.consumeMData
          r := ra[i]!.consumeMData
          path := path ++ s!".arg[{i}]"
        | none => break
      else
        break
    throwError "Native128 refuses different original {label}; no carrier/point guard bypass."

/-- All arguments are read from the three exact ordinary certificates. No
new geometric type is reconstructed when applying the tiny chain theorem. -/
private def phiNativeWholeThreeOwn128 (first second third : Expr)
    (reverseThird : Bool) : TermElabM Expr := do
  let first ← phiNativeWholeEqVector128 first
  let second ← phiNativeWholeEqVector128 second
  let mut third ← phiNativeWholeEqVector128 third
  if reverseThird then
    let reverse ← phiNativeWholeNoRecovery118
      (mkAppN (mkConst ``Eq.symm third.levels)
        #[third.carrier, third.left, third.right, third.proof])
    third ← phiNativeWholeEqVector128 reverse
  unless first.levels == second.levels && first.levels == third.levels do
    throwError "Native128 component equality universe vectors differ."
  phiNativeWholeJoin128 "first/second carrier" first.carrier second.carrier
  phiNativeWholeJoin128 "second/third carrier" second.carrier third.carrier
  phiNativeWholeJoin128 "first.right/second.left" first.right second.left
  phiNativeWholeJoin128 "second.right/third.left" second.right third.left
  let arguments := #[first.carrier, first.left, first.right, second.right,
    third.right, first.proof, second.proof, third.proof]
  let expectedDomains := #[← inferType first.carrier, first.carrier,
    first.carrier, first.carrier, first.carrier, first.proposition,
    second.proposition, third.proposition]
  let info ← getConstInfo ``phiNativeWholeThreeEqualityLinks128
  unless info.levelParams.length == first.levels.length do
    throwError "Native128 ordinary three-link theorem has a different level count."
  let mut lawType := info.instantiateTypeLevelParams first.levels
  for i in [:8] do
    let .forallE _ domain body _ := lawType
      | throwError "Native128 ordinary chain prefix ended at {i}."
    phiNativeWholeJoin128 s!"three-link binder{i}" domain expectedDomains[i]!
    lawType := body.instantiate1 arguments[i]!
  let proof ← phiNativeWholeNoRecovery118
    (mkAppN (mkConst ``phiNativeWholeThreeEqualityLinks128 first.levels) arguments)
  let proofType ← phiNativeWholeNoRecovery118 (← whnf (← inferType proof))
  let some (carrier, left, right) := proofType.consumeMData.headBeta.eq?
    | throwError "Native128 ordinary chain did not produce Eq3."
  phiNativeWholeJoin128 "chain final carrier" carrier first.carrier
  phiNativeWholeJoin128 "chain original first point" left first.left
  phiNativeWholeJoin128 "chain original last point" right third.right
  logInfo m!"Native128 exact three-link/eight-vector chain: all carrier/universe/two intermediate point/binder/full endpoint raw joins true; reverseThird={reverseThird}. Original maps/actions unchanged."
  return proof

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholeLinearRightPoint117
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let E2 := (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (hypersurfaceToBase p hp))
          (positiveSheafOfModules (grading I) 2)))
    letI : Module K E2 := Module.compHom E2 (algebraMap K L)
    letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
    letI : Module K ((moduleSpecΓFunctor
        (R := .of ((hypersurface p hp).residueField P.1))).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (toBase (equationIdeal p hp)))
          (positiveSheafOfModules (grading (equationIdeal p hp)) 2)))) :=
      Module.compHom _ (algebraMap K ((hypersurface p hp).residueField P.1))
    letI : IsScalarTower K ((hypersurface p hp).residueField P.1)
      ((moduleSpecΓFunctor
        (R := .of ((hypersurface p hp).residueField P.1))).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (toBase (equationIdeal p hp)))
          (positiveSheafOfModules (grading (equationIdeal p hp)) 2)))) :=
      IsScalarTower.of_compHom K ((hypersurface p hp).residueField P.1) _
    ((actualResidueDifferentialDerivation (K := K) (R := R) (L := L)).toLinearMap.comp
      (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP)) s =
    actualResidueDifferentialDerivation (K := K) (R := R) (L := L)
      (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s) := by
  intro C I R L E2
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholeLinearCoefficientPoint117
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let E2 := (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (hypersurfaceToBase p hp))
          (positiveSheafOfModules (grading I) 2)))
    letI : Module K E2 := Module.compHom E2 (algebraMap K L)
    letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
    letI : Module K ((moduleSpecΓFunctor
        (R := .of ((hypersurface p hp).residueField P.1))).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (toBase (equationIdeal p hp)))
          (positiveSheafOfModules (grading (equationIdeal p hp)) 2)))) :=
      Module.compHom _ (algebraMap K ((hypersurface p hp).residueField P.1))
    letI : IsScalarTower K ((hypersurface p hp).residueField P.1)
      ((moduleSpecΓFunctor
        (R := .of ((hypersurface p hp).residueField P.1))).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (toBase (equationIdeal p hp)))
          (positiveSheafOfModules (grading (equationIdeal p hp)) 2)))) :=
      IsScalarTower.of_compHom K ((hypersurface p hp).residueField P.1) _
    actualOriginalPositiveTwoContractedNativeDifferentialMap p hp P hP
      (actualOriginalGlobalCanonicalQuadraticPhi p hp P s) =
    actualResidueDifferentialDerivation (K := K) (R := R) (L := L)
      (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s) := by
  intro C I R L E2
  exact actualOriginalGlobalCanonicalQuadraticPhi_native_contracted_coefficient p hp P hP s


meta section
open Lean Meta Elab Term

private def phiNativeWholePointwiseCarrierPair129 (coefficient right : Expr) :
    TermElabM (Expr × Expr × List Level) := do
  let coefficient ← phiNativeWholeNoRecovery118 coefficient
  let right ← phiNativeWholeNoRecovery118 right
  unless coefficient.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholeLinearCoefficientPoint117 &&
      right.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholeLinearRightPoint117 &&
      coefficient.getAppArgs.size == 8 && right.getAppArgs.size == 8 do
    throwError "Native129 requires only exact original Coefficient117/Right117 eight-vectors."
  for i in [:8] do
    phiNativeWholeRawJoin127 s!"pointwise carrier original parameter{i}"
      coefficient.getAppArgs[i]! right.getAppArgs[i]!
  let c ← phiNativeWholeEqVector128 coefficient
  let r ← phiNativeWholeEqVector128 right
  unless c.levels == r.levels do
    throwError "Native129 coefficient/right original Eq universe vectors differ."
  return (c.carrier, r.carrier, c.levels)

/- Follow only the actual801 carrier frontier; all installed intermediate
constructor heads/arities and diagnosed terminal instance heads are guarded. -/
private def phiNativeWholePointwiseRingPair129 (coefficient right : Expr) :
    TermElabM (Expr × Expr) := do
  let (a, b, _) ← phiNativeWholePointwiseCarrierPair129 coefficient right
  let path := #[(``TensorProduct, 8, 6), (``Algebra.toModule, 5, 2),
    (``CommRing.toCommSemiring, 2, 1),
    (``HomogeneousLocalization.homogeneousLocalizationCommRing, 11, 5),
    (``Submodule.addSubgroupClass, 5, 3),
    (``Submodule.Quotient.addCommGroup, 6, 2)]
  let mut left := a
  let mut right := b
  for (name, arity, index) in path do
    let la := left.consumeMData.getAppArgs
    let ra := right.consumeMData.getAppArgs
    unless left.consumeMData.getAppFn.isConstOf name &&
        right.consumeMData.getAppFn.isConstOf name && la.size == arity && ra.size == arity do
      logInfo m!"Native129 actual carrier frontier expected {name}/{arity}: left={left}; right={right}."
      throwError "Native129 refuses a different original diagnosed carrier path."
    unless index < arity do
      throwError "Native129 actual carrier path index exceeds its guarded arity."
    left := la[index]!
    right := ra[index]!
  unless left.consumeMData.getAppFn.isConstOf ``CommRing.toRing &&
      left.consumeMData.getAppArgs.size == 2 &&
      right.consumeMData.getAppFn.isConstOf ``AddMonoidAlgebra.ring &&
      right.consumeMData.getAppArgs.size == 4 do
    logInfo m!"Native129 actual polynomial Ring endpoint pair: left={left}; right={right}."
    throwError "Native129 requires exact actual CommRing.toRing2/AddMonoidAlgebra.ring4 frontier."
  return (left, right)

elab "phi_native_whole_pointwise_ring129% " coefficient:term " and " right:term : term => do
  let (left, right) ← phiNativeWholePointwiseRingPair129
    (← Term.elabTerm coefficient none (catchExPostpone := false))
    (← Term.elabTerm right none (catchExPostpone := false))
  let leftType ← phiNativeWholeNoRecovery118 (← inferType left)
  let rightType ← phiNativeWholeNoRecovery118 (← inferType right)
  let leftLevel ← getLevel leftType
  let rightLevel ← getLevel rightType
  unless leftLevel == rightLevel do
    throwError "Native129 actual Ring endpoint type universe vectors differ."
  logInfo m!"Native129 actual Ring projection endpoints: left={left}; right={right}; leftType={leftType}; rightType={rightType}. Retained heterogeneous types, no assumed homogeneous Ring/carrier equality."
  return ← phiNativeWholeNoRecovery118
    (mkAppN (mkConst ``HEq [leftLevel]) #[leftType, left, rightType, right])

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholePointwiseRingHEq129
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    phi_native_whole_pointwise_ring129%
      (actualOriginalGlobalPhiNativeWholeLinearCoefficientPoint117 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLinearRightPoint117 p hp P hP s) := by
  rfl


meta section
open Lean Meta Elab Tactic Term

private def phiNativeWholePointwiseCarrierProposition129 (coefficient right : Expr) :
    TermElabM (Expr × Expr × Expr × List Level) := do
  let (a, b, levels) ← phiNativeWholePointwiseCarrierPair129 coefficient right
  let sort := mkSort levels[0]!
  let typeLevels := [Level.succ levels[0]!]
  phiNativeWholeRawJoin127 "pointwise carrier LEFT sort" (← inferType a) sort
  phiNativeWholeRawJoin127 "pointwise carrier RIGHT sort" (← inferType b) sort
  return (a, b, sort, typeLevels)

elab "phi_native_whole_pointwise_carrier129% " coefficient:term " and " right:term : term => do
  let (a, b, sort, typeLevels) ← phiNativeWholePointwiseCarrierProposition129
    (← Term.elabTerm coefficient none (catchExPostpone := false))
    (← Term.elabTerm right none (catchExPostpone := false))
  return ← phiNativeWholeNoRecovery118 (mkAppN (mkConst ``Eq typeLevels) #[sort, a, b])

elab "phi_native_whole_pointwise_carrier_seeded129 " suppliedSeed:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let seed ← phiNativeWholeNoRecovery118
      (← Term.elabTerm suppliedSeed none (catchExPostpone := false))
    unless seed.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholePointwiseRingHEq129 &&
        seed.getAppArgs.size == 8 do
      throwError "Native129 requires only actual original Ring129 eight-vector certificate."
    let arguments := seed.getAppArgs
    let levels := seed.getAppFn.constLevels!
    let coefficient := mkAppN
      (mkConst ``actualOriginalGlobalPhiNativeWholeLinearCoefficientPoint117 levels) arguments
    let right := mkAppN
      (mkConst ``actualOriginalGlobalPhiNativeWholeLinearRightPoint117 levels) arguments
    let (a, b, sort, typeLevels) ← phiNativeWholePointwiseCarrierProposition129 coefficient right
    let target ← phiNativeWholeNoRecovery118 (← goal.getType)
    let expectedTarget := mkAppN (mkConst ``Eq typeLevels) #[sort, a, b]
    phiNativeWholeRawJoin127 "pointwise complete original carrier target" target expectedTarget
    let (actualLeft, actualRight) ← phiNativeWholePointwiseRingPair129 coefficient right
    let seedType ← phiNativeWholeNoRecovery118 (← inferType seed)
    let some (leftType, left, rightType, right) := seedType.consumeMData.headBeta.heq?
      | throwError "Native129 Ring seed lacks its own exact stored HEq4."
    phiNativeWholeRawJoin127 "pointwise Ring seed exact LEFT" left actualLeft
    phiNativeWholeRawJoin127 "pointwise Ring seed exact RIGHT" right actualRight
    phiNativeWholeRawJoin127 "pointwise Ring seed exact LEFT type" leftType (← inferType actualLeft)
    phiNativeWholeRawJoin127 "pointwise Ring seed exact RIGHT type" rightType (← inferType actualRight)
    let source := mkAppN (mkConst ``Eq.refl typeLevels) #[sort, a]
    let source ← phiNativeWholeNoRecovery118 source
    let sourceType ← phiNativeWholeNoRecovery118 (← inferType source)
    let expectedSource := mkAppN (mkConst ``Eq typeLevels) #[sort, a, a]
    phiNativeWholeRawJoin127 "pointwise exact original carrier reflexivity" sourceType expectedSource
    let reverseSeed ← mkHEqSymm seed
    let (heq, state) ←
      (NativeWholeOriginalMapSeed124Engine.CasselsFullStructural142.structuralHEq
        sourceType target 96 #[] "full142").run
          { pairs := #[(left, right, seed), (right, left, reverseSeed)] }
    let typeProof ← mkEqOfHEq heq
    let proof ← phiNativeWholeNoRecovery118
      (mkAppN (mkConst ``Eq.mp [Level.zero]) #[sourceType, target, typeProof, source])
    logInfo m!"Native129 complete actual coefficient/right carrier compatibility consumes only exact polynomial Ring129 seed: native={state.wrapperLeaves}, proof={state.proofLeaves}, fallback={state.fallbackProofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}. Original scalar actions/data unchanged."
    goal.assign proof
    replaceMainGoal []

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholePointwiseCarrierEq129
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    phi_native_whole_pointwise_carrier129%
      (actualOriginalGlobalPhiNativeWholeLinearCoefficientPoint117 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLinearRightPoint117 p hp P hP s) := by
  phi_native_whole_pointwise_carrier_seeded129
    (actualOriginalGlobalPhiNativeWholePointwiseRingHEq129 p hp P hP s)


meta section
open Lean Meta Elab Tactic Term

private def phiNativeWholePointwisePoints130 (coefficient right : Expr) :
    TermElabM (Expr × Expr × Expr × Expr × List Level) := do
  let coefficient ← phiNativeWholeNoRecovery118 coefficient
  let right ← phiNativeWholeNoRecovery118 right
  let (a, b, levels) ← phiNativeWholePointwiseCarrierPair129 coefficient right
  let c ← phiNativeWholeEqVector128 coefficient
  let r ← phiNativeWholeEqVector128 right
  phiNativeWholeRawJoin127 "pointwise stored coefficient carrier" c.carrier a
  phiNativeWholeRawJoin127 "pointwise stored right carrier" r.carrier b
  unless c.levels == levels && r.levels == levels do
    throwError "Native130 pointwise actual point/carrier Eq universes differ."
  return (a, c.right, b, r.right, levels)

elab "phi_native_whole_pointwise_points130% " mode:num coefficient:term " and " right:term : term => do
  unless mode.getNat < 2 do
    throwError "Native130 requires exact actual point HEq0/source reflexivity1."
  let (a, x, b, y, levels) ← phiNativeWholePointwisePoints130
    (← Term.elabTerm coefficient none (catchExPostpone := false))
    (← Term.elabTerm right none (catchExPostpone := false))
  if mode.getNat == 0 then
    return ← phiNativeWholeNoRecovery118 (mkAppN (mkConst ``HEq levels) #[a, x, b, y])
  let proof ← phiNativeWholeNoRecovery118 (mkAppN (mkConst ``HEq.refl levels) #[a, x])
  let actualType ← phiNativeWholeNoRecovery118 (← inferType proof)
  let expectedType := mkAppN (mkConst ``HEq levels) #[a, x, a, x]
  phiNativeWholeRawJoin127 "pointwise exact source reflexivity type" actualType expectedType
  return proof

elab "phi_native_whole_pointwise_points_seeded130 " supplied:term " using " carrierSeed:term
    " and " ringSeed:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← phiNativeWholeNoRecovery118
      (← Term.elabTerm supplied none (catchExPostpone := false))
    let carrierSeed ← phiNativeWholeNoRecovery118
      (← Term.elabTerm carrierSeed none (catchExPostpone := false))
    let ringSeed ← phiNativeWholeNoRecovery118
      (← Term.elabTerm ringSeed none (catchExPostpone := false))
    unless carrierSeed.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholePointwiseCarrierEq129 &&
        ringSeed.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholePointwiseRingHEq129 &&
        carrierSeed.getAppArgs.size == 8 && ringSeed.getAppArgs.size == 8 do
      throwError "Native130 requires only genuine actual Carrier129/Ring129 eight-vector certificates."
    let arguments := carrierSeed.getAppArgs
    for i in [:8] do
      phiNativeWholeRawJoin127 s!"pointwise seed original parameter{i}"
        arguments[i]! ringSeed.getAppArgs[i]!
    let levels := carrierSeed.getAppFn.constLevels!
    let coefficient := mkAppN
      (mkConst ``actualOriginalGlobalPhiNativeWholeLinearCoefficientPoint117 levels) arguments
    let right := mkAppN
      (mkConst ``actualOriginalGlobalPhiNativeWholeLinearRightPoint117 levels) arguments
    let (a, x, b, y, pointLevels) ← phiNativeWholePointwisePoints130 coefficient right
    let target ← phiNativeWholeNoRecovery118 (← goal.getType)
    let expectedTarget := mkAppN (mkConst ``HEq pointLevels) #[a, x, b, y]
    phiNativeWholeRawJoin127 "pointwise exact complete original HEq target" target expectedTarget
    let sourceType ← phiNativeWholeNoRecovery118 (← inferType source)
    let expectedSource := mkAppN (mkConst ``HEq pointLevels) #[a, x, a, x]
    phiNativeWholeRawJoin127 "pointwise exact original source HEq" sourceType expectedSource
    let carrierType ← phiNativeWholeNoRecovery118 (← inferType carrierSeed)
    let some (_, ca, cb) := carrierType.consumeMData.headBeta.eq?
      | throwError "Native130 complete Carrier129 seed lacks its actual literal Eq3."
    phiNativeWholeRawJoin127 "pointwise exact carrier seed LEFT" ca a
    phiNativeWholeRawJoin127 "pointwise exact carrier seed RIGHT" cb b
    let ringType ← phiNativeWholeNoRecovery118 (← inferType ringSeed)
    let some (ringLeftType, ringLeft, ringRightType, ringRight) := ringType.consumeMData.headBeta.heq?
      | throwError "Native130 polynomial Ring129 seed lacks its actual literal HEq4."
    let (actualRingLeft, actualRingRight) ← phiNativeWholePointwiseRingPair129 coefficient right
    phiNativeWholeRawJoin127 "pointwise exact ring seed LEFT" ringLeft actualRingLeft
    phiNativeWholeRawJoin127 "pointwise exact ring seed RIGHT" ringRight actualRingRight
    phiNativeWholeRawJoin127 "pointwise exact ring seed LEFT type" ringLeftType (← inferType actualRingLeft)
    phiNativeWholeRawJoin127 "pointwise exact ring seed RIGHT type" ringRightType (← inferType actualRingRight)
    let carrierHEq ← phiNativeWholeNoRecovery118 (← mkHEqOfEq carrierSeed)
    let reverseCarrier ← phiNativeWholeNoRecovery118 (← mkHEqSymm carrierHEq)
    let reverseRing ← phiNativeWholeNoRecovery118 (← mkHEqSymm ringSeed)
    let (heq, state) ←
      (NativeWholeOriginalMapSeed124Engine.CasselsFullStructural142.structuralHEq
        sourceType target 96 #[] "full142").run
          { pairs := #[(a, b, carrierHEq), (b, a, reverseCarrier),
            (ringLeft, ringRight, ringSeed), (ringRight, ringLeft, reverseRing)] }
    let typeProof ← mkEqOfHEq heq
    let proof ← phiNativeWholeNoRecovery118
      (mkAppN (mkConst ``Eq.mp [Level.zero]) #[sourceType, target, typeProof, source])
    logInfo m!"Native130 exact original point compatibility consumes genuine complete carrier129/Ring129 seeds only: native={state.wrapperLeaves}, proof={state.proofLeaves}, fallback={state.fallbackProofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}. Original derivative/restriction points retained."
    goal.assign proof
    replaceMainGoal []

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholePointwiseMiddleHEq130
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    phi_native_whole_pointwise_points130% 0
      (actualOriginalGlobalPhiNativeWholeLinearCoefficientPoint117 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLinearRightPoint117 p hp P hP s) := by
  phi_native_whole_pointwise_points_seeded130
    (phi_native_whole_pointwise_points130% 1
      (actualOriginalGlobalPhiNativeWholeLinearCoefficientPoint117 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLinearRightPoint117 p hp P hP s)) using
    (actualOriginalGlobalPhiNativeWholePointwiseCarrierEq129 p hp P hP s) and
    (actualOriginalGlobalPhiNativeWholePointwiseRingHEq129 p hp P hP s)


meta section
open Lean Meta Elab Term

elab "phi_native_whole_pointwise_four_link130% " first:term " and " second:term
    " and " middle:term " and " last:term : term => do
  let first ← phiNativeWholeNoRecovery118
    (← Term.elabTerm first none (catchExPostpone := false))
  let second ← phiNativeWholeNoRecovery118
    (← Term.elabTerm second none (catchExPostpone := false))
  let middle ← phiNativeWholeNoRecovery118
    (← Term.elabTerm middle none (catchExPostpone := false))
  let last ← phiNativeWholeNoRecovery118
    (← Term.elabTerm last none (catchExPostpone := false))
  unless first.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholeLinearLeftPoint128 &&
      second.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholeLinearCoefficientPoint117 &&
      middle.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholePointwiseMiddleHEq130 &&
      last.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholeLinearRightPoint117 &&
      first.getAppArgs.size == 8 && second.getAppArgs.size == 8 &&
      middle.getAppArgs.size == 8 && last.getAppArgs.size == 8 do
    throwError "Native130 requires only genuine Left128/Coefficient117/Middle130/Right117 original eight-vectors."
  for component in #[second, middle, last] do
    for i in [:8] do
      phiNativeWholeRawJoin127 s!"pointwise chain original parameter{i}"
        first.getAppArgs[i]! component.getAppArgs[i]!
  let h01 ← phiNativeWholeEqVector128 first
  let h12 ← phiNativeWholeEqVector128 second
  let originalLast ← phiNativeWholeEqVector128 last
  let reverseLast ← phiNativeWholeNoRecovery118
    (mkAppN (mkConst ``Eq.symm originalLast.levels)
      #[originalLast.carrier, originalLast.left, originalLast.right, last])
  let hy ← phiNativeWholeEqualityVector127 reverseLast
  let hp ← phiNativeWholeNoRecovery118 (← inferType middle)
  let some (a, x, b, y) := hp.consumeMData.headBeta.heq?
    | throwError "Native130 middle point certificate lacks its own stored HEq4."
  let .const hn hl := hp.consumeMData.headBeta.getAppFn
    | throwError "Native130 middle HEq lacks its actual universe head."
  unless hn == ``HEq && hl == h01.levels && h01.levels == h12.levels &&
      h01.levels == hy.levels do
    throwError "Native130 actual chain Eq/HEq universe vectors differ."
  phiNativeWholeRawJoin127 "pointwise first/second carrier" h01.carrier h12.carrier
  phiNativeWholeRawJoin127 "pointwise second/middle LEFT carrier" h12.carrier a
  phiNativeWholeRawJoin127 "pointwise middle RIGHT/reversed last carrier" b hy.carrier
  phiNativeWholeRawJoin127 "pointwise first.right/second.left" h01.right h12.left
  phiNativeWholeRawJoin127 "pointwise second.right/middle.left" h12.right x
  phiNativeWholeRawJoin127 "pointwise middle.right/reversed last.left" y hy.left
  let arguments := #[a, b, h01.left, h01.right, h12.right, hy.left, hy.right,
    first, second, middle, reverseLast]
  let sort := mkSort h01.levels[0]!
  let expectedDomains := #[sort, sort, a, a, a, b, b,
    h01.proposition, h12.proposition, hp, hy.proposition]
  let info ← getConstInfo ``phiNativeWholeFourLinkHEq127
  unless info.levelParams.length == h01.levels.length do
    throwError "Native130 passed ordinary four-link127 level count differs."
  let mut lawType := info.instantiateTypeLevelParams h01.levels
  for i in [:11] do
    let .forallE _ domain body _ := lawType
      | throwError "Native130 ordinary pointwise four-link prefix ended at {i}."
    phiNativeWholeRawJoin127 s!"pointwise exact four-link binder{i}" domain expectedDomains[i]!
    lawType := body.instantiate1 arguments[i]!
  let proof ← phiNativeWholeNoRecovery118
    (mkAppN (mkConst ``phiNativeWholeFourLinkHEq127 h01.levels) arguments)
  let actualType ← phiNativeWholeNoRecovery118 (← inferType proof)
  let expectedType := mkAppN (mkConst ``HEq h01.levels)
    #[h01.carrier, h01.left, originalLast.carrier, originalLast.left]
  phiNativeWholeRawJoin127 "pointwise complete original full map endpoints" actualType expectedType
  phiNativeWholeRawJoin127 "pointwise complete own law proposition" actualType lawType
  logInfo m!"Native130 ordinary actual pointwise four-link/11-vector HEq assembly: all original8 parameters, both carrier sides, three genuine point joins, every binder, complete original full-map endpoints/proposition raw unchanged."
  return proof

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholePointwiseAssemblyHEqOwn130
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_whole_pointwise_four_link130%
      (actualOriginalGlobalPhiNativeWholeLinearLeftPoint128 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLinearCoefficientPoint117 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholePointwiseMiddleHEq130 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLinearRightPoint117 p hp P hP s)) :=
    phi_native_whole_pointwise_four_link130%
      (actualOriginalGlobalPhiNativeWholeLinearLeftPoint128 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLinearCoefficientPoint117 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholePointwiseMiddleHEq130 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholeLinearRightPoint117 p hp P hP s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def actualOriginalGlobalPhiNativeWholePointwiseProposition131
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) : Prop :=
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let E2 := (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (hypersurfaceToBase p hp))
          (positiveSheafOfModules (grading I) 2)))
    letI : Module K E2 := Module.compHom E2 (algebraMap K L)
    letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
    letI : Module K ((moduleSpecΓFunctor
        (R := .of ((hypersurface p hp).residueField P.1))).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (toBase (equationIdeal p hp)))
          (positiveSheafOfModules (grading (equationIdeal p hp)) 2)))) :=
      Module.compHom _ (algebraMap K ((hypersurface p hp).residueField P.1))
    letI : IsScalarTower K ((hypersurface p hp).residueField P.1)
      ((moduleSpecΓFunctor
        (R := .of ((hypersurface p hp).residueField P.1))).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (toBase (equationIdeal p hp)))
          (positiveSheafOfModules (grading (equationIdeal p hp)) 2)))) :=
      IsScalarTower.of_compHom K ((hypersurface p hp).residueField P.1) _
    (((actualOriginalPositiveTwoContractedNativeDifferentialMap p hp P hP).restrictScalars K).comp
      (actualOriginalGlobalCanonicalQuadraticPhiLinearMap p hp P)) s =
    ((actualResidueDifferentialDerivation (K := K) (R := R) (L := L)).toLinearMap.comp
      (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP)) s


meta section
open Lean Meta Elab Tactic Term

private def phiNativeWholePointwiseFactory131 (factory : Expr) :
    TermElabM (Expr × Expr × Expr × List Level) := do
  let factory ← phiNativeWholeNoRecovery118 factory
  unless factory.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholePointwiseProposition131 &&
      factory.getAppArgs.size == 8 do
    throwError "Native131 requires only exact original pointwise factory131 eight-vector."
  let proposition ← phiNativeWholeNoRecovery118 (← whnf factory)
  let some (a, x, y) := proposition.consumeMData.headBeta.eq?
    | throwError "Native131 original pointwise factory body is not its literal Eq3."
  let .const name levels := proposition.consumeMData.headBeta.getAppFn
    | throwError "Native131 original pointwise factory Eq lacks its actual universe vector."
  unless name == ``Eq && levels.length == 1 do
    throwError "Native131 original pointwise factory singleton Eq universe differs."
  return (a, x, y, levels)

elab "phi_native_whole_pointwise_factory_heq131% " factory:term : term => do
  let (a, x, y, levels) ← phiNativeWholePointwiseFactory131
    (← Term.elabTerm factory none (catchExPostpone := false))
  return ← phiNativeWholeNoRecovery118 (mkAppN (mkConst ``HEq levels) #[a, x, a, y])


private def phiNativeWholePointwiseLeftPair132 (source factory : Expr) :
    TermElabM (Expr × Expr × Expr × Expr × List Level) := do
  let source ← phiNativeWholeNoRecovery118 source
  let factory ← phiNativeWholeNoRecovery118 factory
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholePointwiseAssemblyHEqOwn130 &&
      factory.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholePointwiseProposition131 &&
      source.getAppArgs.size == 8 && factory.getAppArgs.size == 8 do
    throwError "Native132 requires exact actual own130/factory131 original eight-vectors."
  for i in [:8] do
    phiNativeWholeRawJoin127 s!"pointwise LEFT bridge original parameter{i}"
      source.getAppArgs[i]! factory.getAppArgs[i]!
  let sourceType ← phiNativeWholeNoRecovery118 (← inferType source)
  let some (sourceA, sourceLeft, _, _) := sourceType.consumeMData.headBeta.heq?
    | throwError "Native132 original own130 lacks its stored literal HEq4."
  let .const name levels := sourceType.consumeMData.headBeta.getAppFn
    | throwError "Native132 original own130 lacks its exact universe head."
  let (factoryA, factoryLeft, _, factoryLevels) ← phiNativeWholePointwiseFactory131 factory
  unless name == ``HEq && levels.length == 1 && levels == factoryLevels do
    throwError "Native132 original own/factory point universe vectors differ."
  let sort := mkSort levels[0]!
  phiNativeWholeRawJoin127 "pointwise LEFT source carrier sort" (← inferType sourceA) sort
  phiNativeWholeRawJoin127 "pointwise LEFT factory carrier sort" (← inferType factoryA) sort
  return (sourceA, sourceLeft, factoryA, factoryLeft, levels)

elab "phi_native_whole_pointwise_left132% " mode:num source:term " and " factory:term : term => do
  unless mode.getNat < 4 do
    throwError "Native132 requires complete type Eq0/type reflexivity1/original point HEq2/point reflexivity3."
  let (a, x, b, y, levels) ← phiNativeWholePointwiseLeftPair132
    (← Term.elabTerm source none (catchExPostpone := false))
    (← Term.elabTerm factory none (catchExPostpone := false))
  let sort := mkSort levels[0]!
  let typeLevels := [Level.succ levels[0]!]
  if mode.getNat == 0 then
    return ← phiNativeWholeNoRecovery118 (mkAppN (mkConst ``Eq typeLevels) #[sort, a, b])
  if mode.getNat == 1 then
    let proof ← phiNativeWholeNoRecovery118 (mkAppN (mkConst ``Eq.refl typeLevels) #[sort, a])
    phiNativeWholeRawJoin127 "pointwise LEFT exact whole carrier reflexivity"
      (← inferType proof) (mkAppN (mkConst ``Eq typeLevels) #[sort, a, a])
    return proof
  if mode.getNat == 2 then
    return ← phiNativeWholeNoRecovery118 (mkAppN (mkConst ``HEq levels) #[a, x, b, y])
  let proof ← phiNativeWholeNoRecovery118 (mkAppN (mkConst ``HEq.refl levels) #[a, x])
  phiNativeWholeRawJoin127 "pointwise LEFT exact original point reflexivity"
    (← inferType proof) (mkAppN (mkConst ``HEq levels) #[a, x, a, x])
  return proof

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholePointwiseLeftCarrierEq132
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    phi_native_whole_pointwise_left132% 0
      (actualOriginalGlobalPhiNativeWholePointwiseAssemblyHEqOwn130 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholePointwiseProposition131 p hp P hP s) := by
  basis_full_exact142
    (phi_native_whole_pointwise_left132% 1
      (actualOriginalGlobalPhiNativeWholePointwiseAssemblyHEqOwn130 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholePointwiseProposition131 p hp P hP s))


meta section
open Lean Meta Elab Tactic Term

elab "phi_native_whole_pointwise_left_seeded132 " supplied:term " using " suppliedSeed:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← phiNativeWholeNoRecovery118
      (← Term.elabTerm supplied none (catchExPostpone := false))
    let seed ← phiNativeWholeNoRecovery118
      (← Term.elabTerm suppliedSeed none (catchExPostpone := false))
    unless seed.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholePointwiseLeftCarrierEq132 &&
        seed.getAppArgs.size == 8 do
      throwError "Native132 requires genuine complete original LEFT-carrier132 eight-vector certificate."
    let arguments := seed.getAppArgs
    let levels := seed.getAppFn.constLevels!
    let own := mkAppN
      (mkConst ``actualOriginalGlobalPhiNativeWholePointwiseAssemblyHEqOwn130 levels) arguments
    let factory := mkAppN
      (mkConst ``actualOriginalGlobalPhiNativeWholePointwiseProposition131 levels) arguments
    let (a, x, b, y, pointLevels) ← phiNativeWholePointwiseLeftPair132 own factory
    let target ← phiNativeWholeNoRecovery118 (← goal.getType)
    let expectedTarget := mkAppN (mkConst ``HEq pointLevels) #[a, x, b, y]
    phiNativeWholeRawJoin127 "pointwise LEFT exact entire original point target" target expectedTarget
    let sourceType ← phiNativeWholeNoRecovery118 (← inferType source)
    phiNativeWholeRawJoin127 "pointwise LEFT exact original source point"
      sourceType (mkAppN (mkConst ``HEq pointLevels) #[a, x, a, x])
    let seedType ← phiNativeWholeNoRecovery118 (← inferType seed)
    let some (_, seedA, seedB) := seedType.consumeMData.headBeta.eq?
      | throwError "Native132 whole LEFT-carrier certificate lacks its own stored Eq3."
    phiNativeWholeRawJoin127 "pointwise LEFT exact type seed SOURCE" seedA a
    phiNativeWholeRawJoin127 "pointwise LEFT exact type seed FACTORY" seedB b
    let typeHEq ← phiNativeWholeNoRecovery118 (← mkHEqOfEq seed)
    let reverseType ← phiNativeWholeNoRecovery118 (← mkHEqSymm typeHEq)
    let (heq, state) ←
      (NativeWholeOriginalMapSeed124Engine.CasselsFullStructural142.structuralHEq
        sourceType target 96 #[] "full142").run
          { pairs := #[(a, b, typeHEq), (b, a, reverseType)] }
    let typeProof ← mkEqOfHEq heq
    let proof ← phiNativeWholeNoRecovery118
      (mkAppN (mkConst ``Eq.mp [Level.zero]) #[sourceType, target, typeProof, source])
    logInfo m!"Native132 exact original LEFT full-map point compatibility uses genuine COMPLETE LeftCarrier132 equality only: native={state.wrapperLeaves}, proof={state.proofLeaves}, fallback={state.fallbackProofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}. Original whole carrier and point values retained."
    goal.assign proof
    replaceMainGoal []

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholePointwiseLeftPointHEq132
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    phi_native_whole_pointwise_left132% 2
      (actualOriginalGlobalPhiNativeWholePointwiseAssemblyHEqOwn130 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholePointwiseProposition131 p hp P hP s) := by
  phi_native_whole_pointwise_left_seeded132
    (phi_native_whole_pointwise_left132% 3
      (actualOriginalGlobalPhiNativeWholePointwiseAssemblyHEqOwn130 p hp P hP s)
      and (actualOriginalGlobalPhiNativeWholePointwiseProposition131 p hp P hP s)) using
    (actualOriginalGlobalPhiNativeWholePointwiseLeftCarrierEq132 p hp P hP s)


universe wNativeWhole133
private theorem phiNativeWholeTypeJoin133 {S : Sort wNativeWhole133}
    (a b f : S) (hab : a = b) (haf : a = f) : b = f := hab.symm.trans haf

meta section
open Lean Meta Elab Term

elab "phi_native_whole_pointwise_right_type133% " ab:term " and " af:term : term => do
  let ab ← phiNativeWholeNoRecovery118 (← Term.elabTerm ab none (catchExPostpone := false))
  let af ← phiNativeWholeNoRecovery118 (← Term.elabTerm af none (catchExPostpone := false))
  unless ab.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholePointwiseCarrierEq129 &&
      af.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholePointwiseLeftCarrierEq132 &&
      ab.getAppArgs.size == 8 && af.getAppArgs.size == 8 do
    throwError "Native133 requires only genuine complete Carrier129/LeftCarrier132 eight-vectors."
  for i in [:8] do
    phiNativeWholeRawJoin127 s!"right type original parameter{i}" ab.getAppArgs[i]! af.getAppArgs[i]!
  let hab ← phiNativeWholeEqualityVector127 ab
  let haf ← phiNativeWholeEqualityVector127 af
  unless hab.levels == haf.levels do
    throwError "Native133 complete type equality universe vectors differ."
  phiNativeWholeRawJoin127 "right type equality shared carrier SORT" hab.carrier haf.carrier
  phiNativeWholeRawJoin127 "right type equality shared original LEFT carrier" hab.left haf.left
  let arguments := #[hab.carrier, hab.left, hab.right, haf.right, ab, af]
  let expectedDomains := #[mkSort hab.levels[0]!, hab.carrier, hab.carrier, hab.carrier,
    hab.proposition, haf.proposition]
  let info ← getConstInfo ``phiNativeWholeTypeJoin133
  unless info.levelParams.length == hab.levels.length do
    throwError "Native133 tiny original type-join universe count differs."
  let mut lawType := info.instantiateTypeLevelParams hab.levels
  for i in [:6] do
    let .forallE _ domain body _ := lawType
      | throwError "Native133 ordinary type join prefix ended at {i}."
    phiNativeWholeRawJoin127 s!"right type exact binder{i}" domain expectedDomains[i]!
    lawType := body.instantiate1 arguments[i]!
  let proof ← phiNativeWholeNoRecovery118
    (mkAppN (mkConst ``phiNativeWholeTypeJoin133 hab.levels) arguments)
  let actualType ← phiNativeWholeNoRecovery118 (← inferType proof)
  let expectedType := mkAppN (mkConst ``Eq hab.levels) #[hab.carrier, hab.right, haf.right]
  phiNativeWholeRawJoin127 "right type entire original endpoint equality" actualType expectedType
  phiNativeWholeRawJoin127 "right type entire own law" actualType lawType
  logInfo m!"Native133 genuine complete RIGHT-to-factory type identity via exact129/132 six-vector ordinary equality join; all original parameters/common LEFT/sorts/binders/endpoints raw unchanged."
  return proof

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholePointwiseRightCarrierEqOwn133
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_whole_pointwise_right_type133%
      (actualOriginalGlobalPhiNativeWholePointwiseCarrierEq129 p hp P hP s) and
      (actualOriginalGlobalPhiNativeWholePointwiseLeftCarrierEq132 p hp P hP s)) :=
    phi_native_whole_pointwise_right_type133%
      (actualOriginalGlobalPhiNativeWholePointwiseCarrierEq129 p hp P hP s) and
      (actualOriginalGlobalPhiNativeWholePointwiseLeftCarrierEq132 p hp P hP s)


meta section
open Lean Meta Elab Tactic Term

private def phiNativeWholePointwiseRightPair133 (own factory : Expr) :
    TermElabM (Expr × Expr × Expr × Expr × List Level) := do
  let own ← phiNativeWholeNoRecovery118 own
  let factory ← phiNativeWholeNoRecovery118 factory
  -- Retain all passed132 own/factory parameter/universe/sort checks.
  let _ ← phiNativeWholePointwiseLeftPair132 own factory
  let proposition ← phiNativeWholeNoRecovery118 (← inferType own)
  let some (_, _, b, y) := proposition.consumeMData.headBeta.heq?
    | throwError "Native133 original own130 lacks its complete HEq4."
  let .const _ levels := proposition.consumeMData.headBeta.getAppFn
    | throwError "Native133 actual own130 universe head missing."
  let (f, _, z, fl) ← phiNativeWholePointwiseFactory131 factory
  unless levels == fl do
    throwError "Native133 actual RIGHT/factory point universes differ."
  return (b, y, f, z, levels)

elab "phi_native_whole_pointwise_right133% " mode:num own:term " and " factory:term : term => do
  unless mode.getNat < 2 do
    throwError "Native133 requires original RIGHT point HEq0/source reflexivity1."
  let (b, y, f, z, levels) ← phiNativeWholePointwiseRightPair133
    (← Term.elabTerm own none (catchExPostpone := false))
    (← Term.elabTerm factory none (catchExPostpone := false))
  if mode.getNat == 0 then
    return ← phiNativeWholeNoRecovery118 (mkAppN (mkConst ``HEq levels) #[b, y, f, z])
  let proof ← phiNativeWholeNoRecovery118 (mkAppN (mkConst ``HEq.refl levels) #[b, y])
  phiNativeWholeRawJoin127 "right point exact source reflexivity"
    (← inferType proof) (mkAppN (mkConst ``HEq levels) #[b, y, b, y])
  return proof

elab "phi_native_whole_pointwise_right_seeded133 " supplied:term " using " typeSeed:term
    " and " ringSeed:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← phiNativeWholeNoRecovery118 (← Term.elabTerm supplied none (catchExPostpone := false))
    let typeSeed ← phiNativeWholeNoRecovery118 (← Term.elabTerm typeSeed none (catchExPostpone := false))
    let ringSeed ← phiNativeWholeNoRecovery118 (← Term.elabTerm ringSeed none (catchExPostpone := false))
    unless typeSeed.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholePointwiseRightCarrierEqOwn133 &&
        ringSeed.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholePointwiseRingHEq129 &&
        typeSeed.getAppArgs.size == 8 && ringSeed.getAppArgs.size == 8 do
      throwError "Native133 requires only genuine RightType133/Ring129 original eight-vectors."
    let arguments := typeSeed.getAppArgs
    for i in [:8] do
      phiNativeWholeRawJoin127 s!"right point seed original parameter{i}" arguments[i]! ringSeed.getAppArgs[i]!
    let levels := typeSeed.getAppFn.constLevels!
    let own := mkAppN (mkConst ``actualOriginalGlobalPhiNativeWholePointwiseAssemblyHEqOwn130 levels) arguments
    let factory := mkAppN (mkConst ``actualOriginalGlobalPhiNativeWholePointwiseProposition131 levels) arguments
    let (b, y, f, z, pl) ← phiNativeWholePointwiseRightPair133 own factory
    let target ← phiNativeWholeNoRecovery118 (← goal.getType)
    phiNativeWholeRawJoin127 "right point complete original target" target (mkAppN (mkConst ``HEq pl) #[b, y, f, z])
    let sourceType ← phiNativeWholeNoRecovery118 (← inferType source)
    phiNativeWholeRawJoin127 "right point complete original source" sourceType (mkAppN (mkConst ``HEq pl) #[b, y, b, y])
    let tt ← phiNativeWholeNoRecovery118 (← inferType typeSeed)
    let some (_, tb, tf) := tt.consumeMData.headBeta.eq?
      | throwError "Native133 complete RIGHT type seed lacks original Eq3."
    phiNativeWholeRawJoin127 "right point type seed original RIGHT carrier" tb b
    phiNativeWholeRawJoin127 "right point type seed original FACTORY carrier" tf f
    let rt ← phiNativeWholeNoRecovery118 (← inferType ringSeed)
    let some (lt, l, qt, q) := rt.consumeMData.headBeta.heq?
      | throwError "Native133 original Ring129 seed lacks HEq4."
    let coefficient := mkAppN (mkConst ``actualOriginalGlobalPhiNativeWholeLinearCoefficientPoint117 levels) arguments
    let right := mkAppN (mkConst ``actualOriginalGlobalPhiNativeWholeLinearRightPoint117 levels) arguments
    let (actualL, actualQ) ← phiNativeWholePointwiseRingPair129 coefficient right
    phiNativeWholeRawJoin127 "right point exact polynomial ring LEFT" l actualL
    phiNativeWholeRawJoin127 "right point exact polynomial ring RIGHT" q actualQ
    phiNativeWholeRawJoin127 "right point exact polynomial ring LEFT type" lt (← inferType actualL)
    phiNativeWholeRawJoin127 "right point exact polynomial ring RIGHT type" qt (← inferType actualQ)
    let th ← phiNativeWholeNoRecovery118 (← mkHEqOfEq typeSeed)
    let tr ← phiNativeWholeNoRecovery118 (← mkHEqSymm th)
    let rr ← phiNativeWholeNoRecovery118 (← mkHEqSymm ringSeed)
    let (heq, state) ←
      (NativeWholeOriginalMapSeed124Engine.CasselsFullStructural142.structuralHEq
        sourceType target 96 #[] "full142").run
          { pairs := #[(b, f, th), (f, b, tr), (l, q, ringSeed), (q, l, rr)] }
    let typeProof ← mkEqOfHEq heq
    let proof ← phiNativeWholeNoRecovery118
      (mkAppN (mkConst ``Eq.mp [Level.zero]) #[sourceType, target, typeProof, source])
    logInfo m!"Native133 exact original RIGHT full-map point compatibility: native={state.wrapperLeaves}, proof={state.proofLeaves}, fallback={state.fallbackProofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}. Only genuine complete RightType133/Ring129 seeds, original literal points unchanged."
    goal.assign proof
    replaceMainGoal []

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholePointwiseRightPointHEq133
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    phi_native_whole_pointwise_right133% 0
      (actualOriginalGlobalPhiNativeWholePointwiseAssemblyHEqOwn130 p hp P hP s) and
      (actualOriginalGlobalPhiNativeWholePointwiseProposition131 p hp P hP s) := by
  phi_native_whole_pointwise_right_seeded133
    (phi_native_whole_pointwise_right133% 1
      (actualOriginalGlobalPhiNativeWholePointwiseAssemblyHEqOwn130 p hp P hP s) and
      (actualOriginalGlobalPhiNativeWholePointwiseProposition131 p hp P hP s)) using
    (actualOriginalGlobalPhiNativeWholePointwiseRightCarrierEqOwn133 p hp P hP s) and
    (actualOriginalGlobalPhiNativeWholePointwiseRingHEq129 p hp P hP s)


private theorem phiNativeWholeFinalHEqJoin133 {A B F : Sort wNativeWhole133}
    (a : A) (b : B) (l r : F)
    (left : HEq a l) (own : HEq a b) (right : HEq b r) : HEq l r :=
  left.symm.trans (own.trans right)

meta section
open Lean Meta Elab Term

elab "phi_native_whole_final_heq133% " left:term " and " own:term " and " right:term : term => do
  let left ← phiNativeWholeNoRecovery118 (← Term.elabTerm left none (catchExPostpone := false))
  let own ← phiNativeWholeNoRecovery118 (← Term.elabTerm own none (catchExPostpone := false))
  let right ← phiNativeWholeNoRecovery118 (← Term.elabTerm right none (catchExPostpone := false))
  unless left.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholePointwiseLeftPointHEq132 &&
      own.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholePointwiseAssemblyHEqOwn130 &&
      right.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholePointwiseRightPointHEq133 &&
      left.getAppArgs.size == 8 && own.getAppArgs.size == 8 && right.getAppArgs.size == 8 do
    throwError "Native133 requires only exact LeftPoint132/own130/RightPoint133 eight-vectors."
  for component in #[left, right] do
    for i in [:8] do
      phiNativeWholeRawJoin127 s!"final original parameter{i}" own.getAppArgs[i]! component.getAppArgs[i]!
  let lp ← phiNativeWholeNoRecovery118 (← inferType left)
  let op ← phiNativeWholeNoRecovery118 (← inferType own)
  let rp ← phiNativeWholeNoRecovery118 (← inferType right)
  let some (la, lx, lf, ll) := lp.consumeMData.headBeta.heq?
    | throwError "Native133 exact LEFT certificate lacks HEq4."
  let some (a, x, b, y) := op.consumeMData.headBeta.heq?
    | throwError "Native133 exact OWN certificate lacks HEq4."
  let some (rb, ry, rf, rr) := rp.consumeMData.headBeta.heq?
    | throwError "Native133 exact RIGHT certificate lacks HEq4."
  phiNativeWholeRawJoin127 "final original LEFT carrier" la a
  phiNativeWholeRawJoin127 "final original LEFT point" lx x
  phiNativeWholeRawJoin127 "final original RIGHT carrier" rb b
  phiNativeWholeRawJoin127 "final original RIGHT point" ry y
  phiNativeWholeRawJoin127 "final same original FACTORY carrier" lf rf
  let .const name levels := op.consumeMData.headBeta.getAppFn
    | throwError "Native133 original own HEq lacks universe head."
  unless name == ``HEq && levels.length == 1 &&
      lp.consumeMData.headBeta.getAppFn.constLevels! == levels &&
      rp.consumeMData.headBeta.getAppFn.constLevels! == levels do
    throwError "Native133 exact final HEq universe vectors differ."
  let arguments := #[a, b, lf, x, y, ll, rr, left, own, right]
  let sort := mkSort levels[0]!
  let expectedDomains := #[sort, sort, sort, a, b, lf, lf, lp, op, rp]
  let info ← getConstInfo ``phiNativeWholeFinalHEqJoin133
  unless info.levelParams.length == levels.length do
    throwError "Native133 ordinary final endpoint join universe count differs."
  let mut lawType := info.instantiateTypeLevelParams levels
  for i in [:10] do
    let .forallE _ domain body _ := lawType
      | throwError "Native133 final ordinary endpoint join prefix ended at {i}."
    phiNativeWholeRawJoin127 s!"final exact endpoint binder{i}" domain expectedDomains[i]!
    lawType := body.instantiate1 arguments[i]!
  let proof ← phiNativeWholeNoRecovery118 (mkAppN (mkConst ``phiNativeWholeFinalHEqJoin133 levels) arguments)
  let actualType ← phiNativeWholeNoRecovery118 (← inferType proof)
  let factory := mkAppN (mkConst ``actualOriginalGlobalPhiNativeWholePointwiseProposition131 own.getAppFn.constLevels!) own.getAppArgs
  let (f, fl, fr, factoryLevels) ← phiNativeWholePointwiseFactory131 factory
  unless factoryLevels == levels do
    throwError "Native133 exact original factory point universes differ."
  phiNativeWholeRawJoin127 "final original factory carrier" lf f
  phiNativeWholeRawJoin127 "final original factory LEFT endpoint" ll fl
  phiNativeWholeRawJoin127 "final original factory RIGHT endpoint" rr fr
  let expectedType := mkAppN (mkConst ``HEq levels) #[f, fl, f, fr]
  phiNativeWholeRawJoin127 "final entire literal original factory HEq" actualType expectedType
  phiNativeWholeRawJoin127 "final entire own endpoint law" actualType lawType
  logInfo m!"Native133 final same-carrier literal original pointwise HEq via exact10-vector ordinary endpoint join; all original8 parameters/carriers/points/binders/full factory proposition raw unchanged. No geometric checker aggregation."
  return proof

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholePointwiseLiteralHEq133
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_whole_final_heq133%
      (actualOriginalGlobalPhiNativeWholePointwiseLeftPointHEq132 p hp P hP s) and
      (actualOriginalGlobalPhiNativeWholePointwiseAssemblyHEqOwn130 p hp P hP s) and
      (actualOriginalGlobalPhiNativeWholePointwiseRightPointHEq133 p hp P hP s)) :=
    phi_native_whole_final_heq133%
      (actualOriginalGlobalPhiNativeWholePointwiseLeftPointHEq132 p hp P hP s) and
      (actualOriginalGlobalPhiNativeWholePointwiseAssemblyHEqOwn130 p hp P hP s) and
      (actualOriginalGlobalPhiNativeWholePointwiseRightPointHEq133 p hp P hP s)

meta section
open Lean Meta Elab Term

elab "phi_native_whole_pointwise_literal_eq133% " supplied:term : term => do
  let proof ← phiNativeWholeNoRecovery118
    (← Term.elabTerm supplied none (catchExPostpone := false))
  unless proof.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeWholePointwiseLiteralHEq133 &&
      proof.getAppArgs.size == 8 do
    throwError "Native133 requires the original literal HEq128 eight-vector."
  let proposition ← phiNativeWholeNoRecovery118 (← inferType proof)
  let some (a, x, b, y) := proposition.consumeMData.headBeta.heq?
    | throwError "Native133 literal certificate lacks its stored HEq4."
  phiNativeWholeRawJoin127 "literal homogeneous LEFT/RIGHT carrier" a b
  let .const name levels := proposition.consumeMData.headBeta.getAppFn
    | throwError "Native133 literal HEq lacks its universe head."
  unless name == ``HEq && levels.length == 1 do
    throwError "Native133 literal HEq singleton universe differs."
  let info ← getConstInfo ``eq_of_heq
  unless info.levelParams.length == levels.length do
    throwError "Native133 eq_of_heq universe count differs."
  let arguments := #[a, x, y, proof]
  let expectedDomains := #[mkSort levels[0]!, a, a, proposition]
  let mut lawType := info.instantiateTypeLevelParams levels
  for i in [:4] do
    let .forallE _ domain body _ := lawType
      | throwError "Native133 ordinary eq_of_heq prefix ended at {i}."
    phiNativeWholeRawJoin127 s!"literal eq_of_heq exact binder{i}" domain expectedDomains[i]!
    lawType := body.instantiate1 arguments[i]!
  let result ← phiNativeWholeNoRecovery118
    (mkAppN (mkConst ``eq_of_heq levels) arguments)
  let actualType ← phiNativeWholeNoRecovery118 (← inferType result)
  let expectedType := mkAppN (mkConst ``Eq levels) #[a, x, y]
  phiNativeWholeRawJoin127 "literal whole Eq exact endpoint/type" actualType expectedType
  phiNativeWholeRawJoin127 "literal whole Eq law proposition" actualType lawType
  logInfo m!"Native133 ordinary eq_of_heq uses all four exact stored vectors; both carriers and complete factory endpoints raw unchanged."
  return result

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholePointwiseLiteralEqOwn133
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_whole_pointwise_literal_eq133%
      (actualOriginalGlobalPhiNativeWholePointwiseLiteralHEq133 p hp P hP s)) :=
    phi_native_whole_pointwise_literal_eq133%
      (actualOriginalGlobalPhiNativeWholePointwiseLiteralHEq133 p hp P hP s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma actualOriginalGlobalPhiNativeWholeLinearPointwise133
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let E2 := (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (hypersurfaceToBase p hp))
          (positiveSheafOfModules (grading I) 2)))
    letI : Module K E2 := Module.compHom E2 (algebraMap K L)
    letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
    letI : Module K ((moduleSpecΓFunctor
        (R := .of ((hypersurface p hp).residueField P.1))).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (toBase (equationIdeal p hp)))
          (positiveSheafOfModules (grading (equationIdeal p hp)) 2)))) :=
      Module.compHom _ (algebraMap K ((hypersurface p hp).residueField P.1))
    letI : IsScalarTower K ((hypersurface p hp).residueField P.1)
      ((moduleSpecΓFunctor
        (R := .of ((hypersurface p hp).residueField P.1))).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (toBase (equationIdeal p hp)))
          (positiveSheafOfModules (grading (equationIdeal p hp)) 2)))) :=
      IsScalarTower.of_compHom K ((hypersurface p hp).residueField P.1) _
    (((actualOriginalPositiveTwoContractedNativeDifferentialMap p hp P hP).restrictScalars K).comp
      (actualOriginalGlobalCanonicalQuadraticPhiLinearMap p hp P)) s =
    ((actualResidueDifferentialDerivation (K := K) (R := R) (L := L)).toLinearMap.comp
      (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP)) s := by
  intro C I R L E2
  basis_full_exact142 (actualOriginalGlobalPhiNativeWholePointwiseLiteralEqOwn133 p hp P hP s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma actualOriginalGlobalCanonicalQuadraticPhi_native_contracted_linearMap
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let E2 := (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (hypersurfaceToBase p hp))
          (positiveSheafOfModules (grading I) 2)))
    letI : Module K E2 := Module.compHom E2 (algebraMap K L)
    letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
    letI : Module K ((moduleSpecΓFunctor
        (R := .of ((hypersurface p hp).residueField P.1))).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (toBase (equationIdeal p hp)))
          (positiveSheafOfModules (grading (equationIdeal p hp)) 2)))) :=
      Module.compHom _ (algebraMap K ((hypersurface p hp).residueField P.1))
    letI : IsScalarTower K ((hypersurface p hp).residueField P.1)
      ((moduleSpecΓFunctor
        (R := .of ((hypersurface p hp).residueField P.1))).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (toBase (equationIdeal p hp)))
          (positiveSheafOfModules (grading (equationIdeal p hp)) 2)))) :=
      IsScalarTower.of_compHom K ((hypersurface p hp).residueField P.1) _
    ((actualOriginalPositiveTwoContractedNativeDifferentialMap p hp P hP).restrictScalars K).comp
      (actualOriginalGlobalCanonicalQuadraticPhiLinearMap p hp P) =
    (actualResidueDifferentialDerivation (K := K) (R := R) (L := L)).toLinearMap.comp
      (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP) := by
  intro C I R L E2
  apply DFunLike.ext
  intro s
  exact actualOriginalGlobalPhiNativeWholeLinearPointwise133 p hp P hP s

end PfaffianDescent
