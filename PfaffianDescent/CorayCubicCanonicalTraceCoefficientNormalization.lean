import PfaffianDescent.CorayCubicCanonicalTraceNativeAdditiveEndpoints
import Lean.Elab.Command

/-! Original-K linearity of the SAME selected-component residue trace.
No duality/perfectness/genus assertion. SOURCE ONLY / UNVERIFIED.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian MvPolynomial TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra


meta section
open Lean Meta Elab Term

private def residueNoRecovery147 (e : Expr) : TermElabM Expr := do
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
    throwError "RESIDUE147 refused unresolved/recovery expression."
  return e

/-- Substitute at most16 actual outer statement lets; no definition unfolding. -/
private def residueOuterLets147 (e : Expr) : TermElabM Expr := do
  let mut e := e.consumeMData
  for _ in [:16] do
    match e with
    | .letE _ _ val body _ => e := (body.instantiate1 val).consumeMData
    | _ => break
  if e.isLet then throwError "RESIDUE147 outer statement-let bound16 exceeded."
  return e

private def residueProof147 (stx : Syntax) : TermElabM Expr := do
  residueNoRecovery147 (← elabTerm stx none (catchExPostpone := false))

/-- Read original exact endpoint proofs and assemble on THEIR SAME carrier.
No native arrow reconstruction, expected target, type conversion, or map unfolding. -/
elab "residue_own_additive_trans147% " first:term " then " second:term : term => do
  let first ← residueProof147 first
  let second ← residueProof147 second
  let p ← residueOuterLets147 (← inferType first)
  let q ← residueOuterLets147 (← inferType second)
  let some (pc, pl, pm) := p.eq?
    | throwError "RESIDUE147 first endpoint not an actual stored Eq."
  let some (qc, qm, qr) := q.eq?
    | throwError "RESIDUE147 second endpoint not an actual stored Eq."
  unless pc.equal qc && pm.equal qm do
    throwError "RESIDUE147 refused changed stored carrier or middle endpoint."
  let .const _ ls := p.getAppFn
    | throwError "RESIDUE147 first Eq universe vector missing."
  let proof ← residueNoRecovery147
    (mkAppN (mkConst ``Eq.trans ls) #[pc, pl, pm, qr, first, second])
  logInfo "RESIDUE147 own-trans exact carrier/middle RAW guards passed; ordinary Eq.trans emitted."
  return proof

end

/-- Ordinary composition of the SAME original additive endpoints on their own stored carrier. -/
private theorem cubicNativeStoredAdditiveComposition147
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules]
    [hExt : HasExt.{u} (hypersurface p hp).Modules] :
    type_of% (residue_own_additive_trans147% (@cubicNativeCanonicalTraceLinearMap_projection_toAddMonoidHom K
      (inferInstance : Field K) p hp hp0
      (inferInstance : IsDomain (CoordinateRing (equationIdeal p hp)))
      ‹HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules› hExt) then (@cubicNativeCanonicalTraceEquiv_toAddMonoidHom K
      (inferInstance : Field K) p hp hp0
      (inferInstance : IsDomain (CoordinateRing (equationIdeal p hp)))
      ‹HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules› hExt)) :=
  residue_own_additive_trans147% (@cubicNativeCanonicalTraceLinearMap_projection_toAddMonoidHom K
      (inferInstance : Field K) p hp hp0
      (inferInstance : IsDomain (CoordinateRing (equationIdeal p hp)))
      ‹HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules› hExt) then (@cubicNativeCanonicalTraceEquiv_toAddMonoidHom K
      (inferInstance : Field K) p hp hp0
      (inferInstance : IsDomain (CoordinateRing (equationIdeal p hp)))
      ‹HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules› hExt)

/-- EXACT original literal coefficient statement, folded solely for a bounded type bridge. -/
private def residueNativeLiteralProposition147
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules]
    [hExt : HasExt.{u} (hypersurface p hp).Modules] : Prop :=
    let X : Scheme.{u} := Proj (grading (equationIdeal p hp))
    let W : X.Modules := sheafOfModules (grading (equationIdeal p hp)) 1
    letI : HasExt.{u} X.Modules := hExt
    letI : Linear K X.Modules := schemeModulesLinearOver (hypersurfaceToBase p hp)
    letI : AddCommGroup (schemeModuleCohomology X W 2) := Ext.instAddCommGroup
    letI : Module K (schemeModuleCohomology X W 2) := Ext.instModule
    (cubicNativeCanonicalTraceLinearMap p hp hp0).toAddMonoidHom =
      (cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0).toAddMonoidHom


meta section
open Lean Meta Elab Term

private def residueRawHead147 (e : Expr) : String :=
  let e := e.consumeMData
  match e.getAppFn with
  | .const nm ls => s!"{nm};levels={reprStr ls};args={e.getAppArgs.size}"
  | .lam n _ _ bi => s!"lambda({n};{reprStr bi})"
  | .forallE n _ _ bi => s!"forall({n};{reprStr bi})"
  | .letE n _ _ _ nd => s!"let({n};nondep={nd})"
  | .fvar id => s!"fvar({id.name})"
  | .bvar i => s!"bvar({i})"
  | .mvar id => s!"mvar({id.name})"
  | .proj n i _ => s!"projection({n};{i})"
  | .lit val => s!"literal({reprStr val})"
  | .sort ls => s!"sort({ls})"
  | _ => "nonconstant"

private def residueLiteralVector147 (proof literal : Expr) : TermElabM (Expr × Expr × Expr) := do
  let proof ← residueNoRecovery147 proof
  let literal ← residueNoRecovery147 literal
  let p ← residueOuterLets147 (← inferType proof)
  let .const nm ls := literal.getAppFn
    | throwError "RESIDUE147 expected folded literal proposition application."
  unless nm == ``residueNativeLiteralProposition147 do
    throwError "RESIDUE147 refused different literal proposition."
  let .defnInfo info ← getConstInfo nm
    | throwError "RESIDUE147 literal proposition has no definition metadata."
  unless info.levelParams.length == ls.length do
    throwError "RESIDUE147 literal proposition universe count mismatch."
  let q ← residueOuterLets147
    ((info.value.instantiateLevelParams info.levelParams ls).beta literal.getAppArgs)
  return (p, q, literal)


/-- Exact bounded raw mismatch walk: at most12 differing nodes total, at most16
application arguments per node. No normalization/conversion. -/
private partial def residueRawDiff148 (label : String) (left right : Expr)
    (budget : Nat) : TermElabM Nat := do
  let left := left.consumeMData
  let right := right.consumeMData
  if budget == 0 || left.equal right then return budget
  logInfo m!"RESIDUE148 DIFF {label} left={residueRawHead147 left} right={residueRawHead147 right}"
  let mut remaining := budget - 1
  match left, right with
  | .app _ _, .app _ _ =>
    remaining ← residueRawDiff148 (label ++ ".head") left.getAppFn right.getAppFn remaining
    let la := left.getAppArgs
    let ra := right.getAppArgs
    logInfo m!"RESIDUE148 DIFF {label} argCounts={la.size}/{ra.size}"
    for i in [:min (min la.size ra.size) 16] do
      if remaining == 0 then break
      remaining ← residueRawDiff148 (label ++ s!".arg[{i}]") la[i]! ra[i]! remaining
  | .forallE _ lt lb lbi, .forallE _ rt rb rbi
  | .lam _ lt lb lbi, .lam _ rt rb rbi =>
    logInfo m!"RESIDUE148 DIFF {label} binderInfoSame={lbi == rbi}"
    remaining ← residueRawDiff148 (label ++ ".type") lt rt remaining
    remaining ← residueRawDiff148 (label ++ ".body") lb rb remaining
  | .letE _ lt lv lb lnd, .letE _ rt rv rb rnd =>
    logInfo m!"RESIDUE148 DIFF {label} letNondependentSame={lnd == rnd}"
    remaining ← residueRawDiff148 (label ++ ".type") lt rt remaining
    remaining ← residueRawDiff148 (label ++ ".value") lv rv remaining
    remaining ← residueRawDiff148 (label ++ ".body") lb rb remaining
  | .proj ln li lb, .proj rn ri rb =>
    logInfo m!"RESIDUE148 DIFF {label} projectionSame={ln == rn && li == ri}"
    remaining ← residueRawDiff148 (label ++ ".body") lb rb remaining
  | _, _ => pure ()
  return remaining

/-- Read precisely the proof aliases and bodies observed in passing1504.
The compiler names are taken from the ACTUAL folded literal constant. -/
private def residueObservedHeadSpecs149 (literalName : Name) : List (Name × Name × Name) :=
  let coordinateProof := ``AllCharacteristics.HomogeneousProjective.CoordinateRing ++ `_proof_1
  [(coordinateProof, ``AddSubmonoidClass, ``Submodule.addSubmonoidClass),
   (``IsScalarTower.right, ``IsScalarTower, ``IsScalarTower.mk),
   (literalName ++ `_proof_1, ``AddSubmonoidClass, coordinateProof),
   (literalName ++ `_proof_3, ``IsScalarTower, ``IsScalarTower.right),
   (literalName ++ `_proof_4, ``AddSubgroupClass, ``Submodule.addSubgroupClass)]

/-- Bounded METADATA comparison only. Reduce only exact inferInstance identity
applications by their verified stored beta body and precisely observed Prop aliases.
Every returned identity argument is the same existing instance term. -/
private def residueNormalizeObserved149 (label : String) (literalName : Name)
    (e : Expr) : TermElabM Expr := do
  let specs := residueObservedHeadSpecs149 literalName
  let visits ← IO.mkRef (0 : Nat)
  let replacements ← IO.mkRef (0 : Nat)
  let identities ← IO.mkRef (0 : Nat)
  let seen ← IO.mkRef ([] : List Name)
  let result ← Core.transform e (pre := fun node => do
    visits.modify (· + 1)
    if (← visits.get) > 20000 then
      throwError "RESIDUE149 {label} observed-node bound20000 exceeded."
    let node := node.consumeMData
    let .const nm ls := node.getAppFn | return .continue
    if nm == ``inferInstance then
      let args := node.getAppArgs
      if args.size != 2 then return .continue
      let .defnInfo info ← getConstInfo nm
        | throwError "RESIDUE149 inferInstance is not the expected identity definition."
      unless info.levelParams.length == ls.length do
        throwError "RESIDUE149 inferInstance universe mismatch."
      let body := (info.value.instantiateLevelParams info.levelParams ls).beta args
      unless body.consumeMData.equal args[1]!.consumeMData do
        throwError "RESIDUE149 refused nonidentity inferInstance stored beta body."
      identities.modify (· + 1)
      if (← identities.get) > 128 then
        throwError "RESIDUE149 {label} identity occurrence bound128 exceeded."
      if (← identities.get) == 1 then
        logInfo m!"RESIDUE149 VERIFIED_INSTANCE_IDENTITY {label} instanceTypeHead={residueRawHead147 args[0]!} sameOriginalArgument=true"
      return .done args[1]!
    let some (_, expectedTypeHead, expectedBodyHead) := specs.find? (fun spec => spec.1 == nm)
      | return .continue
    if node.hasLooseBVars then
      throwError "RESIDUE149 {label} observed proof occurrence has loose bvars."
    let proofType ← inferType node
    if proofType.consumeMData.isForall then return .continue
    let proofSort ← inferType proofType
    unless proofSort.consumeMData.equal (mkSort Level.zero) do
      throwError "RESIDUE149 {label} observed alias not exactly Prop-valued."
    let .const typeHead _ := proofType.getAppFn
      | throwError "RESIDUE149 {label} observed proof type head nonconstant."
    unless typeHead == expectedTypeHead do
      throwError "RESIDUE149 {label} observed proof type head changed: {nm}, {typeHead}."
    let info ← getConstInfo nm
    let some val := info.value? (allowOpaque := true)
      | throwError "RESIDUE149 {label} observed proof alias has no body."
    unless info.levelParams.length == ls.length do
      throwError "RESIDUE149 {label} observed proof universe mismatch."
    let body ← residueNoRecovery147 (← residueOuterLets147
      ((val.instantiateLevelParams info.levelParams ls).beta node.getAppArgs))
    let .const bodyHead _ := body.getAppFn
      | throwError "RESIDUE149 {label} observed proof body head nonconstant."
    unless bodyHead == expectedBodyHead do
      throwError "RESIDUE149 {label} observed proof body head changed: {nm}, {bodyHead}."
    if !((← seen.get).contains nm) then
      seen.modify (nm :: ·)
      logInfo m!"RESIDUE149 VERIFIED_OBSERVED_PROP {label} {nm} typeHead={typeHead} bodyHead={bodyHead}"
    replacements.modify (· + 1)
    if (← replacements.get) > 128 then
      throwError "RESIDUE149 {label} observed proof occurrence bound128 exceeded."
    -- One layer per pass; no arbitrary map/action/data definition unfolds.
    return .done body)
  logInfo m!"RESIDUE149 OBSERVED_PASS {label} visits={← visits.get} proofReplacements={← replacements.get} identityReplacements={← identities.get}"
  return result

private def residueObservedWholeMatch149 (p q : Expr) (literalName : Name) : TermElabM Bool := do
  let mut pn := p
  let mut qn := q
  -- Two alias layers plus original nested explicit inferInstance identities;
  -- four finite passes suffice or the guarded bridge REFUSES.
  for round in [:4] do
    pn ← residueNormalizeObserved149 s!"source{round}" literalName pn
    qn ← residueNormalizeObserved149 s!"literal{round}" literalName qn
    logInfo m!"RESIDUE149 OBSERVED_WHOLE_RAW_SAME round{round} {pn.equal qn}"
    if pn.equal qn then return true
  discard <| residueRawDiff148 "remainingObserved149" pn qn 12
  return false

/-- TRUE metadata only: neither P=Q nor the original header is asserted. -/
elab "residue_observed_alias_diagnostic149% " supplied:term " against " literal:term : term => do
  let supplied ← residueProof147 supplied
  let literal ← residueProof147 literal
  let (p, q, literal) ← residueLiteralVector147 supplied literal
  let .const literalName _ := literal.getAppFn
    | throwError "RESIDUE149 missing actual folded literal constant."
  logInfo m!"RESIDUE149 ACTUAL_LITERAL_NAME {literalName}"
  discard <| residueRawDiff148 "rawObserved149" p q 12
  let matched ← residueObservedWholeMatch149 p q literalName
  logInfo m!"RESIDUE149 DIAGNOSTIC_COMPLETE wholeVectorMatched={matched}; TRUE metadata only."
  return mkConst ``True.intro

/-- Ordinary standalone P=folded Q proof, strictly guarded by WHOLE exact vector
identity after only the observed Prop bodies and identity instance wrappers. -/
elab "residue_observed_type_bridge149% " supplied:term " against " literal:term : term => do
  let supplied ← residueProof147 supplied
  let literal ← residueProof147 literal
  let (p, q, literal) ← residueLiteralVector147 supplied literal
  let .const literalName _ := literal.getAppFn
    | throwError "RESIDUE149 missing actual literal constant."
  unless (← residueObservedWholeMatch149 p q literalName) do
    throwError "RESIDUE149 refused ordinary type bridge: WHOLE vectors still differ."
  -- Unnormalized original P/Q stay in the declared theorem TYPE. The ordinary
  -- kernel must still validate this proof; metadata is never acceptance evidence.
  return mkAppN (mkConst ``Eq.refl [Level.succ Level.zero]) #[mkSort Level.zero, literal]


/-- Bounded identity ONLY. Each inferInstance application must have the actual
stored definition beta body RAW exactly equal to its SAME existing argument1.
No proof alias/category/cohomology/module/action/map definition is unfolded. -/
private def residueExactIdentityVector151 (label : String) (e : Expr) : TermElabM Expr := do
  let mut e := e
  for round in [:4] do
    let visits ← IO.mkRef (0 : Nat)
    let identities ← IO.mkRef (0 : Nat)
    let next ← Core.transform e (pre := fun node => do
      visits.modify (· + 1)
      if (← visits.get) > 20000 then
        throwError "RESIDUE151 {label} identity-node bound20000 exceeded."
      let node := node.consumeMData
      let .const nm ls := node.getAppFn | return .continue
      if nm != ``inferInstance then return .continue
      let args := node.getAppArgs
      if args.size != 2 then return .continue
      let .defnInfo info ← getConstInfo nm
        | throwError "RESIDUE151 inferInstance not the actual identity definition."
      unless info.levelParams.length == ls.length do
        throwError "RESIDUE151 inferInstance universe vector mismatch."
      let body := (info.value.instantiateLevelParams info.levelParams ls).beta args
      unless body.consumeMData.equal args[1]!.consumeMData do
        throwError "RESIDUE151 refused changing a nonidentity inferInstance application."
      identities.modify (· + 1)
      if (← identities.get) > 128 then
        throwError "RESIDUE151 {label} identity occurrence bound128 exceeded."
      if (← identities.get) == 1 then
        logInfo m!"RESIDUE151 VERIFIED_INSTANCE_IDENTITY {label} round{round} typeHead={residueRawHead147 args[0]!} sameOriginalArgument=true"
      return .done args[1]!)
    logInfo m!"RESIDUE151 IDENTITY_PASS {label} round{round} visits={← visits.get} identities={← identities.get}"
    let stable := e.equal next
    e := next
    if stable then break
  return e

private def residueExactTransferVectors151 (supplied bridge literal : Expr) :
    TermElabM (Expr × Expr × Expr × Bool) := do
  let p ← inferType supplied
  let some (carrier, bp, bq) := (← residueOuterLets147 (← inferType bridge)).eq?
    | throwError "RESIDUE151 expected actual stored bridge Eq."
  let carrierSame := carrier.equal (mkSort Level.zero)
  logInfo m!"RESIDUE151 RAW_TRANSFER carrierSort0={carrierSame} bridgeSource/sourceType={bp.equal p} bridgeTarget/foldedLiteral={bq.equal literal}"
  discard <| residueRawDiff148 "transferCarrier/Prop151" carrier (mkSort Level.zero) 12
  discard <| residueRawDiff148 "transferBridgeSource/sourceType151" bp p 12
  discard <| residueRawDiff148 "transferBridgeTarget/foldedLiteral151" bq literal 12
  let bpn ← residueExactIdentityVector151 "bridgeSource" bp
  let pn ← residueExactIdentityVector151 "sourceType" p
  let bqn ← residueExactIdentityVector151 "bridgeTarget" bq
  let qn ← residueExactIdentityVector151 "foldedLiteral" literal
  let sourceSame := bpn.equal pn
  let targetSame := bqn.equal qn
  logInfo m!"RESIDUE151 IDENTITY_TRANSFER carrierSort0={carrierSame} WHOLEbridgeSource/sourceType={sourceSame} WHOLEbridgeTarget/foldedLiteral={targetSame}"
  if !sourceSame then
    discard <| residueRawDiff148 "remainingTransferSource151" bpn pn 12
  if !targetSame then
    discard <| residueRawDiff148 "remainingTransferTarget151" bqn qn 12
  return (bp, bq, supplied, carrierSame && sourceSame && targetSame)

/-- TRUE-only diagnostic at the exact original coefficient transfer vector.
No Eq.mp, P=Q, or original coefficient equality is emitted. -/
elab "residue_transfer_diagnostic151% " supplied:term " using " bridge:term " against " literal:term : term => do
  let supplied ← residueProof147 supplied
  let bridge ← residueProof147 bridge
  let literal ← residueProof147 literal
  let (_, _, _, matched) ← residueExactTransferVectors151 supplied bridge literal
  logInfo m!"RESIDUE151 TRANSFER_DIAGNOSTIC_COMPLETE wholeIdentityMatch={matched}; TRUE metadata only."
  return mkConst ``True.intro

/-- Ordinary Eq.mp on the bridge's ACTUAL unnormalized P/Q. Only same-existing
inferInstance identity forwarding is accepted by the exact WHOLE raw-vector guard.
Ordinary kernel validation remains required; no desired-trace premise is added. -/
elab "residue_exact_transfer151% " supplied:term " using " bridge:term " against " literal:term : term => do
  let supplied ← residueProof147 supplied
  let bridge ← residueProof147 bridge
  let literal ← residueProof147 literal
  let (bp, bq, supplied, matched) ← residueExactTransferVectors151 supplied bridge literal
  unless matched do
    throwError "RESIDUE151 refused Eq.mp: full transfer vectors differ beyond verified original-instance identities."
  return mkAppN (mkConst ``Eq.mp [Level.zero]) #[bp, bq, bridge, supplied]

end
private theorem cubicNativeObservedLiteralTypeBridge149
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules]
    [hExt : HasExt.{u} (hypersurface p hp).Modules] :
    (type_of% (@cubicNativeStoredAdditiveComposition147 K (inferInstance : Field K) p hp hp0
      (inferInstance : IsDomain (CoordinateRing (equationIdeal p hp)))
      ‹HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules› hExt)) = residueNativeLiteralProposition147 p hp hp0 :=
  residue_observed_type_bridge149% (@cubicNativeStoredAdditiveComposition147 K (inferInstance : Field K) p hp hp0
      (inferInstance : IsDomain (CoordinateRing (equationIdeal p hp)))
      ‹HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules› hExt) against (residueNativeLiteralProposition147 p hp hp0)

/-- First ordinary cut: SAME actual151 Eq.mp, with the ORIGINAL literal Q left FOLDED. -/
private theorem cubicNativeOriginalLiteralFoldedCoefficient152
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules]
    [hExt : HasExt.{u} (hypersurface p hp).Modules] :
    residueNativeLiteralProposition147 p hp hp0 :=
  residue_exact_transfer151% (@cubicNativeStoredAdditiveComposition147 K (inferInstance : Field K) p hp hp0
      (inferInstance : IsDomain (CoordinateRing (equationIdeal p hp)))
      ‹HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules› hExt)
    using (@cubicNativeObservedLiteralTypeBridge149 K (inferInstance : Field K) p hp hp0
      (inferInstance : IsDomain (CoordinateRing (equationIdeal p hp)))
      ‹HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules› hExt) against (residueNativeLiteralProposition147 p hp hp0)


meta section
open Lean Meta Elab Term

/-- Return the accepted folded proof ITSELF after exact folded-Q identity guards.
No Eq.mp/source-carrier conversion or literal/category/action unfolding here. -/
elab "residue_folded_original_header152% " supplied:term " against " literal:term : term => do
  let supplied ← residueProof147 supplied
  let literal ← residueProof147 literal
  let suppliedType ← inferType supplied
  let .const literalName _ := literal.getAppFn
    | throwError "RESIDUE152 expected folded original literal constant."
  unless literalName == ``residueNativeLiteralProposition147 &&
      suppliedType.getAppFn.isConstOf literalName do
    throwError "RESIDUE152 refused a different folded original proposition head."
  logInfo m!"RESIDUE152 FOLDED_HEADER rawSame={suppliedType.equal literal}"
  let pn ← residueExactIdentityVector151 "foldedProofType152" suppliedType
  let qn ← residueExactIdentityVector151 "foldedLiteral152" literal
  unless pn.equal qn do
    discard <| residueRawDiff148 "remainingFoldedHeader152" pn qn 12
    throwError "RESIDUE152 refused folded header transfer beyond SAME original-instance identities."
  logInfo "RESIDUE152 FOLDED_HEADER WHOLEidentityRawSame=true; returning original accepted folded proof unchanged."
  -- Ordinary kernel checks unfolding of that exact original folded Q against
  -- the unchanged literal header in its own standalone declaration.
  return supplied

end

/-- Normalize only the canonical projection using the accepted additive trace equality. -/
theorem cubicNativeCanonicalTraceLinearMap_toAddMonoidHom
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules]
    [hExt : HasExt.{u} (hypersurface p hp).Modules] :
    let X : Scheme.{u} := Proj (grading (equationIdeal p hp))
    let W : X.Modules := sheafOfModules (grading (equationIdeal p hp)) 1
    letI : HasExt.{u} X.Modules := hExt
    letI : Linear K X.Modules := schemeModulesLinearOver (hypersurfaceToBase p hp)
    letI : AddCommGroup (schemeModuleCohomology X W 2) := Ext.instAddCommGroup
    letI : Module K (schemeModuleCohomology X W 2) := Ext.instModule
    (cubicNativeCanonicalTraceLinearMap p hp hp0).toAddMonoidHom =
      (cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0).toAddMonoidHom :=
  residue_folded_original_header152% (@cubicNativeOriginalLiteralFoldedCoefficient152 K (inferInstance : Field K) p hp hp0
      (inferInstance : IsDomain (CoordinateRing (equationIdeal p hp)))
      ‹HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules› hExt) against (residueNativeLiteralProposition147 p hp hp0)

end PfaffianDescent.Coray
