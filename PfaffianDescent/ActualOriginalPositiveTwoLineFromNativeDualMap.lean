import PfaffianDescent.ResidueCompatibleActualDualMorphismLine
import PfaffianDescent.ActualOriginalPositiveTwoNativeJetHZeroKernel

/- SOURCE ONLY / UNVERIFIED. From the SAME actual native map and original
residue, derive a genuine Omega(2) line, its action on EVERY original ideal
quadratic section, and the exact embedded native reconstruction. -/
namespace NativeDualLineCoercion005
open CategoryTheory
universe u v

/- The diagnosed ModuleCat wrapper is precisely its declared concrete hom.
This is a genuine ordinary data equality, checked by the enclosing kernel. -/
private theorem module_hom_eq_concrete
    {R : Type u} [Ring R] {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    f.hom = ConcreteCategory.hom (C := ModuleCat.{v} R) f := by
  rfl

end NativeDualLineCoercion005

noncomputable section
namespace NativeDualLineResidue005
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

end NativeDualLineResidue005
end

namespace NativeDualLineStructural005

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

end NativeDualLineStructural005

meta section
namespace NativeDualLineStructural005
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
      n == ``ModuleCat.Hom.hom ||
      n == ``AllCharacteristics.HomogeneousProjective.ChartRing ||
      n == ``AllCharacteristics.HomogeneousProjective.scheme || n == ``id
    | _ => false
  if !allowed then return e
  let some e' ← delta? e (fun n => isLocalLawName n ||
    n == ``AllCharacteristics.HomogeneousProjective.hypersurface ||
      n == ``PfaffianDescent.closedImmersionIdealTwist ||
      n == ``ModuleCat.Hom.hom ||
      n == ``AllCharacteristics.HomogeneousProjective.ChartRing ||
      n == ``AllCharacteristics.HomogeneousProjective.scheme || n == ``id)
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
  let proof := mkAppN (mkConst ``NativeDualLineResidue005.native_commRing_eq levels) fieldArgs
  let ty ← instantiateMVars (← inferType proof)
  let some (_, oldRing, newRing) := ty.eq?
    | throwError "NativeRing117 ordinary leaf did not infer an equality."
  let oldRing ← normalizeHead oldRing 8
  let newRing ← normalizeHead newRing 8
  unless oldRing.equal left && newRing.equal right do
    logInfo m!"NativeRing117 refused a different residue boundary: raw left match={oldRing.equal left}, raw right match={newRing.equal right}."
    return none
  return some (← mkHEqOfEq proof)

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
  let proof := mkAppN (mkConst ``NativeDualLineResidue005.native_bundle_eq levels) ra
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
  let proof := mkAppN (mkConst ``NativeDualLineResidue005.native_carrier_eq levels) nativeArgs
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
  let proof := mkAppN (mkConst ``NativeDualLineResidue005.native_field_heq levels) la
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
  let proof := mkAppN (mkConst ``NativeDualLineResidue005.native_standard_bundle_eq levels) ra
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
  if let some h ← nativeRingLeaf117? left right then
    modify fun s => { s with wrapperLeaves := s.wrapperLeaves + 1 }
    return ← cache left0 right0 h
  if let some h ← nativeRingLeaf117? right left then
    modify fun s => { s with wrapperLeaves := s.wrapperLeaves + 1 }
    return ← cache left0 right0 (← mkHEqSymm h)
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

end NativeDualLineStructural005
end

namespace NativeDualLineCoercion009
open CategoryTheory
universe u v

/- The diagnosed ModuleCat wrapper is precisely its declared concrete hom.
This is a genuine ordinary data equality, checked by the enclosing kernel. -/
private theorem module_hom_eq_concrete
    {R : Type u} [Ring R] {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    f.hom = ConcreteCategory.hom (C := ModuleCat.{v} R) f := by
  rfl

end NativeDualLineCoercion009

noncomputable section
namespace NativeDualLineResidue009
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

end NativeDualLineResidue009
end

namespace NativeDualLineStructural009

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

end NativeDualLineStructural009

meta section
namespace NativeDualLineStructural009
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
      n == ``ModuleCat.Hom.hom ||
      n == ``AllCharacteristics.HomogeneousProjective.ChartRing ||
      n == ``AllCharacteristics.HomogeneousProjective.scheme || n == ``id
    | _ => false
  if !allowed then return e
  let some e' ← delta? e (fun n => isLocalLawName n ||
    n == ``AllCharacteristics.HomogeneousProjective.hypersurface ||
      n == ``PfaffianDescent.closedImmersionIdealTwist ||
      n == ``ModuleCat.Hom.hom ||
      n == ``AllCharacteristics.HomogeneousProjective.ChartRing ||
      n == ``AllCharacteristics.HomogeneousProjective.scheme || n == ``id)
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
  let proof := mkAppN (mkConst ``NativeDualLineResidue009.native_commRing_eq levels) fieldArgs
  let ty ← instantiateMVars (← inferType proof)
  let some (_, oldRing, newRing) := ty.eq?
    | throwError "NativeRing117 ordinary leaf did not infer an equality."
  let oldRing ← normalizeHead oldRing 8
  let newRing ← normalizeHead newRing 8
  unless oldRing.equal left && newRing.equal right do
    logInfo m!"NativeRing117 refused a different residue boundary: raw left match={oldRing.equal left}, raw right match={newRing.equal right}."
    return none
  return some (← mkHEqOfEq proof)

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
  let proof := mkAppN (mkConst ``NativeDualLineResidue009.native_bundle_eq levels) ra
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
  let proof := mkAppN (mkConst ``NativeDualLineResidue009.native_carrier_eq levels) nativeArgs
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
  let proof := mkAppN (mkConst ``NativeDualLineResidue009.native_field_heq levels) la
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
  let proof := mkAppN (mkConst ``NativeDualLineResidue009.native_standard_bundle_eq levels) ra
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
  if let some h ← nativeRingLeaf117? left right then
    modify fun s => { s with wrapperLeaves := s.wrapperLeaves + 1 }
    return ← cache left0 right0 h
  if let some h ← nativeRingLeaf117? right left then
    modify fun s => { s with wrapperLeaves := s.wrapperLeaves + 1 }
    return ← cache left0 right0 (← mkHEqSymm h)
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

end NativeDualLineStructural009
end

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

section
variable {K : Type u} [Field K] [PerfectField K]
  (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
  (P : closedPoints (hypersurface p hp))
  (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)

/- Check only native composition surjectivity; the opaque public line is absent. -/
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineCompositionSurjective004 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    letI : Algebra (ChartRing (equationIdeal p hp) C.index) L := C.residue.toAlgebra
    letI : IsScalarTower K (ChartRing (equationIdeal p hp) C.index) L :=
      IsScalarTower.of_algebraMap_eq (fun c => (RingHom.congr_fun C.base c).symm)
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r), Function.Surjective phi →
        Function.Surjective ((residueCompatibleActualDualFiberLine phi hred).comp
          (actualCubicPositiveTwoOriginalNativePointFiberEquiv (K := K) (L := L) p hp
            ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue
              C.factorization).toLinearMap) := by
  intro C L
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let R := ChartRing (equationIdeal p hp) C.index
  letI aK : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  letI : SMul K R := aK.toSMul
  intro phi hred hphi
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun C.base c).symm)
  let E := actualCubicPositiveTwoOriginalNativePointFiberEquiv (K := K) (L := L) p hp
    ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization
  exact (residueCompatibleActualDualFiberLine_surjective phi hred hphi).comp E.surjective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def actualOriginalPositiveTwoLineFromNativeDualMap :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L,
      (∀ r, (phi r).fst = C.residue r) →
        (ActualOriginalPositiveTwoFiber p hp P →ₗ[L] L) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let R := ChartRing (equationIdeal p hp) C.index
  let L := (hypersurface p hp).residueField P.1
  letI aK : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  letI : SMul K R := aK.toSMul
  intro phi hred
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun C.base c).symm)
  let E := actualCubicPositiveTwoOriginalNativePointFiberEquiv (K := K) (L := L) p hp
    ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization
  exact (residueCompatibleActualDualFiberLine phi hred).comp E.toLinearMap

meta section
open Lean Meta Elab Tactic

/- One public line defining delta; no recursive dsimp or instance normalization. -/
private def nativeDualLineDefinitionVectors006 (supplied : Syntax) : Term.TermElabM (Expr × Expr) := do
  let original ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let original ← instantiateMVars original
  logInfo m!"NativeDualLine006 stored line head={original.getAppFn}, arity={original.getAppArgs.size}."
  unless original.getAppFn.isConstOf ``actualOriginalPositiveTwoLineFromNativeDualMap &&
      original.getAppArgs.size == 9 do
    throwError "NativeDualLine006 expected original public line9 (seven geometric parameters, phi, hred)."
  let some expanded ← delta? original (fun n => n == ``actualOriginalPositiveTwoLineFromNativeDualMap)
    | throwError "NativeDualLine006 cannot take the single public line delta."
  if original.hasMVar || original.hasLevelMVar || original.hasLooseBVars || original.hasSorry ||
      expanded.hasMVar || expanded.hasLevelMVar || expanded.hasLooseBVars || expanded.hasSorry then
    throwError "NativeDualLine006 refuses unresolved/recovery map endpoints."
  return (original, expanded)

elab "native_dual_line_definition_cut006% " supplied:term : term => do
  let (original, expanded) ← nativeDualLineDefinitionVectors006 supplied
  return ← mkEq original expanded

elab "native_dual_line_definition_rfl006" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, original, target) := (← instantiateMVars (← goal.getType)).consumeMData.headBeta.eq?
    | throwError "NativeDualLine006 expected an ordinary defining-map Eq."
  unless original.getAppFn.isConstOf ``actualOriginalPositiveTwoLineFromNativeDualMap &&
      original.getAppArgs.size == 9 do
    throwError "NativeDualLine006 refuses a different defining map head/arity."
  let some expanded ← delta? original (fun n => n == ``actualOriginalPositiveTwoLineFromNativeDualMap)
    | throwError "NativeDualLine006 cannot retrieve the single defining delta."
  unless target.equal expanded do
    throwError "NativeDualLine006 refuses a different stored defining body."
  logInfo "NativeDualLine006 ordinary rfl assigned for exactly one defining delta; kernel checks it."
  goal.assign (← mkEqRefl original)
  replaceMainGoal []

/- Preserve the exact original Surjective3 and unapplied linear-map coe5 application vectors. -/
private def nativeDualLineSurjectiveVectors006 (supplied : Syntax) : Term.TermElabM (Array Expr) := do
  let original ← Term.elabTerm supplied (some (mkSort Level.zero)) (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let original ← instantiateMVars original
  let sa := original.consumeMData.getAppArgs
  unless original.getAppFn.isConstOf ``Function.Surjective && sa.size == 3 do
    throwError "NativeDualLine006 expected stored Surjective3; head={original.getAppFn}, arity={sa.size}."
  let fn := sa[2]!.consumeMData
  let fa := fn.getAppArgs
  unless fn.getAppFn.isConstOf ``DFunLike.coe && fa.size == 5 do
    throwError "NativeDualLine006 expected stored unapplied linear-map coe5; head={fn.getAppFn}, arity={fa.size}."
  let line := fa[4]!.consumeMData
  unless line.getAppFn.isConstOf ``actualOriginalPositiveTwoLineFromNativeDualMap &&
      line.getAppArgs.size == 9 do
    throwError "NativeDualLine006 refuses a different public line under stored Surjective."
  let some expanded ← delta? line (fun n => n == ``actualOriginalPositiveTwoLineFromNativeDualMap)
    | throwError "NativeDualLine006 cannot retrieve the single public-line body."
  let bodyFn := mkAppN fn.getAppFn (fa.set! 4 expanded)
  let bodyProp := mkAppN original.getAppFn (sa.set! 2 bodyFn)
  if original.hasMVar || original.hasLevelMVar || original.hasLooseBVars || original.hasSorry ||
      bodyProp.hasMVar || bodyProp.hasLevelMVar || bodyProp.hasLooseBVars || bodyProp.hasSorry then
    throwError "NativeDualLine006 refuses unresolved/recovery stored surjectivity endpoints."
  return #[original, bodyProp, line, expanded]

elab "native_dual_line_body_surjective006% " supplied:term : term => do
  let values ← nativeDualLineSurjectiveVectors006 supplied
  return values[1]!

elab "native_dual_line_surjective_transport006% " suppliedProp:term ", " suppliedMapEq:term : term => do
  let values ← nativeDualLineSurjectiveVectors006 suppliedProp
  let hMap ← Term.elabTerm suppliedMapEq none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let hMap ← instantiateMVars hMap
  let some (_, left, right) := (← instantiateMVars (← inferType hMap)).consumeMData.headBeta.eq?
    | throwError "NativeDualLine006 expected checked defining-map equality."
  unless left.equal values[2]! && right.equal values[3]! do
    throwError "NativeDualLine006 defining-map equality has different exact endpoints."
  let original := values[0]!
  let sa := original.getAppArgs
  let fn := sa[2]!.consumeMData
  let fa := fn.getAppArgs
  let predicate ← withLocalDeclD `line (← inferType left) fun line => do
    mkLambdaFVars #[line] (mkAppN original.getAppFn
      (sa.set! 2 (mkAppN fn.getAppFn (fa.set! 4 line))))
  let proof ← mkCongrArg predicate hMap
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeDualLine006 refuses unresolved/recovery ordinary proposition transport."
  logInfo "NativeDualLine006 ordinary congrArg of exact stored Surjective/coe vectors inferred without expected public type."
  return proof

end

meta section
open Lean Meta Elab Tactic

/- Infer the exact proposition of the already checked native composition proof. -/
private def nativeDualLineSourceProposition008 (supplied : Syntax) : Term.TermElabM Expr := do
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let source ← instantiateMVars source
  let sourceType ← instantiateMVars (← inferType source)
  if source.hasMVar || source.hasLevelMVar || source.hasLooseBVars || source.hasSorry ||
      sourceType.hasMVar || sourceType.hasLevelMVar || sourceType.hasLooseBVars || sourceType.hasSorry then
    throwError "NativeDualLine008 refuses unresolved/recovery native source."
  unless ← isProp sourceType do
    throwError "NativeDualLine008 expected the native composition proof's proposition."
  return sourceType

elab "native_dual_line_source_prop008% " supplied:term : term => do
  return ← nativeDualLineSourceProposition008 supplied

/- Ordinary equality of the actual native and ONE-delta-body propositions. -/
elab "native_dual_line_body_type_cut008% " supplied:term ", " suppliedProp:term : term => do
  let sourceType ← nativeDualLineSourceProposition008 supplied
  let values ← nativeDualLineSurjectiveVectors006 suppliedProp
  let target := values[1]!
  logInfo m!"NativeDualLine008 proposition cut: source head={sourceType.getAppFn}, arity={sourceType.getAppArgs.size}; body head={target.getAppFn}, arity={target.getAppArgs.size}; raw match={sourceType.equal target}."
  return ← mkEq sourceType target

end

meta section
open Lean Meta Elab Tactic

/- Actual008 compares the source/body propositions at path0/2 after the outer Eq. -/
private def nativeDualLineFiberPath009 (input : Expr) : Term.TermElabM Expr := do
  let mut current := input
  for index in #[0, 2] do
    current ← NativeDualLineStructural009.normalizeHead current 8
    current ← NativeDualLineStructural009.projectionAsApplication current
    let args := current.getAppArgs
    unless index < args.size do
      throwError "NativeDualLine009 path index{index} exceeds head={current.getAppFn}, arity={args.size}."
    current := args[index]!
  return ← NativeDualLineStructural009.normalizeHead current 8

/- Preserve every actual module object, native point and fiber-alias parameter. -/
elab "native_dual_line_fiber_cut009% " suppliedSource:term ", " suppliedProp:term : term => do
  let sourceType ← nativeDualLineSourceProposition008 suppliedSource
  let values ← nativeDualLineSurjectiveVectors006 suppliedProp
  let left ← nativeDualLineFiberPath009 sourceType
  let right ← nativeDualLineFiberPath009 values[1]!
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless left.getAppFn.isConstOf ``Functor.obj && la.size == 6 &&
      right.getAppFn.isConstOf ``ActualOriginalPositiveTwoFiber && ra.size == 5 do
    throwError "NativeDualLine009 refuses a seed beyond Functor.obj6/OriginalPositiveTwoFiber5: left={left.getAppFn}/{la.size}, right={right.getAppFn}/{ra.size}."
  if left.hasMVar || left.hasLevelMVar || left.hasLooseBVars || left.hasSorry ||
      right.hasMVar || right.hasLevelMVar || right.hasLooseBVars || right.hasSorry then
    throwError "NativeDualLine009 refuses unresolved/recovery exact fiber endpoints."
  logInfo m!"NativeDualLine009 exact original fiber nodes: functor head={la[4]!.getAppFn}, object head={la[5]!.getAppFn}; original alias K/field/p/hp/P vector retained5."
  return ← mkHEq left right

/- Only the ordinary exact fiber HEq and its reverse enter the existing cache. -/
elab "native_dual_line_body_fiber_exact009 " supplied:term " using " suppliedSeed:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← Term.elabTerm supplied none (catchExPostpone := false)
    let seed ← Term.elabTerm suppliedSeed none (catchExPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    let source ← instantiateMVars source
    let seed ← instantiateMVars seed
    let sourceType ← instantiateMVars (← inferType source)
    let target ← instantiateMVars (← goal.getType)
    let seedType := (← instantiateMVars (← inferType seed)).consumeMData.headBeta
    let some (_, left, _, right) := seedType.heq?
      | throwError "NativeDualLine009 expected ordinary exact fiber HEq."
    unless left.getAppFn.isConstOf ``Functor.obj && left.getAppArgs.size == 6 &&
        right.getAppFn.isConstOf ``ActualOriginalPositiveTwoFiber && right.getAppArgs.size == 5 do
      throwError "NativeDualLine009 refuses a seed beyond actual Functor.obj6/fiberAlias5."
    if source.hasMVar || source.hasLevelMVar || source.hasLooseBVars || source.hasSorry ||
        seed.hasMVar || seed.hasLevelMVar || seed.hasLooseBVars || seed.hasSorry then
      throwError "NativeDualLine009 refuses unresolved/recovery source or seed."
    let reverse ← mkHEqSymm seed
    let (heq, state) ←
      (NativeDualLineStructural009.structuralHEq sourceType target
        96 #[] "chart009").run
          { pairs := #[(left, right, seed), (right, left, reverse)] }
    let typeProof ← mkEqOfHEq heq
    let proof := mkAppN (mkConst ``Eq.mp [Level.zero]) #[sourceType, target, typeProof, source]
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "NativeDualLine009 refuses unresolved/recovery emitted certificate."
    logInfo m!"NativeDualLine009 exact cached ordinary fiber compatibility emitted: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruence steps={state.congrSteps}, binders={state.binderSteps}, unused traversal budget={state.remaining}."
    goal.assign proof
    replaceMainGoal []

end

meta section
open Lean Meta Elab Tactic

private def nativeDualLineValuePath010 (input : Expr) : Term.TermElabM Expr := do
  let mut current := input
  for index in #[2, 4] do
    current ← NativeDualLineStructural009.normalizeHead current 8
    current ← NativeDualLineStructural009.projectionAsApplication current
    let args := current.getAppArgs
    unless index < args.size do
      throwError "NativeDualLine010 path index{index} exceeds head={current.getAppFn}, arity={args.size}."
    current := args[index]!
  return current


end

meta section
open Lean Meta Elab Tactic

/- Seven guarded, SINGLE computational reductions of the actual printed body.
No native factory is unfolded, and no source composition is used here. -/
private def nativeDualLineBodyHead011 (e : Expr) : String :=
  match e.getAppFn.consumeMData with
  | .const name _ => s!"constant {name}"
  | .letE name .. => s!"let {name}"
  | .lam name .. => s!"lambda {name}"
  | .fvar _ => "local"
  | .proj name index _ => s!"projection {name}.{index}"
  | _ => "other"

private def nativeDualLineBodyStep011 (step : Nat) (input : Expr) : MetaM Expr := do
  let current := input.consumeMData
  let fn := current.getAppFn.consumeMData
  let args := current.getAppArgs
  let output ← match step with
    | 0 => do
        unless fn.isConstOf ``id && args.size == 4 do
          throwError "NativeDualLine011 step0 expects id4 (type, stored function, phi, hred); actual arity={args.size}."
        return mkAppN args[1]! (args.extract 2 4)
    | 1 | 2 | 3 => do
        let .letE name _ value body _ := fn
          | throwError "NativeDualLine011 step{step} expects an applied C/R/L let; actual head={nativeDualLineBodyHead011 fn}, arity={args.size}."
        unless args.size == 2 do
          throwError "NativeDualLine011 step{step} expects exactly phi/hred after let {name}; actual arity={args.size}."
        logInfo m!"NativeDualLine011 step{step}: substitute ONE stored let {name}; retain other lets."
        return mkAppN (body.instantiate1 value) args
    | 4 | 5 => do
        let .lam name _ body _ := fn
          | throwError "NativeDualLine011 step{step} expects the actual phi/hred lambda; actual head={nativeDualLineBodyHead011 fn}, arity={args.size}."
        let expected := if step == 4 then 2 else 1
        unless args.size == expected do
          throwError "NativeDualLine011 step{step} expects {expected} remaining lambda arguments; actual arity={args.size}."
        logInfo m!"NativeDualLine011 step{step}: beta ONE stored lambda {name}."
        return mkAppN (body.instantiate1 args[0]!) (args.extract 1 args.size)
    | 6 => do
        let .letE name _ value body _ := fn
          | throwError "NativeDualLine011 step6 expects the actual E let; actual head={nativeDualLineBodyHead011 fn}, arity={args.size}."
        unless args.isEmpty do
          throwError "NativeDualLine011 step6 expects naked E let; actual arity={args.size}."
        let output := body.instantiate1 value
        unless output.getAppFn.isConstOf ``LinearMap.comp && output.getAppArgs.size == 21 do
          throwError "NativeDualLine011 E substitution must produce original LinearMap.comp21; actual head={nativeDualLineBodyHead011 output}, arity={output.getAppArgs.size}."
        logInfo m!"NativeDualLine011 step6: substitute ONE stored let {name}; resulting original comp21 retained."
        return output
    | _ => throwError "NativeDualLine011 refuses a computational step outside0–6."
  if output.hasMVar || output.hasLevelMVar || output.hasLooseBVars || output.hasSorry then
    throwError "NativeDualLine011 refuses unresolved/recovery computed node at step{step}."
  return output

private def nativeDualLineBodyStages011 (suppliedProp : Syntax) (count : Nat) : Term.TermElabM (Array Expr) := do
  unless count <= 7 do
    throwError "NativeDualLine011 refuses more than the seven fixed body reductions."
  let values ← nativeDualLineSurjectiveVectors006 suppliedProp
  -- values[3] is the EXACT same one-delta body used in bodyProp's coe slot4.
  let raw := values[3]!
  let mut nodes := #[raw]
  let mut current := raw
  for step in [:count] do
    current ← nativeDualLineBodyStep011 step current
    nodes := nodes.push current
  return nodes

elab "native_dual_line_body_compute_cut011% " step:num suppliedProp:term : term => do
  let index := step.getNat
  unless index < 7 do
    throwError "NativeDualLine011 requires one of the exact seven body reductions."
  let nodes ← nativeDualLineBodyStages011 suppliedProp (index + 1)
  logInfo m!"NativeDualLine011 RHS-only ordinary computational certificate {index}; no native-source value or equality assumed."
  return ← mkHEq nodes[index]! nodes[index + 1]!

end

meta section
open Lean Meta Elab Tactic

elab "native_dual_line_computed_composition_cut011% " suppliedSource:term ", " suppliedProp:term : term => do
  let sourceType ← nativeDualLineSourceProposition008 suppliedSource
  let left ← nativeDualLineValuePath010 sourceType
  let nodes ← nativeDualLineBodyStages011 suppliedProp 7
  let right := nodes[7]!
  unless left.getAppFn.isConstOf ``LinearMap.comp && left.getAppArgs.size == 21 &&
      right.getAppFn.isConstOf ``LinearMap.comp && right.getAppArgs.size == 21 do
    throwError "NativeDualLine011 final cut expects exact RAW comp21/comp21, not an applied let; left arity={left.getAppArgs.size}, right arity={right.getAppArgs.size}."
  if left.hasMVar || left.hasLevelMVar || left.hasLooseBVars || left.hasSorry ||
      right.hasMVar || right.hasLevelMVar || right.hasLooseBVars || right.hasSorry then
    throwError "NativeDualLine011 refuses unresolved/recovery native/computed composition endpoints."
  let la := left.getAppArgs
  let ra := right.getAppArgs
  let mut differentSlots : Array Nat := #[]
  for index in [:21] do
    unless la[index]!.equal ra[index]! do
      differentSlots := differentSlots.push index
  logInfo m!"NativeDualLine011 RAW comp21/comp21 cut: same raw expression={left.equal right}; differing raw argument slots={differentSlots}. No equality inferred from this diagnostic."
  return ← mkHEq left right

elab "native_dual_line_computed_exact011 " "using " suppliedSeed:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
    let some (_, left, _, right) := target.heq?
      | throwError "NativeDualLine011 expects the separately stored composition HEq."
    unless left.getAppFn.isConstOf ``LinearMap.comp && left.getAppArgs.size == 21 &&
        right.getAppFn.isConstOf ``LinearMap.comp && right.getAppArgs.size == 21 do
      throwError "NativeDualLine011 composition tactic refuses other native maps or computational lets."
    let seed ← Term.elabTerm suppliedSeed none (catchExPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    let seed ← instantiateMVars seed
    let seedType := (← instantiateMVars (← inferType seed)).consumeMData.headBeta
    let some (_, fiberLeft, _, fiberRight) := seedType.heq?
      | throwError "NativeDualLine011 expects the PASSED exact009 fiber HEq."
    unless fiberLeft.getAppFn.isConstOf ``Functor.obj && fiberLeft.getAppArgs.size == 6 &&
        fiberRight.getAppFn.isConstOf ``ActualOriginalPositiveTwoFiber && fiberRight.getAppArgs.size == 5 do
      throwError "NativeDualLine011 refuses any seed beyond the existing Functor.obj6/fiber5 compatibility."
    if seed.hasMVar || seed.hasLevelMVar || seed.hasLooseBVars || seed.hasSorry then
      throwError "NativeDualLine011 refuses unresolved/recovery seed proof."
    let reverse ← mkHEqSymm seed
    let (proof, state) ←
      (NativeDualLineStructural009.structuralHEq left right 96 #[] "chart009").run
        { pairs := #[(fiberLeft, fiberRight, seed), (fiberRight, fiberLeft, reverse)] }
    let proof ← instantiateMVars proof
    if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "NativeDualLine011 refuses unresolved/recovery composition compatibility proof."
    logInfo m!"NativeDualLine011 ordinary native/computed comp compatibility emitted: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruence steps={state.congrSteps}, binders={state.binderSteps}, unused traversal budget={state.remaining}."
    goal.assign proof
    replaceMainGoal []

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineComputedCompositionHEq011 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
      ∀ hphi : Function.Surjective phi,
        native_dual_line_computed_composition_cut011% (nativeDualLineCompositionSurjective004 p hp P hP phi hred hphi),
          (Function.Surjective (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred)) := by
  intro C L phi hred hphi
  have hFiber : native_dual_line_fiber_cut009% (nativeDualLineCompositionSurjective004 p hp P hP phi hred hphi),
      (Function.Surjective (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred)) := by
    rfl
  native_dual_line_computed_exact011 using hFiber


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineBodyComputeStep0011 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
        native_dual_line_body_compute_cut011% 0
          (Function.Surjective (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred)) := by
  intro C L phi hred
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineBodyComputeStep1011 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
        native_dual_line_body_compute_cut011% 1
          (Function.Surjective (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred)) := by
  intro C L phi hred
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineBodyComputeStep2011 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
        native_dual_line_body_compute_cut011% 2
          (Function.Surjective (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred)) := by
  intro C L phi hred
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineBodyComputeStep3011 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
        native_dual_line_body_compute_cut011% 3
          (Function.Surjective (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred)) := by
  intro C L phi hred
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineBodyComputeStep4011 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
        native_dual_line_body_compute_cut011% 4
          (Function.Surjective (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred)) := by
  intro C L phi hred
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineBodyComputeStep5011 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
        native_dual_line_body_compute_cut011% 5
          (Function.Surjective (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred)) := by
  intro C L phi hred
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineBodyComputeStep6011 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
        native_dual_line_body_compute_cut011% 6
          (Function.Surjective (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred)) := by
  intro C L phi hred
  rfl

meta section
open Lean Meta Elab Tactic

/- Infer each accepted certificate WITHOUT a reconstructed expected native type. -/
private def nativeDualLineStoredHEq013 (supplied : Syntax) : Term.TermElabM (Expr × Expr × Expr) := do
  let proof ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  let type := (← instantiateMVars (← inferType proof)).consumeMData.headBeta
  let some (_, left, _, right) := type.heq?
    | throwError "NativeDualLine013 requires an ordinary stored HEq certificate."
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry ||
      type.hasMVar || type.hasLevelMVar || type.hasLooseBVars || type.hasSorry then
    throwError "NativeDualLine013 refuses unresolved/recovery stored certificates."
  return (proof, left, right)

elab "native_dual_line_rhs_join013% " supplied0:term ", " supplied1:term ", " supplied2:term ", " supplied3:term ", " supplied4:term ", " supplied5:term ", " supplied6:term : term => do
  let certificates ← (#[supplied0.raw, supplied1.raw, supplied2.raw, supplied3.raw,
    supplied4.raw, supplied5.raw, supplied6.raw]).mapM nativeDualLineStoredHEq013
  let (first, _, firstRight) := certificates[0]!
  let mut proof := first
  let mut right := firstRight
  for index in [1:7] do
    let (next, nextLeft, nextRight) := certificates[index]!
    unless right.equal nextLeft do
      throwError "NativeDualLine013 RHS join{index} refuses different RAW intermediate endpoints; no conversion assumed."
    proof ← mkHEqTrans proof next
    right := nextRight
  proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeDualLine013 refuses unresolved/recovery RHS chain."
  logInfo "NativeDualLine013 exact seven-step RHS chain inferred from stored ordinary certificate vectors; six raw middle checks passed."
  return proof

elab "native_dual_line_value_join013% " suppliedNative:term ", " suppliedRhs:term : term => do
  let (nativeProof, _, nativeRight) ← nativeDualLineStoredHEq013 suppliedNative
  let (rhsProof, _, rhsRight) ← nativeDualLineStoredHEq013 suppliedRhs
  unless nativeRight.equal rhsRight do
    throwError "NativeDualLine013 refuses different RAW computed composition endpoints for the native/RHS join."
  let proof ← mkHEqTrans nativeProof (← mkHEqSymm rhsProof)
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeDualLine013 refuses unresolved/recovery native value join."
  logInfo "NativeDualLine013 exact native/computed certificate joined with reverse stored RHS computation chain; raw middle check passed."
  return proof

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineRhsJoinInferred013 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
      type_of% (native_dual_line_rhs_join013% (nativeDualLineBodyComputeStep0011 p hp P hP phi hred),
        (nativeDualLineBodyComputeStep1011 p hp P hP phi hred),
        (nativeDualLineBodyComputeStep2011 p hp P hP phi hred),
        (nativeDualLineBodyComputeStep3011 p hp P hP phi hred),
        (nativeDualLineBodyComputeStep4011 p hp P hP phi hred),
        (nativeDualLineBodyComputeStep5011 p hp P hP phi hred),
        (nativeDualLineBodyComputeStep6011 p hp P hP phi hred)) := by
  intro C L phi hred
  exact native_dual_line_rhs_join013% (nativeDualLineBodyComputeStep0011 p hp P hP phi hred),
        (nativeDualLineBodyComputeStep1011 p hp P hP phi hred),
        (nativeDualLineBodyComputeStep2011 p hp P hP phi hred),
        (nativeDualLineBodyComputeStep3011 p hp P hP phi hred),
        (nativeDualLineBodyComputeStep4011 p hp P hP phi hred),
        (nativeDualLineBodyComputeStep5011 p hp P hP phi hred),
        (nativeDualLineBodyComputeStep6011 p hp P hP phi hred)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineValueJoinInferred014 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
      ∀ hphi : Function.Surjective phi,
      type_of% (native_dual_line_value_join013% (nativeDualLineComputedCompositionHEq011 p hp P hP phi hred hphi),
        (nativeDualLineRhsJoinInferred013 p hp P hP phi hred)) := by
  intro C L phi hred hphi
  exact native_dual_line_value_join013% (nativeDualLineComputedCompositionHEq011 p hp P hP phi hred hphi),
        (nativeDualLineRhsJoinInferred013 p hp P hP phi hred)

meta section
open Lean Meta Elab Tactic

/- Follow actual009's value path2/4 inside source/body propositions. Keep the
RAW final nodes, so cache keys match BEFORE the existing head normalization. -/

/- Check only the observed normalized heads, while certifying exact RAW endpoints. -/
private def nativeDualLineValueShape010 (left right : Expr) : MetaM Unit := do
  let normalizedLeft ← NativeDualLineStructural009.normalizeHead left 8
  let normalizedRight ← NativeDualLineStructural009.normalizeHead right 8
  let appliedLet := match normalizedRight.getAppFn with
    | .letE .. => true
    | _ => false
  unless normalizedLeft.getAppFn.isConstOf ``LinearMap.comp &&
      normalizedLeft.getAppArgs.size == 21 && appliedLet &&
      normalizedRight.getAppArgs.size == 2 do
    throwError "NativeDualLine010 refuses any value beyond comp21/appliedLet2: left arity={normalizedLeft.getAppArgs.size}, right applied-let={appliedLet}, right arity={normalizedRight.getAppArgs.size}."

elab "native_dual_line_value_cut010% " suppliedSource:term ", " suppliedProp:term : term => do
  let sourceType ← nativeDualLineSourceProposition008 suppliedSource
  let values ← nativeDualLineSurjectiveVectors006 suppliedProp
  let left ← nativeDualLineValuePath010 sourceType
  let right ← nativeDualLineValuePath010 values[1]!
  nativeDualLineValueShape010 left right
  if left.hasMVar || left.hasLevelMVar || left.hasLooseBVars || left.hasSorry ||
      right.hasMVar || right.hasLevelMVar || right.hasLooseBVars || right.hasSorry then
    throwError "NativeDualLine010 refuses unresolved/recovery exact composition endpoints."
  logInfo "NativeDualLine010 exact RAW source/body composition nodes retained; existing normalized boundary comp21/appliedLet2; ordinary declaration must certify equality."
  return ← mkHEq left right

elab "native_dual_line_body_values_exact010 " supplied:term " using " suppliedSeed:term ", " suppliedValue:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← Term.elabTerm supplied none (catchExPostpone := false)
    let seed ← Term.elabTerm suppliedSeed none (catchExPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    let source ← instantiateMVars source
    let seed ← instantiateMVars seed
    let sourceType ← instantiateMVars (← inferType source)
    let target ← instantiateMVars (← goal.getType)
    let seedType := (← instantiateMVars (← inferType seed)).consumeMData.headBeta
    let some (_, left, _, right) := seedType.heq?
      | throwError "NativeDualLine009 expected ordinary exact fiber HEq."
    unless left.getAppFn.isConstOf ``Functor.obj && left.getAppArgs.size == 6 &&
        right.getAppFn.isConstOf ``ActualOriginalPositiveTwoFiber && right.getAppArgs.size == 5 do
      throwError "NativeDualLine009 refuses a seed beyond actual Functor.obj6/fiberAlias5."
    if source.hasMVar || source.hasLevelMVar || source.hasLooseBVars || source.hasSorry ||
        seed.hasMVar || seed.hasLevelMVar || seed.hasLooseBVars || seed.hasSorry then
      throwError "NativeDualLine009 refuses unresolved/recovery source or seed."
    let valueSeed ← Term.elabTerm suppliedValue none (catchExPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    let valueSeed ← instantiateMVars valueSeed
    let valueType := (← instantiateMVars (← inferType valueSeed)).consumeMData.headBeta
    let some (_, valueLeft, _, valueRight) := valueType.heq?
      | throwError "NativeDualLine010 expected ordinary exact value HEq."
    nativeDualLineValueShape010 valueLeft valueRight
    if valueSeed.hasMVar || valueSeed.hasLevelMVar || valueSeed.hasLooseBVars || valueSeed.hasSorry then
      throwError "NativeDualLine010 refuses unresolved/recovery exact value seed."
    let valueReverse ← mkHEqSymm valueSeed
    let reverse ← mkHEqSymm seed
    let (heq, state) ←
      (NativeDualLineStructural009.structuralHEq sourceType target
        96 #[] "chart009").run
          { pairs := #[(left, right, seed), (right, left, reverse),
            (valueLeft, valueRight, valueSeed), (valueRight, valueLeft, valueReverse)] }
    let typeProof ← mkEqOfHEq heq
    let proof := mkAppN (mkConst ``Eq.mp [Level.zero]) #[sourceType, target, typeProof, source]
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "NativeDualLine009 refuses unresolved/recovery emitted certificate."
    logInfo m!"NativeDualLine010 exact cached ordinary fiber/value compatibility emitted: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruence steps={state.congrSteps}, binders={state.binderSteps}, unused traversal budget={state.remaining}."
    goal.assign proof
    replaceMainGoal []


end


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineValueSeed014 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
      ∀ hphi : Function.Surjective phi,
        native_dual_line_value_cut010% (nativeDualLineCompositionSurjective004 p hp P hP phi hred hphi),
          (Function.Surjective (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred)) := by
  intro C L phi hred hphi
  exact nativeDualLineValueJoinInferred014 p hp P hP phi hred hphi

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineBodyTypeEq008 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
      ∀ hphi : Function.Surjective phi,
        native_dual_line_body_type_cut008% (nativeDualLineCompositionSurjective004 p hp P hP phi hred hphi),
          (Function.Surjective (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred)) := by
  intro C L phi hred hphi
  have hSelf : (native_dual_line_source_prop008% (nativeDualLineCompositionSurjective004 p hp P hP phi hred hphi)) =
      (native_dual_line_source_prop008% (nativeDualLineCompositionSurjective004 p hp P hP phi hred hphi)) := rfl
  have hFiber : native_dual_line_fiber_cut009% (nativeDualLineCompositionSurjective004 p hp P hP phi hred hphi),
      (Function.Surjective (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred)) := by
    rfl
  have hValue := nativeDualLineValueSeed014 p hp P hP phi hred hphi
  native_dual_line_body_values_exact010 hSelf using hFiber, hValue


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineBodySurjective006 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
      Function.Surjective phi →
        native_dual_line_body_surjective006% (Function.Surjective (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred)) := by
  intro C L phi hred hphi
  have hNative := nativeDualLineCompositionSurjective004 p hp P hP phi hred hphi
  have hTypes := nativeDualLineBodyTypeEq008 p hp P hP phi hred hphi
  exact Eq.mp hTypes hNative

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineDefiningMapEq006 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
      native_dual_line_definition_cut006% (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred) := by
  intro C L phi hred
  native_dual_line_definition_rfl006

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineSurjectivityPropEqInferred006 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
      type_of% (native_dual_line_surjective_transport006% (Function.Surjective (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred)),
        (nativeDualLineDefiningMapEq006 p hp P hP phi hred)) := by
  intro C L phi hred
  exact native_dual_line_surjective_transport006% (Function.Surjective (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred)),
        (nativeDualLineDefiningMapEq006 p hp P hP phi hred)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem actualOriginalPositiveTwoLineFromNativeDualMap_surjective :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r), Function.Surjective phi →
        Function.Surjective (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred) := by
  intro C L phi hred hphi
  have hBody := nativeDualLineBodySurjective006 p hp P hP phi hred hphi
  have hProp := nativeDualLineSurjectivityPropEqInferred006 p hp P hP phi hred
  exact Eq.mp hProp.symm hBody

meta section
open Lean Meta Elab Tactic

/- Follow only the actual004 carrier path, using existing fuel8 head/projection helpers. -/
private def nativeDualLineCarrierPath005 (input : Expr) : Term.TermElabM Expr := do
  let mut current := input
  for index in #[0, 2] do
    current ← NativeDualLineStructural005.normalizeHead current 8
    current ← NativeDualLineStructural005.projectionAsApplication current
    let args := current.getAppArgs
    unless index < args.size do
      throwError "NativeDualLine005 path index{index} exceeds head={current.getAppFn}, arity={args.size}."
    current := args[index]!
  return ← NativeDualLineStructural005.normalizeHead current 8

/- Guards establish exact stored endpoint shapes, not equality. -/
elab "native_dual_line_carrier_cut005% " supplied:term ", " suppliedTarget:term : term => do
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  let target ← Term.elabTerm suppliedTarget (some (mkSort Level.zero)) (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let source ← instantiateMVars source
  let target ← instantiateMVars target
  let sourceType ← instantiateMVars (← inferType source)
  let left ← nativeDualLineCarrierPath005 sourceType
  let right ← nativeDualLineCarrierPath005 target
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless left.getAppFn.isConstOf ``IsLocalRing.ResidueField && la.size == 3 &&
      right.getAppFn.isConstOf ``CommRingCat.carrier && ra.size == 1 do
    throwError "NativeDualLine005 refuses a carrier beyond rawResidueField3/bundledCarrier1: left={left.getAppFn}/{la.size}, right={right.getAppFn}/{ra.size}."
  if left.hasMVar || left.hasLevelMVar || right.hasMVar || right.hasLevelMVar ||
      source.hasMVar || source.hasLevelMVar || source.hasLooseBVars || source.hasSorry ||
      target.hasMVar || target.hasLevelMVar || target.hasLooseBVars || target.hasSorry then
    throwError "NativeDualLine005 refuses unresolved/recovery exact carrier vectors."
  logInfo m!"NativeDualLine005 exact carrier path0/2: raw stalk head={la[0]!.getAppFn}, ring head={la[1]!.getAppFn}, local-ring head={la[2]!.getAppFn}; bundled endpoint head={ra[0]!.getAppFn}."
  return ← mkHEq left right

/- Only the supplied ordinary HEq is inserted into the unchanged existing cache. -/
elab "native_dual_line_carrier_exact005 " supplied:term " using " suppliedSeed:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← Term.elabTerm supplied none (catchExPostpone := false)
    let seed ← Term.elabTerm suppliedSeed none (catchExPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    let source ← instantiateMVars source
    let seed ← instantiateMVars seed
    let sourceType ← instantiateMVars (← inferType source)
    let target ← instantiateMVars (← goal.getType)
    let seedType := (← instantiateMVars (← inferType seed)).consumeMData.headBeta
    let some (_, left, _, right) := seedType.heq?
      | throwError "NativeDualLine005 expected exact ordinary carrier HEq."
    unless left.getAppFn.isConstOf ``IsLocalRing.ResidueField && left.getAppArgs.size == 3 &&
        right.getAppFn.isConstOf ``CommRingCat.carrier && right.getAppArgs.size == 1 do
      throwError "NativeDualLine005 refuses any seed beyond rawResidueField3/bundledCarrier1."
    if source.hasMVar || source.hasLevelMVar || source.hasLooseBVars || source.hasSorry ||
        seed.hasMVar || seed.hasLevelMVar || seed.hasLooseBVars || seed.hasSorry then
      throwError "NativeDualLine005 refuses unresolved/recovery source or seed."
    let reverse ← mkHEqSymm seed
    let (heq, state) ←
      (NativeDualLineStructural005.structuralHEq sourceType target
        96 #[] "chart009").run
          { pairs := #[(left, right, seed), (right, left, reverse)] }
    let typeProof ← mkEqOfHEq heq
    let proof := mkAppN (mkConst ``Eq.mp [Level.zero]) #[sourceType, target, typeProof, source]
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "NativeDualLine005 refuses unresolved/recovery emitted proof."
    logInfo m!"NativeDualLine005 exact cached ordinary carrier compatibility emitted: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruence steps={state.congrSteps}, binders={state.binderSteps}, unused traversal budget={state.remaining}."
    goal.assign proof
    replaceMainGoal []

end


/-- Ordinary abstract cancellation, before any native specialization. -/
private theorem nativeDualLineCancel004
    {S X Y Z : Type u} [CommSemiring S]
    [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid Z]
    [Module S X] [Module S Y] [Module S Z]
    (f : Y →ₗ[S] Z) (E : X ≃ₗ[S] Y) :
    (f.comp E.toLinearMap).comp E.symm.toLinearMap = f := by
  apply LinearMap.ext
  intro x
  exact congrArg f (E.apply_symm_apply x)

/-- Ordinary universal differential evaluation with the original residue algebra. -/
private theorem nativeDualLineResidueEvaluation004
    {A B D : Type u} [Field A] [CommRing B] [Field D]
    [Algebra A B] [Algebra A D] [Algebra B D] [IsScalarTower A B D]
    (phi : B →ₐ[A] DualNumber D)
    (hred : ∀ r, (phi r).fst = algebraMap B D r) (r : B) :
    residueCompatibleActualDualFiberLine phi hred
      (actualResidueDifferentialDerivation (K := A) (R := B) (L := D) r) =
        (phi r).snd := by
  rw [actualResidueDifferentialDerivation_apply,
    residueCompatibleActualDualFiberLine_tmul_D, one_mul]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineCoefficientHeader005
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let R := ChartRing (equationIdeal p hp) C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    actualCubicPositiveTwoOriginalNativePointFiberEquiv (K := K) (L := L) p hp
      ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization
        (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s) =
      actualResidueDifferentialDerivation (K := K) (R := R) (L := L)
        (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s) := by
  intro C R L
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  letI aK : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  letI : SMul K R := aK.toSMul
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun C.base c).symm)
  have hNative := actualOriginalIdealQuadraticPositiveTwoPhi_native_coefficient p hp P hP s
  have hCarrier : native_dual_line_carrier_cut005% hNative,
    (actualCubicPositiveTwoOriginalNativePointFiberEquiv (K := K) (L := L) p hp
        ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization
          (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s) =
      actualResidueDifferentialDerivation (K := K) (R := R) (L := L)
        (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s)) := by
    rfl
  native_dual_line_carrier_exact005 hNative using hCarrier


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem actualOriginalPositiveTwoLineFromNativeDualMap_Phi_coefficient :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r)
      (s : ActualOriginalPointIdealQuadraticSections p hp P),
      actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred
        (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s) =
          (phi (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s)).snd := by
  intro C L
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let R := ChartRing (equationIdeal p hp) C.index
  letI aK : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  letI : SMul K R := aK.toSMul
  intro phi hred s
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun C.base c).symm)
  let E := actualCubicPositiveTwoOriginalNativePointFiberEquiv (K := K) (L := L) p hp
    ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization
  change residueCompatibleActualDualFiberLine phi hred
    (E (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s)) = _
  have hNative := nativeDualLineCoefficientHeader005 p hp P hP s
  run_tac Lean.logInfo "NativeDualLine004.00: isolated-native-coefficient-header-applied"
  have hMapped := congrArg (residueCompatibleActualDualFiberLine phi hred) hNative
  run_tac Lean.logInfo "NativeDualLine004.01: own-coefficient-congruence-inferred"
  have hValue := nativeDualLineResidueEvaluation004 phi hred
    (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s)
  have hJoin := hMapped.trans hValue
  run_tac Lean.logInfo "NativeDualLine004.02: own-coefficient-trans-inferred_before-public-assignment"
  exact hJoin


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineNativeCancellation015 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    letI : Algebra (ChartRing (equationIdeal p hp) C.index) L := C.residue.toAlgebra
    letI : IsScalarTower K (ChartRing (equationIdeal p hp) C.index) L :=
      IsScalarTower.of_algebraMap_eq (fun c => (RingHom.congr_fun C.base c).symm)
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
    let E := actualCubicPositiveTwoOriginalNativePointFiberEquiv (K := K) (L := L) p hp
      ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization;
      ((residueCompatibleActualDualFiberLine phi hred).comp E.toLinearMap).comp E.symm.toLinearMap = residueCompatibleActualDualFiberLine phi hred := by
  intro C L
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let R := ChartRing (equationIdeal p hp) C.index
  letI aK : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  letI : SMul K R := aK.toSMul
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun C.base c).symm)
  intro phi hred E
  exact nativeDualLineCancel004 (residueCompatibleActualDualFiberLine phi hred) E

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineNativeReconstruction015 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    letI : Algebra (ChartRing (equationIdeal p hp) C.index) L := C.residue.toAlgebra
    letI : IsScalarTower K (ChartRing (equationIdeal p hp) C.index) L :=
      IsScalarTower.of_algebraMap_eq (fun c => (RingHom.congr_fun C.base c).symm)
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
    let E := actualCubicPositiveTwoOriginalNativePointFiberEquiv (K := K) (L := L) p hp
      ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization;
      actualKaehlerLineDualAlgebraMap (((residueCompatibleActualDualFiberLine phi hred).comp E.toLinearMap).comp E.symm.toLinearMap) = phi := by
  intro C L
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let R := ChartRing (equationIdeal p hp) C.index
  letI aK : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  letI : SMul K R := aK.toSMul
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun C.base c).symm)
  intro phi hred E
  have hCancel := nativeDualLineNativeCancellation015 p hp P hP phi hred
  have hMapped := congrArg (fun ell => actualKaehlerLineDualAlgebraMap ell) hCancel
  have hReconstruct := residueCompatibleActualDualFiberLine_reconstruct phi hred
  have hJoin := hMapped.trans hReconstruct
  exact hJoin

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineNativeSpecMapLift015 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    letI : Algebra (ChartRing (equationIdeal p hp) C.index) L := C.residue.toAlgebra
    letI : IsScalarTower K (ChartRing (equationIdeal p hp) C.index) L :=
      IsScalarTower.of_algebraMap_eq (fun c => (RingHom.congr_fun C.base c).symm)
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
    let E := actualCubicPositiveTwoOriginalNativePointFiberEquiv (K := K) (L := L) p hp
      ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization;
      Spec.map (CommRingCat.ofHom
        (actualKaehlerLineDualAlgebraMap (((residueCompatibleActualDualFiberLine phi hred).comp E.toLinearMap).comp E.symm.toLinearMap)).toRingHom) ≫
          chartι (equationIdeal p hp) C.index =
        Spec.map (CommRingCat.ofHom phi.toRingHom) ≫ chartι (equationIdeal p hp) C.index := by
  intro C L
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let R := ChartRing (equationIdeal p hp) C.index
  letI aK : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  letI : SMul K R := aK.toSMul
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun C.base c).symm)
  intro phi hred E
  have hAlg := nativeDualLineNativeReconstruction015 p hp P hP phi hred
  have hMapped := congrArg (fun psi : R →ₐ[K] DualNumber L =>
    Spec.map (CommRingCat.ofHom psi.toRingHom) ≫ chartι (equationIdeal p hp) C.index) hAlg
  exact hMapped

meta section
open Lean Meta Elab Tactic

/- Source composition is read from the PASSED native cancellation proposition,
not from a surjectivity proof. No hphi is introduced or assumed. -/
private def nativeDualLineNoSurjCompositionVectors017
    (suppliedCancel suppliedProp : Syntax) : Term.TermElabM (Array Expr) := do
  let proof ← Term.elabTerm suppliedCancel none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  let type ← instantiateMVars (← inferType proof)
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry ||
      type.hasMVar || type.hasLevelMVar || type.hasLooseBVars || type.hasSorry then
    throwError "NativeDualLine017 refuses unresolved/recovery native cancellation source."
  let type ← NativeDualLineStructural009.normalizeHead type 8
  let some (_, cancelled, epsilon) := type.consumeMData.headBeta.eq?
    | throwError "NativeDualLine017 requires the stored ordinary cancellation Eq."
  unless cancelled.getAppFn.isConstOf ``LinearMap.comp && cancelled.getAppArgs.size == 21 &&
      epsilon.getAppFn.isConstOf ``residueCompatibleActualDualFiberLine do
    throwError "NativeDualLine017 requires exact native outer comp21/epsilon-line cancellation endpoints."
  let native := cancelled.getAppArgs[19]!
  let nodes ← nativeDualLineBodyStages011 suppliedProp 7
  let computed := nodes[7]!
  unless native.getAppFn.isConstOf ``LinearMap.comp && native.getAppArgs.size == 21 &&
      computed.getAppFn.isConstOf ``LinearMap.comp && computed.getAppArgs.size == 21 do
    throwError "NativeDualLine017 requires original INNER native comp21 and computed comp21."
  logInfo "NativeDualLine017 actual source INNER comp21 obtained from cancelled outer comp21 slot19; no surjectivity proof or premise."
  return #[native, computed, nodes[0]!]

private def nativeDualLineCompFiberObject017 (comp : Expr) : Term.TermElabM Expr := do
  let carrier ← NativeDualLineStructural009.normalizeHead comp.getAppArgs[3]! 8
  let carrier ← NativeDualLineStructural009.projectionAsApplication carrier
  unless carrier.getAppFn.isConstOf ``ModuleCat.carrier && carrier.getAppArgs.size == 3 do
    throwError "NativeDualLine017 expects exact domain ModuleCat.carrier3 at comp slot3; arity={carrier.getAppArgs.size}."
  return ← NativeDualLineStructural009.normalizeHead carrier.getAppArgs[2]! 8

elab "native_dual_line_nosurj_fiber_cut017% " suppliedCancel:term ", " suppliedProp:term : term => do
  let values ← nativeDualLineNoSurjCompositionVectors017 suppliedCancel suppliedProp
  let left ← nativeDualLineCompFiberObject017 values[0]!
  let right ← nativeDualLineCompFiberObject017 values[1]!
  unless left.getAppFn.isConstOf ``Functor.obj && left.getAppArgs.size == 6 &&
      right.getAppFn.isConstOf ``ActualOriginalPositiveTwoFiber && right.getAppArgs.size == 5 do
    throwError "NativeDualLine017 requires actual Functor.obj6/fiber5 object aliases; left arity={left.getAppArgs.size}, right arity={right.getAppArgs.size}."
  if left.hasMVar || left.hasLevelMVar || left.hasLooseBVars || left.hasSorry ||
      right.hasMVar || right.hasLevelMVar || right.hasLooseBVars || right.hasSorry then
    throwError "NativeDualLine017 refuses unresolved/recovery exact domain objects."
  return ← mkHEq left right

elab "native_dual_line_nosurj_composition_cut017% " suppliedCancel:term ", " suppliedProp:term : term => do
  let values ← nativeDualLineNoSurjCompositionVectors017 suppliedCancel suppliedProp
  return ← mkHEq values[0]! values[1]!

/- The folded public line equality and reverse native/body equality share
exactly the same RAW computed body. All constructors remain ordinary laws. -/
elab "native_dual_line_opaque_line_join017% " suppliedLineEq:term ", " suppliedValue:term : term => do
  let lineEq ← Term.elabTerm suppliedLineEq none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let lineEq ← instantiateMVars lineEq
  let eqType := (← instantiateMVars (← inferType lineEq)).consumeMData.headBeta
  let some (_, original, body) := eqType.eq?
    | throwError "NativeDualLine017 requires ordinary folded-line Eq006."
  let (valueProof, native, valueBody) ← nativeDualLineStoredHEq013 suppliedValue
  unless original.getAppFn.isConstOf ``actualOriginalPositiveTwoLineFromNativeDualMap &&
      original.getAppArgs.size == 9 && native.getAppFn.isConstOf ``LinearMap.comp && native.getAppArgs.size == 21 do
    throwError "NativeDualLine017 requires opaque original line9/native composition21."
  unless body.equal valueBody do
    throwError "NativeDualLine017 refuses different RAW body nodes between folded-line Eq and ordinary native/body HEq."
  let proof ← mkHEqTrans (← mkHEqOfEq lineEq) (← mkHEqSymm valueProof)
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeDualLine017 refuses unresolved/recovery opaque line/native composition join."
  logInfo "NativeDualLine017 ordinary opaque original line9→native composition21 joined with exact raw body midpoint, without hphi."
  return proof

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineNoSurjFiberSeed017 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
      native_dual_line_nosurj_fiber_cut017% (nativeDualLineNativeCancellation015 p hp P hP phi hred),
          (Function.Surjective (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred)) := by
  intro C L phi hred
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineNoSurjComputedComposition017 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
      native_dual_line_nosurj_composition_cut017% (nativeDualLineNativeCancellation015 p hp P hP phi hred),
          (Function.Surjective (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred)) := by
  intro C L phi hred
  have hFiber := nativeDualLineNoSurjFiberSeed017 p hp P hP phi hred
  native_dual_line_computed_exact011 using hFiber

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineNoSurjValueJoinInferred017 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
      type_of% (native_dual_line_value_join013% (nativeDualLineNoSurjComputedComposition017 p hp P hP phi hred),
        (nativeDualLineRhsJoinInferred013 p hp P hP phi hred)) := by
  intro C L phi hred
  exact native_dual_line_value_join013% (nativeDualLineNoSurjComputedComposition017 p hp P hP phi hred),
        (nativeDualLineRhsJoinInferred013 p hp P hP phi hred)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineOpaqueNativeLineInferred017 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
      type_of% (native_dual_line_opaque_line_join017% (nativeDualLineDefiningMapEq006 p hp P hP phi hred),
        (nativeDualLineNoSurjValueJoinInferred017 p hp P hP phi hred)) := by
  intro C L phi hred
  exact native_dual_line_opaque_line_join017% (nativeDualLineDefiningMapEq006 p hp P hP phi hred),
        (nativeDualLineNoSurjValueJoinInferred017 p hp P hP phi hred)

meta section
open Lean Meta Elab Tactic

/- Exactly one ORIGINAL embedding-producer delta, retaining its local lets. -/
private def nativeDualLineEmbeddingVectors016 (supplied : Syntax) : Term.TermElabM (Expr × Expr) := do
  let original ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let original ← instantiateMVars original
  let args := original.getAppArgs
  unless original.getAppFn.isConstOf ``actualOriginalPositiveTwoNativeJetEmbedding && args.size == 8 do
    throwError "NativeDualLine016 expects original opaque embedding8; actual arity={args.size}."
  let line := args[7]!
  unless line.getAppFn.isConstOf ``actualOriginalPositiveTwoLineFromNativeDualMap && line.getAppArgs.size == 9 do
    throwError "NativeDualLine016 expects SAME opaque original line9 at embedding slot7; actual arity={line.getAppArgs.size}."
  let some expanded ← delta? original (fun n => n == ``actualOriginalPositiveTwoNativeJetEmbedding)
    | throwError "NativeDualLine016 cannot take the single original embedding delta."
  if original.hasMVar || original.hasLevelMVar || original.hasLooseBVars || original.hasSorry ||
      expanded.hasMVar || expanded.hasLevelMVar || expanded.hasLooseBVars || expanded.hasSorry then
    throwError "NativeDualLine016 refuses unresolved/recovery opaque embedding endpoints."
  logInfo "NativeDualLine016 original embedding8/line9 exact stored vector; one producer delta only, local lets retained."
  return (original, expanded)

elab "native_dual_line_embedding_definition_cut016% " supplied:term : term => do
  let (original, expanded) ← nativeDualLineEmbeddingVectors016 supplied
  return ← mkEq original expanded

elab "native_dual_line_embedding_definition_rfl016" : tactic => withMainContext do
  let goal ← getMainGoal
  let type := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
  let some (_, original, target) := type.eq?
    | throwError "NativeDualLine016 expects the stored one-delta embedding Eq."
  let args := original.getAppArgs
  unless original.getAppFn.isConstOf ``actualOriginalPositiveTwoNativeJetEmbedding && args.size == 8 &&
      args[7]!.getAppFn.isConstOf ``actualOriginalPositiveTwoLineFromNativeDualMap && args[7]!.getAppArgs.size == 9 do
    throwError "NativeDualLine016 refuses a different embedding/line under the defining Eq."
  let some expanded ← delta? original (fun n => n == ``actualOriginalPositiveTwoNativeJetEmbedding)
    | throwError "NativeDualLine016 cannot retrieve the single original embedding delta."
  unless target.equal expanded do
    throwError "NativeDualLine016 refuses different stored defining-body endpoints."
  logInfo "NativeDualLine016 ordinary rfl for exactly one original embedding delta; kernel checks its original local let telescope."
  goal.assign (← mkEqRefl original)
  replaceMainGoal []

/- Lift the ALREADY CHECKED folded-line equality through the SAME opaque
embedding application vector, WITHOUT unfolding the embedding producer. -/
elab "native_dual_line_embedding_line_lift016% " suppliedEmbedding:term ", " suppliedLineEq:term : term => do
  let embedding ← Term.elabTerm suppliedEmbedding none (catchExPostpone := false)
  let lineEq ← Term.elabTerm suppliedLineEq none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let embedding ← instantiateMVars embedding
  let lineEq ← instantiateMVars lineEq
  let args := embedding.getAppArgs
  unless embedding.getAppFn.isConstOf ``actualOriginalPositiveTwoNativeJetEmbedding && args.size == 8 do
    throwError "NativeDualLine016 expects the unchanged opaque embedding8 vector for congrArg."
  let eqType := (← instantiateMVars (← inferType lineEq)).consumeMData.headBeta
  let some (_, originalLine, _) := eqType.eq?
    | throwError "NativeDualLine016 requires the checked folded-line Eq006."
  unless args[7]!.equal originalLine do
    throwError "NativeDualLine016 refuses a different raw opaque original line under the embedding vector."
  if embedding.hasMVar || embedding.hasLevelMVar || embedding.hasLooseBVars || embedding.hasSorry ||
      lineEq.hasMVar || lineEq.hasLevelMVar || lineEq.hasLooseBVars || lineEq.hasSorry then
    throwError "NativeDualLine016 refuses unresolved/recovery embedding-line transport inputs."
  let predicate ← withLocalDeclD `line (← inferType originalLine) fun line => do
    mkLambdaFVars #[line] (mkAppN embedding.getAppFn (args.set! 7 line))
  let proof ← mkCongrArg predicate lineEq
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeDualLine016 refuses unresolved/recovery embedding-line congrArg."
  logInfo "NativeDualLine016 ordinary congrArg through exact stored opaque embedding8; line006 raw endpoint guard passed."
  return proof

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineEmbeddingDefiningMapEq016 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
      native_dual_line_embedding_definition_cut016% (actualOriginalPositiveTwoNativeJetEmbedding p hp P hP
          (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred)) := by
  intro C L phi hred
  native_dual_line_embedding_definition_rfl016


meta section
open Lean Meta Elab Tactic

/- Expose only the TYPE head of a checked ordinary equality, including its
single native E let. Endpoints themselves stay exactly as stored. -/
private def nativeDualLineStoredEq018 (supplied : Syntax) : Term.TermElabM (Expr × Expr × Expr) := do
  let proof ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  let type ← instantiateMVars (← inferType proof)
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry ||
      type.hasMVar || type.hasLevelMVar || type.hasLooseBVars || type.hasSorry then
    throwError "NativeDualLine018 refuses unresolved/recovery ordinary stored Eq."
  let type ← NativeDualLineStructural009.normalizeHead type 8
  let some (_, left, right) := type.consumeMData.headBeta.eq?
    | throwError "NativeDualLine018 requires ordinary stored Eq endpoints."
  return (proof, left, right)

elab "native_dual_line_embedding_body_cut018% " suppliedDelta:term ", " suppliedNative:term : term => do
  let (_, original, body) ← nativeDualLineStoredEq018 suppliedDelta
  let (_, native, _) ← nativeDualLineStoredEq018 suppliedNative
  unless original.getAppFn.isConstOf ``actualOriginalPositiveTwoNativeJetEmbedding &&
      original.getAppArgs.size == 8 &&
      original.getAppArgs[7]!.getAppFn.isConstOf ``actualOriginalPositiveTwoLineFromNativeDualMap &&
      original.getAppArgs[7]!.getAppArgs.size == 9 do
    throwError "NativeDualLine018 requires actual original embedding8/opaque line9 from the checked single delta."
  let normalizedBody ← NativeDualLineStructural009.normalizeHead body 8
  let normalizedNative ← NativeDualLineStructural009.normalizeHead native 8
  logInfo m!"NativeDualLine018 exact RAW embedding body/native SpecMap endpoints retained; normalized arities={normalizedBody.getAppArgs.size}/{normalizedNative.getAppArgs.size}, raw same={body.equal native}."
  return ← mkHEq body native

elab "native_dual_line_embedding_body_exact018 " "using " suppliedLine:term ", " suppliedFiber:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
    let some (_, body, _, native) := target.heq?
      | throwError "NativeDualLine018 expects stored ordinary body/native map HEq."
    let (lineProof, lineLeft, lineRight) ← nativeDualLineStoredHEq013 suppliedLine
    let (fiberProof, fiberLeft, fiberRight) ← nativeDualLineStoredHEq013 suppliedFiber
    unless lineLeft.getAppFn.isConstOf ``actualOriginalPositiveTwoLineFromNativeDualMap && lineLeft.getAppArgs.size == 9 &&
        lineRight.getAppFn.isConstOf ``LinearMap.comp && lineRight.getAppArgs.size == 21 do
      throwError "NativeDualLine018 requires the PASSED exact opaque-line9/native-comp21 seed."
    unless fiberLeft.getAppFn.isConstOf ``Functor.obj && fiberLeft.getAppArgs.size == 6 &&
        fiberRight.getAppFn.isConstOf ``ActualOriginalPositiveTwoFiber && fiberRight.getAppArgs.size == 5 do
      throwError "NativeDualLine018 requires PASSED exact native domain object/fiber alias seed."
    let lineReverse ← mkHEqSymm lineProof
    let fiberReverse ← mkHEqSymm fiberProof
    let (proof, state) ←
      (NativeDualLineStructural009.structuralHEq body native 96 #[] "chart009").run
        { pairs := #[(lineLeft, lineRight, lineProof), (lineRight, lineLeft, lineReverse),
            (fiberLeft, fiberRight, fiberProof), (fiberRight, fiberLeft, fiberReverse)] }
    let proof ← instantiateMVars proof
    if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "NativeDualLine018 refuses unresolved/recovery body/native compatibility proof."
    logInfo m!"NativeDualLine018 ordinary retained embedding-body compatibility emitted: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruence steps={state.congrSteps}, binders={state.binderSteps}, unused traversal budget={state.remaining}."
    goal.assign proof
    replaceMainGoal []

/- Ordinary typed endpoint transport. Infer each stored vector separately and
refuse raw midpoint changes, before constructing HEq.ofEq/symm/trans terms. -/
elab "native_dual_line_embedding_join018% " suppliedDelta:term ", " suppliedBody:term ", " suppliedNative:term : term => do
  let (deltaProof, _, deltaBody) ← nativeDualLineStoredEq018 suppliedDelta
  let (bodyProof, bodyLeft, bodyRight) ← nativeDualLineStoredHEq013 suppliedBody
  let (nativeProof, nativeLeft, _) ← nativeDualLineStoredEq018 suppliedNative
  unless deltaBody.equal bodyLeft && bodyRight.equal nativeLeft do
    throwError "NativeDualLine018 refuses different RAW stored body/native transport midpoints."
  let proof ← mkHEqTrans (← mkHEqTrans (← mkHEqOfEq deltaProof) bodyProof) (← mkHEqOfEq nativeProof)
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeDualLine018 refuses unresolved/recovery ordinary public endpoint transport."
  logInfo "NativeDualLine018 original opaque embedding transported through retained body and checked native SpecMap; both raw midpoint checks passed."
  return proof

elab "native_dual_line_embedding_eq018% " supplied:term : term => do
  let (proof, _, _) ← nativeDualLineStoredHEq013 supplied
  let proof ← mkEqOfHEq proof
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeDualLine018 refuses unresolved/recovery ordinary Eq-of-HEq proof."
  logInfo "NativeDualLine018 ordinary Eq-of-HEq inferred at its stored original Hom type; declaration kernel remains authoritative."
  return proof

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineEmbeddingBodyHEq018 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
      native_dual_line_embedding_body_cut018% (nativeDualLineEmbeddingDefiningMapEq016 p hp P hP phi hred),
        (nativeDualLineNativeSpecMapLift015 p hp P hP phi hred) := by
  intro C L phi hred
  have hLine := nativeDualLineOpaqueNativeLineInferred017 p hp P hP phi hred
  have hFiber := nativeDualLineNoSurjFiberSeed017 p hp P hP phi hred
  native_dual_line_embedding_body_exact018 using hLine, hFiber

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineEmbeddingJoinInferred018 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
      type_of% (native_dual_line_embedding_join018% (nativeDualLineEmbeddingDefiningMapEq016 p hp P hP phi hred),
        (nativeDualLineEmbeddingBodyHEq018 p hp P hP phi hred),
        (nativeDualLineNativeSpecMapLift015 p hp P hP phi hred)) := by
  intro C L phi hred
  exact native_dual_line_embedding_join018% (nativeDualLineEmbeddingDefiningMapEq016 p hp P hP phi hred),
        (nativeDualLineEmbeddingBodyHEq018 p hp P hP phi hred),
        (nativeDualLineNativeSpecMapLift015 p hp P hP phi hred)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeDualLineEmbeddingEqInferred018 :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
      type_of% (native_dual_line_embedding_eq018% (nativeDualLineEmbeddingJoinInferred018 p hp P hP phi hred)) := by
  intro C L phi hred
  exact native_dual_line_embedding_eq018% (nativeDualLineEmbeddingJoinInferred018 p hp P hP phi hred)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem actualOriginalPositiveTwoLineFromNativeDualMap_embedding :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ∀ (phi : ChartRing (equationIdeal p hp) C.index →ₐ[K] DualNumber L)
      (hred : ∀ r, (phi r).fst = C.residue r),
      actualOriginalPositiveTwoNativeJetEmbedding p hp P hP
        (actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred) =
          Spec.map (CommRingCat.ofHom phi.toRingHom) ≫ chartι (equationIdeal p hp) C.index := by
  intro C L phi hred
  exact nativeDualLineEmbeddingEqInferred018 p hp P hP phi hred

end
end PfaffianDescent
