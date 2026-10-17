import PfaffianDescent.ActualOriginalPositiveTwoNativeJetEmbedding
import PfaffianDescent.SubmoduleKernelThroughLinearEquiv

namespace NativeHZeroCoercion011
open CategoryTheory
universe u v

/- The diagnosed ModuleCat wrapper is precisely its declared concrete hom.
This is a genuine ordinary data equality, checked by the enclosing kernel. -/
private theorem module_hom_eq_concrete
    {R : Type u} [Ring R] {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    f.hom = ConcreteCategory.hom (C := ModuleCat.{v} R) f := by
  rfl

end NativeHZeroCoercion011

noncomputable section
namespace NativeHZeroResidue011
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

end NativeHZeroResidue011
end

namespace NativeHZeroStructural011

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

end NativeHZeroStructural011

meta section
namespace NativeHZeroStructural011
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
  let proof := mkAppN (mkConst ``NativeHZeroResidue011.native_commRing_eq levels) fieldArgs
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
  let proof := mkAppN (mkConst ``NativeHZeroResidue011.native_bundle_eq levels) ra
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
  let proof := mkAppN (mkConst ``NativeHZeroResidue011.native_carrier_eq levels) nativeArgs
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
  let proof := mkAppN (mkConst ``NativeHZeroResidue011.native_field_heq levels) la
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
  let proof := mkAppN (mkConst ``NativeHZeroResidue011.native_standard_bundle_eq levels) ra
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

end NativeHZeroStructural011
end

/- SOURCE ONLY / UNVERIFIED. Exact genuine H0(I_Z(2)) is the kernel of
ell o Phi for the SAME actual original residue/point/native O(2) generator.
The full scheme kernel, including nilpotents, is used in both directions.
This does not claim the still-pending global conormal/chart independence. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Ordinary standalone projection law; actual caller uses its stored endpoints. -/
private theorem nativeDualNumberSemiringProjection011 (L : Type u) [Field L] :
    (@TrivSqZeroExt.semiring L L inferInstance inferInstance inferInstance
      inferInstance inferInstance) =
    (@CommSemiring.toSemiring (DualNumber L)
      (@CommRing.toCommSemiring (DualNumber L) inferInstance)) := by
  rfl

/-- The exact original stalk/residue carrier, with ring and local-ring vectors. -/
private theorem nativeOriginalResidueCarrier013 (S : Scheme.{u}) (x : S) :
    @IsLocalRing.ResidueField (CommRingCat.carrier (S.presheaf.stalk x))
      (@CommRingCat.instCommRingObjForgetRingHomCarrier (S.presheaf.stalk x))
      (inferInstance : IsLocalRing (S.presheaf.stalk x)) =
    CommRingCat.carrier (S.residueField x) := by
  rfl

/-- One ordinary alias equality for the original, unaltered positive-two fiber. -/
private theorem nativeOriginalPositiveTwoFiberAlias014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp)) :
    (moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (actualCubicPositiveTwoDifferentials p hp)) =
    ActualOriginalPositiveTwoFiber p hp P := by
  rfl

/-- Ordinary same-DualNumber zero projection law; actual seed uses its stored vectors. -/
private theorem nativeDualNumberZeroProjection015 (L : Type u) [Field L] :
    (@TrivSqZeroExt.zero L L inferInstance inferInstance) =
    (@MulZeroClass.toZero (DualNumber L) inferInstance) := by
  rfl

meta section
open Lean Meta Elab Tactic

/-- Extract only the diagnosed native codomain semiring beneath RingHom4. -/
private def nativeHZeroStoredSemiring011 (expression : Expr) : Term.TermElabM Expr := do
  let expression := expression.consumeMData.headBeta
  let some (_, value, _) := expression.eq?
    | throwError "NativeHZero011 expected the exact evaluation equality."
  let value := value.consumeMData.headBeta
  let va := value.getAppArgs
  unless value.getAppFn.isConstOf ``DFunLike.coe && va.size == 6 do
    throwError "NativeHZero011 expected exact DFunLike.coe6 evaluation."
  let homType := va[0]!.consumeMData.headBeta
  let ha := homType.getAppArgs
  unless homType.getAppFn.isConstOf ``RingHom && ha.size == 4 do
    throwError "NativeHZero011 expected exact RingHom4 type."
  let parent := ha[3]!.consumeMData.headBeta
  let pa := parent.getAppArgs
  unless parent.getAppFn.isConstOf ``Semiring.toNonAssocSemiring && pa.size == 2 do
    throwError "NativeHZero011 expected the diagnosed codomain Semiring.toNonAssocSemiring2 projection; head={parent.getAppFn}, arity={pa.size}."
  return pa[1]!

/-- Actual semiring endpoints are inferred from hjoin and hmem, rather than
reconstructed from phi in a different expected RingHom dictionary. -/
elab "native_hzero_semiring_cut011% " suppliedJoin:term ", " suppliedMem:term : term => do
  let join ← Term.elabTerm suppliedJoin none (catchExPostpone := false)
  let mem ← Term.elabTerm suppliedMem none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let join ← instantiateMVars join
  let mem ← instantiateMVars mem
  let jt := (← instantiateMVars (← inferType join)).consumeMData.headBeta
  let mt := (← instantiateMVars (← inferType mem)).consumeMData.headBeta
  let ja := jt.getAppArgs
  let ma := mt.getAppArgs
  unless jt.getAppFn.isConstOf ``Iff && mt.getAppFn.isConstOf ``Iff &&
      ja.size == 2 && ma.size == 2 do
    throwError "NativeHZero011 expected exact inferred join and existing membership Iffs."
  let sourceAnd := ja[0]!.consumeMData.headBeta
  let targetAnd := ma[1]!.consumeMData.headBeta
  let sa := sourceAnd.getAppArgs
  let ta := targetAnd.getAppArgs
  unless sourceAnd.getAppFn.isConstOf ``And && targetAnd.getAppFn.isConstOf ``And &&
      sa.size == 2 && ta.size == 2 do
    throwError "NativeHZero011 expected the exact homogeneous/evaluation conjunctions."
  let left ← nativeHZeroStoredSemiring011 sa[1]!
  let right ← nativeHZeroStoredSemiring011 ta[1]!
  unless left.getAppFn.isConstOf ``TrivSqZeroExt.semiring && left.getAppArgs.size == 7 &&
      right.getAppFn.isConstOf ``CommSemiring.toSemiring && right.getAppArgs.size == 2 do
    throwError "NativeHZero011 expected only the actual TrivSqZeroExt.semiring7/CommSemiring.toSemiring2 boundary; left={left.getAppFn}, right={right.getAppFn}."
  if left.hasMVar || left.hasLevelMVar || right.hasMVar || right.hasLevelMVar ||
      join.hasSorry || mem.hasSorry then
    throwError "NativeHZero011 refuses unresolved/recovery endpoints."
  logInfo "NativeHZero011 exact stored source/target DualNumber semiring endpoints extracted; no dictionary equality assumed."
  return ← mkHEq left right

/-- Follow only the ACTUAL012 diagnosed node path, using the unchanged checker
head/projection helpers and the same fuel8 at each stored node. -/
private def nativeHZeroCarrierPath013 (input : Expr) : Term.TermElabM Expr := do
  let mut current := input
  for index in #[1, 1, 4, 8, 8, 1] do
    current ← NativeHZeroStructural011.normalizeHead current 8
    current ← NativeHZeroStructural011.projectionAsApplication current
    let args := current.getAppArgs
    unless index < args.size do
      throwError "NativeHZero013 diagnosed path index{index} exceeds actual head={current.getAppFn}, arity={args.size}."
    current := args[index]!
  return ← NativeHZeroStructural011.normalizeHead current 8

/-- The ordinary carrier seed has the exact stored native stalk/ring/point
arguments, not a reconstructed or generalized residue field. -/
elab "native_hzero_carrier_cut013% " suppliedJoin:term ", " suppliedMem:term : term => do
  let join ← Term.elabTerm suppliedJoin none (catchExPostpone := false)
  let mem ← Term.elabTerm suppliedMem none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let join ← instantiateMVars join
  let mem ← instantiateMVars mem
  let jt := (← instantiateMVars (← inferType join)).consumeMData.headBeta
  let mt := (← instantiateMVars (← inferType mem)).consumeMData.headBeta
  let ja := jt.getAppArgs
  let ma := mt.getAppArgs
  unless jt.getAppFn.isConstOf ``Iff && mt.getAppFn.isConstOf ``Iff &&
      ja.size == 2 && ma.size == 2 do
    throwError "NativeHZero013 expected exact inferred join and existing membership Iffs."
  let left ← nativeHZeroCarrierPath013 ja[0]!
  let right ← nativeHZeroCarrierPath013 ma[1]!
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless left.getAppFn.isConstOf ``IsLocalRing.ResidueField && la.size == 3 &&
      right.getAppFn.isConstOf ``CommRingCat.carrier && ra.size == 1 do
    throwError "NativeHZero013 refuses any seed beyond actual rawResidueField3/bundledCarrier1; left={left.getAppFn}, arity={la.size}, right={right.getAppFn}, arity={ra.size}."
  if left.hasMVar || left.hasLevelMVar || right.hasMVar || right.hasLevelMVar ||
      join.hasSorry || mem.hasSorry then
    throwError "NativeHZero013 refuses unresolved/recovery exact carrier vectors."
  logInfo m!"NativeHZero013 exact original residue carrier nodes extracted: stalk carrier head={la[0]!.getAppFn}, ring head={la[1]!.getAppFn}, local-ring head={la[2]!.getAppFn}; bundled object head={ra[0]!.getAppFn}."
  return ← mkHEq left right

/-- Follow only the actual013 native fiber alias path, with existing head helpers. -/
private def nativeHZeroFiberPath014 (input : Expr) : Term.TermElabM Expr := do
  let mut current := input
  for index in #[1, 1, 4, 8, 10, 4, 2] do
    current ← NativeHZeroStructural011.normalizeHead current 8
    current ← NativeHZeroStructural011.projectionAsApplication current
    let args := current.getAppArgs
    unless index < args.size do
      throwError "NativeHZero014 diagnosed path index{index} exceeds actual head={current.getAppFn}, arity={args.size}."
    current := args[index]!
  return ← NativeHZeroStructural011.normalizeHead current 8

/-- The seed retains the stored actual point, pullback, positive twist and residue
module dictionaries; no equivalence map or dictionary is generalized. -/
elab "native_hzero_fiber_cut014% " suppliedJoin:term ", " suppliedMem:term : term => do
  let join ← Term.elabTerm suppliedJoin none (catchExPostpone := false)
  let mem ← Term.elabTerm suppliedMem none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let join ← instantiateMVars join
  let mem ← instantiateMVars mem
  let jt := (← instantiateMVars (← inferType join)).consumeMData.headBeta
  let mt := (← instantiateMVars (← inferType mem)).consumeMData.headBeta
  let ja := jt.getAppArgs
  let ma := mt.getAppArgs
  unless jt.getAppFn.isConstOf ``Iff && mt.getAppFn.isConstOf ``Iff &&
      ja.size == 2 && ma.size == 2 do
    throwError "NativeHZero014 expected exact inferred join and existing membership Iffs."
  let left ← nativeHZeroFiberPath014 ja[0]!
  let right ← nativeHZeroFiberPath014 ma[1]!
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless left.getAppFn.isConstOf ``Functor.obj && la.size == 6 &&
      right.getAppFn.isConstOf ``ActualOriginalPositiveTwoFiber && ra.size == 5 do
    throwError "NativeHZero014 refuses any seed beyond actual Functor.obj6/OriginalPositiveTwoFiber5; left={left.getAppFn}, arity={la.size}, right={right.getAppFn}, arity={ra.size}."
  if left.hasMVar || left.hasLevelMVar || right.hasMVar || right.hasLevelMVar ||
      join.hasSorry || mem.hasSorry then
    throwError "NativeHZero014 refuses unresolved/recovery exact fiber alias vectors."
  logInfo m!"NativeHZero014 exact original fiber alias nodes extracted: functor head={la[4]!.getAppFn}, object head={la[5]!.getAppFn}; original alias K/field/p/hp/P vector retained5."
  return ← mkHEq left right

/-- Follow only actual014's zero-instance node, with existing head helpers. -/
private def nativeHZeroZeroPath015 (input : Expr) : Term.TermElabM Expr := do
  let mut current := input
  for index in #[1, 2, 2, 1] do
    current ← NativeHZeroStructural011.normalizeHead current 8
    current ← NativeHZeroStructural011.projectionAsApplication current
    let args := current.getAppArgs
    unless index < args.size do
      throwError "NativeHZero015 diagnosed path index{index} exceeds actual head={current.getAppFn}, arity={args.size}."
    current := args[index]!
  return ← NativeHZeroStructural011.normalizeHead current 8

/-- Preserve the exact original native field and zero instance dictionaries. -/
elab "native_hzero_zero_cut015% " suppliedJoin:term ", " suppliedMem:term : term => do
  let join ← Term.elabTerm suppliedJoin none (catchExPostpone := false)
  let mem ← Term.elabTerm suppliedMem none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let join ← instantiateMVars join
  let mem ← instantiateMVars mem
  let jt := (← instantiateMVars (← inferType join)).consumeMData.headBeta
  let mt := (← instantiateMVars (← inferType mem)).consumeMData.headBeta
  let ja := jt.getAppArgs
  let ma := mt.getAppArgs
  unless jt.getAppFn.isConstOf ``Iff && mt.getAppFn.isConstOf ``Iff &&
      ja.size == 2 && ma.size == 2 do
    throwError "NativeHZero015 expected exact inferred join and existing membership Iffs."
  let left ← nativeHZeroZeroPath015 ja[0]!
  let right ← nativeHZeroZeroPath015 ma[1]!
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless left.getAppFn.isConstOf ``TrivSqZeroExt.zero && la.size == 4 &&
      right.getAppFn.isConstOf ``MulZeroClass.toZero && ra.size == 2 do
    throwError "NativeHZero015 refuses any seed beyond actual TrivSqZeroExt.zero4/MulZeroClass.toZero2; left={left.getAppFn}, arity={la.size}, right={right.getAppFn}, arity={ra.size}."
  if left.hasMVar || left.hasLevelMVar || right.hasMVar || right.hasLevelMVar ||
      join.hasSorry || mem.hasSorry then
    throwError "NativeHZero015 refuses unresolved/recovery exact zero vectors."
  logInfo m!"NativeHZero015 exact original DualNumber zero nodes extracted: native base/ideal carriers={la[0]!.getAppFn}/{la[1]!.getAppFn}; right carrier={ra[0]!.getAppFn}, dictionary={ra[1]!.getAppFn}."
  return ← mkHEq left right

/-- Existing exact checker algorithm and bounds, with only an ordinary exact
semiring equality and its reverse added through the existing cache mechanism. -/
elab "native_hzero_prop_seeded011 " supplied:term " using " suppliedSeed:term ", " suppliedCarrier:term ", " suppliedFiber:term ", " suppliedZero:term : tactic => do
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
      | throwError "NativeHZero011 expected an ordinary exact stored semiring HEq seed."
    unless left.getAppFn.isConstOf ``TrivSqZeroExt.semiring && left.getAppArgs.size == 7 &&
        right.getAppFn.isConstOf ``CommSemiring.toSemiring && right.getAppArgs.size == 2 do
      throwError "NativeHZero011 refuses any seed beyond the diagnosed semiring projection boundary."
    if source.hasMVar || source.hasLevelMVar || source.hasLooseBVars || source.hasSorry ||
        seed.hasMVar || seed.hasLevelMVar || seed.hasLooseBVars || seed.hasSorry then
      throwError "NativeHZero011 refuses unresolved/recovery source or seed."
    let carrierSeed ← Term.elabTerm suppliedCarrier none (catchExPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    let carrierSeed ← instantiateMVars carrierSeed
    let carrierType := (← instantiateMVars (← inferType carrierSeed)).consumeMData.headBeta
    let some (_, carrierLeft, _, carrierRight) := carrierType.heq?
      | throwError "NativeHZero013 expected ordinary exact original carrier HEq."
    unless carrierLeft.getAppFn.isConstOf ``IsLocalRing.ResidueField && carrierLeft.getAppArgs.size == 3 &&
        carrierRight.getAppFn.isConstOf ``CommRingCat.carrier && carrierRight.getAppArgs.size == 1 do
      throwError "NativeHZero013 refuses any carrier seed beyond the diagnosed exact native boundary."
    if carrierSeed.hasMVar || carrierSeed.hasLevelMVar || carrierSeed.hasLooseBVars || carrierSeed.hasSorry then
      throwError "NativeHZero013 refuses unresolved/recovery carrier seed."
    let fiberSeed ← Term.elabTerm suppliedFiber none (catchExPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    let fiberSeed ← instantiateMVars fiberSeed
    let fiberType := (← instantiateMVars (← inferType fiberSeed)).consumeMData.headBeta
    let some (_, fiberLeft, _, fiberRight) := fiberType.heq?
      | throwError "NativeHZero014 expected ordinary exact original fiber alias HEq."
    unless fiberLeft.getAppFn.isConstOf ``Functor.obj && fiberLeft.getAppArgs.size == 6 &&
        fiberRight.getAppFn.isConstOf ``ActualOriginalPositiveTwoFiber && fiberRight.getAppArgs.size == 5 do
      throwError "NativeHZero014 refuses any fiber seed beyond the diagnosed actual alias boundary."
    if fiberSeed.hasMVar || fiberSeed.hasLevelMVar || fiberSeed.hasLooseBVars || fiberSeed.hasSorry then
      throwError "NativeHZero014 refuses unresolved/recovery fiber seed."
    let zeroSeed ← Term.elabTerm suppliedZero none (catchExPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    let zeroSeed ← instantiateMVars zeroSeed
    let zeroType := (← instantiateMVars (← inferType zeroSeed)).consumeMData.headBeta
    let some (_, zeroLeft, _, zeroRight) := zeroType.heq?
      | throwError "NativeHZero015 expected ordinary exact original zero instance HEq."
    unless zeroLeft.getAppFn.isConstOf ``TrivSqZeroExt.zero && zeroLeft.getAppArgs.size == 4 &&
        zeroRight.getAppFn.isConstOf ``MulZeroClass.toZero && zeroRight.getAppArgs.size == 2 do
      throwError "NativeHZero015 refuses any zero seed beyond the diagnosed actual projection boundary."
    if zeroSeed.hasMVar || zeroSeed.hasLevelMVar || zeroSeed.hasLooseBVars || zeroSeed.hasSorry then
      throwError "NativeHZero015 refuses unresolved/recovery zero seed."
    let reverse ← mkHEqSymm seed
    let carrierReverse ← mkHEqSymm carrierSeed
    let fiberReverse ← mkHEqSymm fiberSeed
    let zeroReverse ← mkHEqSymm zeroSeed
    let (heq, state) ←
      (NativeHZeroStructural011.structuralHEq sourceType target
        96 #[] "chart009").run
          { pairs := #[(left, right, seed), (right, left, reverse),
            (carrierLeft, carrierRight, carrierSeed), (carrierRight, carrierLeft, carrierReverse),
            (fiberLeft, fiberRight, fiberSeed), (fiberRight, fiberLeft, fiberReverse),
            (zeroLeft, zeroRight, zeroSeed), (zeroRight, zeroLeft, zeroReverse)] }
    let typeProof ← mkEqOfHEq heq
    let proof := mkAppN (mkConst ``Eq.mp [Level.zero])
      #[sourceType, target, typeProof, source]
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "NativeHZero011 refuses unresolved/recovery emitted proof."
    logInfo m!"NativeHZero011 exact cached ordinary semiring seed compatibility emitted: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruence steps={state.congrSteps}, binders={state.binderSteps}, unused traversal budget={state.remaining}."
    goal.assign proof
    replaceMainGoal []

end

meta section
open Lean Meta Elab Tactic

/-- Bounded diagnostics print only stored heads/arity and immediate raw matches. -/
private def nativeHZeroHead005 (input : Expr) : MetaM String := do
  let head := input.consumeMData.headBeta.getAppFn
  if let .const name _ := head then return name.toString
  if let .fvar id := head then return "local:" ++ (← id.getDecl).userName.toString
  return "nonconstant-head"

/-- The final target is transported by an explicit ordinary proposition equality.
No source or target dictionary is unfolded and no equality is assumed from guards. -/
elab "native_hzero_join_transport005 " supplied:term " using " suppliedSeed:term ", " suppliedCarrier:term ", " suppliedFiber:term ", " suppliedZero:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← Term.elabTerm supplied none (catchExPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    let source ← instantiateMVars source
    let sourceType := (← instantiateMVars (← inferType source)).consumeMData.headBeta
    let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
    if source.hasMVar || source.hasLevelMVar || source.hasLooseBVars || source.hasSorry ||
        sourceType.hasMVar || sourceType.hasLevelMVar || target.hasMVar || target.hasLevelMVar then
      throwError "NativeHZero005 refuses unresolved/recovery source or proposition."
    let sa := sourceType.getAppArgs
    let ta := target.getAppArgs
    logInfo m!"NativeHZero005 stored source/target heads={← nativeHZeroHead005 sourceType}/{← nativeHZeroHead005 target}; arities={sa.size}/{ta.size}; raw proposition match={sourceType.equal target}."
    unless sourceType.getAppFn.isConstOf ``Iff && target.getAppFn.isConstOf ``Iff &&
        sa.size == 2 && ta.size == 2 do
      throwError "NativeHZero005 expected the two exact inferred/caller Iff propositions."
    for side in [:2] do
      let left := sa[side]!.consumeMData.headBeta
      let right := ta[side]!.consumeMData.headBeta
      let la := left.getAppArgs
      let ra := right.getAppArgs
      logInfo m!"NativeHZero005 side[{side}] heads={← nativeHZeroHead005 left}/{← nativeHZeroHead005 right}; arities={la.size}/{ra.size}; raw match={left.equal right}."
      for i in [:min (min la.size ra.size) 12] do
        logInfo m!"NativeHZero005 side[{side}].arg[{i}] heads={← nativeHZeroHead005 la[i]!}/{← nativeHZeroHead005 ra[i]!}; arities={la[i]!.getAppArgs.size}/{ra[i]!.getAppArgs.size}; raw match={la[i]!.equal ra[i]!}."
    let equalityType ← mkEq sourceType target
    let compatibility ← mkFreshExprSyntheticOpaqueMVar equalityType (← goal.getTag)
    let proof := mkAppN (mkConst ``Eq.mp [Level.zero])
      #[sourceType, target, compatibility, source]
    goal.assign proof
    replaceMainGoal [compatibility.mvarId!]
    let reflexivity ← mkEqRefl sourceType
    let suppliedRefl ← Term.exprToSyntax reflexivity
    logInfo "NativeHZero005 explicit proposition equality goal installed before unchanged bounded checker."
    evalTactic (← `(tactic| native_hzero_prop_seeded011 $suppliedRefl using $suppliedSeed, $suppliedCarrier, $suppliedFiber, $suppliedZero))
    logInfo "NativeHZero005 ordinary proposition compatibility and exact-vector Eq.mp emitted."

end

universe v w

/-- The same map and input, with both endpoint values retained explicitly. -/
private theorem nativeHZeroAlgHomRingEvaluationIff008
    {R : Type u} {A : Type v} {B : Type w}
    [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (x : A) (z : B) (Q : Prop)
    (h : f x = z ↔ Q) : f.toRingHom x = z ↔ Q := by
  exact h

meta section
open Lean Meta Elab Tactic

/-- Retain the imported proof's exact let telescope and instantiate only the
ordinary evaluation law from the stored AlgHom type vector; no implicit rewrite. -/
elab "native_hzero_ring_iff008% " supplied:term : term => do
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let source ← instantiateMVars source
  let sourceType ← instantiateMVars (← inferType source)
  if source.hasMVar || source.hasLevelMVar || source.hasLooseBVars || source.hasSorry ||
      sourceType.hasMVar || sourceType.hasLevelMVar then
    throwError "NativeHZero008 refuses unresolved/recovery source."
  lambdaLetTelescope sourceType (preserveNondepLet := true) fun xs body => do
    let body := body.consumeMData.headBeta
    let ia := body.getAppArgs
    unless body.getAppFn.isConstOf ``Iff && ia.size == 2 do
      throwError "NativeHZero008 expected the exact retained source Iff body."
    let some (_, value, endpoint) := ia[0]!.consumeMData.headBeta.eq?
      | throwError "NativeHZero008 expected the source native evaluation equality."
    let value := value.consumeMData.headBeta
    let va := value.getAppArgs
    unless value.getAppFn.isConstOf ``DFunLike.coe && va.size == 6 do
      throwError "NativeHZero008 expected native DFunLike.coe6 evaluation; head={← nativeHZeroHead005 value}, arity={va.size}."
    let mapType := va[0]!.consumeMData.headBeta
    let ma := mapType.getAppArgs
    let .const head levels := mapType.getAppFn
      | throwError "NativeHZero008 expected the stored AlgHom8 constant type."
    unless head == ``AlgHom && ma.size == 8 && levels.length == 3 do
      throwError "NativeHZero008 expected exact AlgHom8 with3 universes; actual head={head}, arity={ma.size}, universes={levels.length}."
    let law ← getConstInfo ``nativeHZeroAlgHomRingEvaluationIff008
    unless law.levelParams.length == 3 do
      throwError "NativeHZero008 ordinary law universe arity differs."
    let lawPrefix008 := mkAppN (mkConst law.name levels) ma
    let prefixType := (← instantiateMVars (← inferType lawPrefix008)).consumeMData.headBeta
    let .forallE _ expectedMapType _ _ := prefixType
      | throwError "NativeHZero008 exact ordinary law prefix did not leave its map binder."
    unless expectedMapType.consumeMData.headBeta.equal mapType do
      throwError "NativeHZero008 ordinary law binder/universe order does not match the stored AlgHom8 vector."
    let beforeSource := mkAppN lawPrefix008 #[va[4]!, va[5]!, endpoint, ia[1]!]
    let beforeSourceType := (← instantiateMVars (← inferType beforeSource)).consumeMData.headBeta
    let .forallE _ expectedSource _ _ := beforeSourceType
      | throwError "NativeHZero008 exact ordinary law application did not leave its proof binder."
    logInfo m!"NativeHZero008 retained source lets={xs.size}; exactAlgHom8/universe-order=true; raw native body/law-domain match={body.equal expectedSource}."
    let proof := mkApp beforeSource source
    let proof ← mkLetFVars (generalizeNondepLet := false) xs proof
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "NativeHZero008 refuses unresolved/recovery ordinary law application."
    logInfo "NativeHZero008 ordinary same-map evaluation law emitted with imported let telescope retained."
    return proof

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem actualOriginalPointIdealQuadratic_nativeRestriction_eval003
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s =
      (p3ActualIdealQuadraticIntrinsicLinearEquiv
        ((hypersurface p hp).fromSpecResidueField P.1 ≫
          quotientProjMap (equationIdeal p hp)) s).val.eval₂
        (chartBaseMap (equationIdeal p hp) C.index)
        (chartCoordinate (equationIdeal p hp) C.index) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma actualOriginalPositiveTwoNativeJet_intrinsic_le_original_point
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) :
    intrinsicFullQuadraticSystem
      (actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell ≫
        quotientProjMap (equationIdeal p hp)) ≤
      intrinsicFullQuadraticSystem
        ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)) := by
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  have h := intrinsicFullQuadraticSystem_le_comp
    (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K
      ((hypersurface p hp).residueField P.1) ((hypersurface p hp).residueField P.1)).toRingHom))
    (actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell ≫
      quotientProjMap (equationIdeal p hp))
  rw [← Category.assoc, actualOriginalPositiveTwoNativeJetEmbedding_reduction] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma actualOriginalPositiveTwoNativeJet_quadratic_mem_iff
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    (p3ActualIdealQuadraticIntrinsicLinearEquiv
      ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)) s).val ∈
        intrinsicFullQuadraticSystem
          (actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell ≫
            quotientProjMap (equationIdeal p hp)) ↔
      ell (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s) = 0 := by
  dsimp only
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) P
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let R := ChartRing (equationIdeal p hp) C.index
  let L := (hypersurface p hp).residueField P.1
  letI : Module.Finite K (DualNumber L) := QuarticNet.dualNumber_moduleFinite
  letI aK : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  letI : SMul K R := aK.toSMul
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun C.base c).symm)
  let E := actualCubicPositiveTwoOriginalNativePointFiberEquiv (K := K) (L := L) p hp
    ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization
  let phi := actualKaehlerLineDualAlgebraMap (ell.comp E.symm.toLinearMap)
  let EP := p3ActualIdealQuadraticIntrinsicLinearEquiv
    ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp))
  have hbase : phi.toRingHom.comp (chartBaseMap (equationIdeal p hp) C.index) =
      algebraMap K (DualNumber L) := by
    apply RingHom.ext
    intro c
    exact phi.commutes c
  have hmem := actualNativeChart_intrinsicQuadratic_mem_iff (K := K) (A := DualNumber L)
    (equationIdeal p hp) C.index phi.toRingHom hbase (EP s).val
  change (EP s).val ∈ intrinsicFullQuadraticSystem
      ((Spec.map (CommRingCat.ofHom phi.toRingHom) ≫ chartι (equationIdeal p hp) C.index) ≫
        quotientProjMap (equationIdeal p hp)) ↔ _
  rw [hmem]
  have hdual := actualOriginalPositiveTwoPhi_dualJet_zero_iff p hp P hP ell s
  have hRestriction := actualOriginalPointIdealQuadratic_nativeRestriction_eval003 p hp P hP s
  rw [hRestriction] at hdual
  have hdualRing := native_hzero_ring_iff008% hdual
  run_tac Lean.logInfo "NativeHZero008.00: inferred-retained-native-ring-evaluation-law-complete"
  run_tac Lean.logInfo "NativeHZero004.00: after-native-restriction-rewrite_before-inferred-join"
  have hhom : (EP s).val.IsHomogeneous 2 :=
    (MvPolynomial.mem_homogeneousSubmodule 2 (EP s).val).mp (EP s).property.1
  run_tac Lean.logInfo "NativeHZero006.00: ordinary-homogeneous-membership-cut-complete"
  have hjoin := (and_iff_right hhom).trans hdualRing
  run_tac Lean.logInfo "NativeHZero004.01: inferred-ordinary-Iff-trans-complete_before-target-assignment"
  have hSemiring : native_hzero_semiring_cut011% hjoin, hmem := by
    rfl
  run_tac Lean.logInfo "NativeHZero011.00: ordinary-exact-stored-semiring-seed-complete"
  have hCarrier : native_hzero_carrier_cut013% hjoin, hmem := by
    rfl
  run_tac Lean.logInfo "NativeHZero013.00: ordinary-exact-original-residue-carrier-seed-complete"
  have hFiber : native_hzero_fiber_cut014% hjoin, hmem := by
    rfl
  run_tac Lean.logInfo "NativeHZero014.00: ordinary-exact-original-fiber-alias-seed-complete"
  have hZero : native_hzero_zero_cut015% hjoin, hmem := by
    rfl
  run_tac Lean.logInfo "NativeHZero015.00: ordinary-exact-original-zero-instance-seed-complete"
  native_hzero_join_transport005 hjoin using hSemiring, hCarrier, hFiber, hZero

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Literal whole-H0 kernel equality as a linear equivalence, with the
canonical inclusion into original point ideal sections kept by construction. -/
def actualOriginalPositiveTwoNativeJetHZeroKernelEquiv
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let E2 := ActualOriginalPositiveTwoFiber p hp P
    letI : Module K E2 := Module.compHom E2 (algebraMap K L)
    letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist
        (actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell ≫
          quotientProjMap (equationIdeal p hp))
        (ProjectiveNegativeTwist.positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2)) ≃ₗ[K]
      LinearMap.ker ((ell.restrictScalars K).comp
        (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP)) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let E2 := ActualOriginalPositiveTwoFiber p hp P
  letI : Module K E2 := Module.compHom E2 (algebraMap K L)
  letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  let WP := intrinsicFullQuadraticSystem
    ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp))
  let WZ := intrinsicFullQuadraticSystem (d ≫ quotientProjMap (equationIdeal p hp))
  let EP := p3ActualIdealQuadraticIntrinsicLinearEquiv
    ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp))
  let EZ := p3ActualIdealQuadraticIntrinsicLinearEquiv (d ≫ quotientProjMap (equationIdeal p hp))
  let t := (ell.restrictScalars K).comp
    (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP)
  exact EZ.trans (submoduleKernelThroughLinearEquiv WZ WP EP t
    (actualOriginalPositiveTwoNativeJet_intrinsic_le_original_point p hp P hP ell)
    (actualOriginalPositiveTwoNativeJet_quadratic_mem_iff p hp P hP ell))

end PfaffianDescent
