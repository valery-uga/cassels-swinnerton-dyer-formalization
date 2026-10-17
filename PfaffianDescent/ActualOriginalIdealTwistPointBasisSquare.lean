import Lean.Meta.Eqns
import Lean.Meta.Tactic.Delta
import Lean
import Lean.Util.Sorry
import PfaffianDescent.ActualOriginalIdealTwistLocalBasisRefinement
import PfaffianDescent.ActualPointLocalChartSourceFactorization
import PfaffianDescent.ActualOriginalPositiveTwoLocalBasisContraction
import PfaffianDescent.ActualOriginalQuadraticConormalPointChartIso

/- Obtain the local equation's exact two section values from the existing
twisted/untwisted point-chart equations. No map, ring, module or factory
argument is reconstructed, reduced, or supplied as a new hypothesis. -/
meta section
namespace CasselsBasisEmbeddedLocal091
open Lean Meta Elab Term

/-- Strip only metadata along an application spine. The arguments,
native factories, and geometric values are kept exactly as supplied. -/
private def stripSpineMetadata092 : Expr → Expr
  | .mdata _ e => stripSpineMetadata092 e
  | .app f a => .app (stripSpineMetadata092 f) a
  | e => e

/-- Resolve assigned type metavariables and bounded pure beta/zeta/id
heads, including local let aliases. No named definition is unfolded. -/
private partial def equationHead092 (e : Expr) (fuel : Nat) : MetaM Expr := do
  let e ← instantiateMVars e
  let e := stripSpineMetadata092 ((stripSpineMetadata092 e).headBeta)
  if fuel == 0 then return e
  match e with
  | .letE _ _ value body _ => equationHead092 (body.instantiate1 value) (fuel - 1)
  | .fvar id =>
    let decl ← id.getDecl
    if let some value := decl.value? then
      equationHead092 value (fuel - 1)
    else return e
  | _ =>
    if e.getAppFn.isConstOf ``id && e.getAppArgs.size == 2 then
      equationHead092 e.getAppArgs[1]! (fuel - 1)
    else return e

private def equationDiagnostic092 (e : Expr) : String :=
  let label := match e.getAppFn with
    | .const n levels => s!"const {n}; levels={reprStr levels}"
    | .mvar id => s!"metavariable {id.name}"
    | .fvar id => s!"local variable {id.name}"
    | .forallE .. => "forall"
    | .lam .. => "lambda"
    | .letE .. => "let"
    | .proj n i _ => s!"projection {n}[{i}]"
    | _ => "other"
  s!"{label}; arguments={e.getAppArgs.size}; metavariables={e.hasMVar}"

elab "basisEmbeddedLocalEq091% " "(" twisted:term ")"
    "(" untwisted:term ")" "(" certificate:term ")" : term =>
    Term.withoutErrToSorry do
  let twistedProof ← Term.elabTerm twisted none (catchExPostpone := false)
  let untwistedProof ← Term.elabTerm untwisted none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let twistedProof ← instantiateMVars twistedProof
  let untwistedProof ← instantiateMVars untwistedProof
  let twistedType ← equationHead092 (← inferType twistedProof) 8
  let untwistedType ← equationHead092 (← inferType untwistedProof) 8
  let some (_, _, twistedRhs) := twistedType.eq?
    | throwError "EmbeddedLocal092 twisted type head: {equationDiagnostic092 twistedType}"
  let some (_, _, untwistedRhs) := untwistedType.eq?
    | throwError "EmbeddedLocal092 untwisted type head: {equationDiagnostic092 untwistedType}"
  let twistedRhs ← equationHead092 twistedRhs 8
  let untwistedRhs ← equationHead092 untwistedRhs 8
  let twistedArgs := twistedRhs.getAppArgs
  let untwistedArgs := untwistedRhs.getAppArgs
  unless twistedRhs.getAppFn.isConstOf ``PfaffianDescent.actualPointLocalSectionClass &&
      untwistedRhs.getAppFn.isConstOf ``PfaffianDescent.actualPointLocalSectionClass &&
      twistedArgs.size == 8 && untwistedArgs.size == 8 do
    throwError "EmbeddedLocal091 expected the two saturated original local section-class terms."
  let exactLeft := twistedArgs[7]!
  let exactRight := untwistedArgs[7]!
  let exactEquation ← mkEq exactLeft exactRight
  let proof ← Term.elabTermEnsuringType certificate (some exactEquation)
    (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "EmbeddedLocal091 refuses unresolved or recovery proof terms."
  logInfo "EmbeddedLocal091 proved the exact chart-section endpoints embedded in ht/hj."
  return proof

end CasselsBasisEmbeddedLocal091
end

namespace CasselsBasisStructuralCertificate093

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

end CasselsBasisStructuralCertificate093

meta section
namespace CasselsBasisStructuralCertificate093
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
      n == ``PfaffianDescent.closedImmersionIdealTwist || n == ``id
    | _ => false
  if !allowed then return e
  let some e' ← delta? e (fun n => isLocalLawName n ||
    n == ``AllCharacteristics.HomogeneousProjective.hypersurface ||
      n == ``PfaffianDescent.closedImmersionIdealTwist || n == ``id)
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

private structure CertificateState where
  remaining : Nat := 1024
  pairs : Array (Expr × Expr × Expr) := #[]
  congruences : Array (Expr × Nat × CongrTheorem) := #[]
  proofLeaves : Nat := 0
  congrSteps : Nat := 0
  binderSteps : Nat := 0
  fallbackProofLeaves : Nat := 0

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

elab "basis_structural_exact093 " supplied:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← Term.elabTerm supplied none
    Term.synthesizeSyntheticMVarsNoPostponing
    let source ← instantiateMVars source
    let sourceType ← inferType source
    let target ← goal.getType
    let (heq, state) ← (structuralHEq sourceType target 96 #[]).run {}
    let eq ← mkEqOfHEq heq
    let finalProof := mkAppN (mkConst ``Eq.mp [Level.zero])
      #[sourceType, target, eq, source]
    logInfo m!"BasisStructural093 certificate: proof leaves={state.proofLeaves}, abstract congruence steps={state.congrSteps}, binder steps={state.binderSteps}, unused traversal budget={state.remaining}."
    goal.assign finalProof
    replaceMainGoal []

/- Isolate the three structural parts of the exact original equality.
Every result is an ordinary proof checked with the enclosing declaration. -/
elab "basisEmbeddedLocalPart098% " part:ident "(" twisted:term ")"
    "(" untwisted:term ")" "(" supplied:term ")" : term =>
    Term.withoutErrToSorry do
  let twistedProof ← Term.elabTerm twisted none (catchExPostpone := false)
  let untwistedProof ← Term.elabTerm untwisted none (catchExPostpone := false)
  let sourceProof ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let twistedProof ← instantiateMVars twistedProof
  let untwistedProof ← instantiateMVars untwistedProof
  let sourceProof ← instantiateMVars sourceProof
  if sourceProof.hasMVar || sourceProof.hasLevelMVar || sourceProof.hasSorry then
    throwError "Part098 refuses an unresolved or recovery source theorem."
  let twistedType ← CasselsBasisEmbeddedLocal091.equationHead092 (← inferType twistedProof) 8
  let untwistedType ← CasselsBasisEmbeddedLocal091.equationHead092 (← inferType untwistedProof) 8
  let some (_, _, twistedRhs) := twistedType.eq?
    | throwError "Part098 expected the existing twisted point-chart equation."
  let some (_, _, untwistedRhs) := untwistedType.eq?
    | throwError "Part098 expected the existing untwisted point-chart equation."
  let twistedRhs ← CasselsBasisEmbeddedLocal091.equationHead092 twistedRhs 8
  let untwistedRhs ← CasselsBasisEmbeddedLocal091.equationHead092 untwistedRhs 8
  let twistedArgs := twistedRhs.getAppArgs
  let untwistedArgs := untwistedRhs.getAppArgs
  unless twistedRhs.getAppFn.isConstOf ``PfaffianDescent.actualPointLocalSectionClass &&
      untwistedRhs.getAppFn.isConstOf ``PfaffianDescent.actualPointLocalSectionClass &&
      twistedArgs.size == 8 && untwistedArgs.size == 8 do
    throwError "Part098 requires the two exact saturated original local section-class terms."
  let exactEquation ← mkEq twistedArgs[7]! untwistedArgs[7]!
  let some (targetCarrier, targetLeft, targetRight) := exactEquation.eq?
    | throwError "Part098 exact target is not an equality."
  let sourceType ← CasselsBasisEmbeddedLocal091.equationHead092 (← inferType sourceProof) 8
  let some (sourceCarrier, sourceLeft, sourceRight) := sourceType.eq?
    | throwError "Part098 source theorem is not an equality."
  let (left, right, homogeneous) ← match part.getId with
    | `carrier => pure (sourceCarrier, targetCarrier, true)
    | `left => pure (sourceLeft, targetLeft, false)
    | `right => pure (sourceRight, targetRight, false)
    | _ => throwError "Part098 expects carrier, left or right."
  let (heq, state) ← (structuralHEq left right 96 #[] s!"part.{part.getId}").run {}
  let proof ← if homogeneous then mkEqOfHEq heq else pure heq
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "Part098 refuses unresolved or recovery certificate terms."
  logInfo m!"BasisPart098 {part.getId}: proof leaves={state.proofLeaves}, abstract congruence steps={state.congrSteps}, binder steps={state.binderSteps}, unused traversal budget={state.remaining}."
  return proof

end CasselsBasisStructuralCertificate093
end

/- SOURCE ONLY / UNVERIFIED. True joint ideal/tensor/O2 point square on
EVERY local original ideal generator, retaining SAME point, chart,
untwisted ideal and source factorization. Coefficients/refinement laws are
all derived internally; no desired generator square is assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def actualOriginalUntwistedIdealPointChartIso
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let j := Spec.map (CommRingCat.ofHom C.residue)
    (Scheme.Modules.pullback q).obj (closedImmersionModule q) ≅
      (Scheme.Modules.pullback j).obj (closedImmersionModule j) := by
  dsimp only
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  exact actualModulePointChartSourceFactorizationIso (chartι (equationIdeal p hp) C.index)
    j q C.factorization (closedImmersionModule q) (closedImmersionModule j)
    (actualOriginalNativeUntwistedIdealChartIso p hp P hP)

/- Request Lean's ordinary checked stored equation for this original
consumer factory, exactly as for the accepted twisted factory. -/
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let some equation ← getUnfoldEqnFor?
    ``actualOriginalUntwistedIdealPointChartIso (nonRec := true)
    | throwError "Original untwisted factory has no stored unfold equation."
  logInfo m!"Original untwisted point chart stored equation: {equation}"

/- Diagnostic cut only; no public point-square claim. -/
private def actualOriginalIdealTwistPointLocalPart098_left
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let J := closedImmersionModule q
  let T := positiveSheafOfModules (grading I) 2
  let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
  let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
  let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
  exact fun (m : J.val.obj (op U)) => by
    have ht := actualPointLocalChartSourceFactorization f j q C.factorization
      (schemeModuleTensor J T) (closedImmersionModule j)
      (actualOriginalNativeIdealTwistChartIso p hp P hP) U hU
      (actualModuleLocalTensorSection J T U m
        (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))
    have hj := actualPointLocalChartSourceFactorization f j q C.factorization
      J (closedImmersionModule j) (actualOriginalNativeUntwistedIdealChartIso p hp P hP)
      U hU m
    exact basisEmbeddedLocalPart098% left (ht) (hj)
      (actualOriginalIdealTwistLocalBasisRefinement p hp P hP U m)

/- Diagnostic cut only; no public point-square claim. -/
private def actualOriginalIdealTwistPointLocalPart098_right
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let J := closedImmersionModule q
  let T := positiveSheafOfModules (grading I) 2
  let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
  let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
  let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
  exact fun (m : J.val.obj (op U)) => by
    have ht := actualPointLocalChartSourceFactorization f j q C.factorization
      (schemeModuleTensor J T) (closedImmersionModule j)
      (actualOriginalNativeIdealTwistChartIso p hp P hP) U hU
      (actualModuleLocalTensorSection J T U m
        (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))
    have hj := actualPointLocalChartSourceFactorization f j q C.factorization
      J (closedImmersionModule j) (actualOriginalNativeUntwistedIdealChartIso p hp P hP)
      U hU m
    exact basisEmbeddedLocalPart098% right (ht) (hj)
      (actualOriginalIdealTwistLocalBasisRefinement p hp P hP U m)

meta section
open Lean Meta Elab Term

private def appliedCutProof102 (stx : Syntax) : TermElabM Expr := do
  let proof ← Term.elabTerm stx none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "ArgumentCut102 refuses unresolved or recovery inputs."
  return proof

private def appliedCutHEq102 (proof : Expr) : MetaM (Array Expr) := do
  let ty ← CasselsBasisEmbeddedLocal091.equationHead092 (← inferType proof) 8
  unless ty.getAppFn.isConstOf ``HEq && ty.getAppArgs.size == 4 do
    throwError "ArgumentCut102 expected a four-argument HEq."
  return ty.getAppArgs

/- These primitive applications use the exact supplied proof vectors.
Each enclosing declaration still receives ordinary kernel checking. -/
elab "basisCutOperation102% " operation:ident "(" supplied:term ")" : term =>
    Term.withoutErrToSorry do
  let suppliedProof ← appliedCutProof102 supplied
  match operation.getId with
  | `symm =>
    let args ← appliedCutHEq102 suppliedProof
    let level ← getLevel args[0]!
    let proof := mkAppN (mkConst ``HEq.symm [level])
      #[args[0]!, args[2]!, args[1]!, args[3]!, suppliedProof]
    logInfo "ArgumentCut102 emitted symmetry using the named cut's exact HEq vector."
    return proof
  | `source_heq =>
    let ty ← CasselsBasisEmbeddedLocal091.equationHead092 (← inferType suppliedProof) 8
    let some (carrier, left, right) := ty.eq?
      | throwError "ArgumentCut102 source proof is not an equality."
    let level ← getLevel carrier
    let proof := mkAppN (mkConst ``heq_of_eq [level])
      #[carrier, left, right, suppliedProof]
    logInfo "ArgumentCut102 emitted source Eq-to-HEq using its exact Eq vector."
    return proof
  | _ => throwError "ArgumentCut102 expects symm or source_heq."

elab "basisCutTrans102% " "(" first:term ")" "(" second:term ")" : term =>
    Term.withoutErrToSorry do
  let firstProof ← appliedCutProof102 first
  let secondProof ← appliedCutProof102 second
  let firstArgs ← appliedCutHEq102 firstProof
  let secondArgs ← appliedCutHEq102 secondProof
  let level ← getLevel firstArgs[0]!
  let proof := mkAppN (mkConst ``HEq.trans [level])
    #[firstArgs[0]!, firstArgs[2]!, secondArgs[2]!, firstArgs[1]!,
      firstArgs[3]!, secondArgs[3]!, firstProof, secondProof]
  logInfo "ArgumentCut102 emitted transitivity using separately named proof vectors."
  return proof

end

/- Independent ordinary diagnostic cut; no desired equation is assumed. -/
private def actualOriginalIdealTwistPointNamedLeftApplication102
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let J := closedImmersionModule q
  let T := positiveSheafOfModules (grading I) 2
  let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
  let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
  let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
  exact fun (m : J.val.obj (op U)) => by
    exact (actualOriginalIdealTwistPointLocalPart098_left p hp P hP m)

/- Independent ordinary diagnostic cut; no desired equation is assumed. -/
private def actualOriginalIdealTwistPointSourceTheoremApplication102
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let J := closedImmersionModule q
  let T := positiveSheafOfModules (grading I) 2
  let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
  let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
  let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
  exact fun (m : J.val.obj (op U)) => by
    exact (actualOriginalIdealTwistLocalBasisRefinement p hp P hP U m)

/- Independent ordinary diagnostic cut; no desired equation is assumed. -/
private def actualOriginalIdealTwistPointNamedLeftSymmetry102
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let J := closedImmersionModule q
  let T := positiveSheafOfModules (grading I) 2
  let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
  let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
  let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
  exact fun (m : J.val.obj (op U)) => by
    exact basisCutOperation102% symm
      (actualOriginalIdealTwistPointLocalPart098_left p hp P hP m)

/- Independent ordinary diagnostic cut; no desired equation is assumed. -/
private def actualOriginalIdealTwistPointSourceTheoremHEq102
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let J := closedImmersionModule q
  let T := positiveSheafOfModules (grading I) 2
  let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
  let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
  let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
  exact fun (m : J.val.obj (op U)) => by
    exact basisCutOperation102% source_heq
      (actualOriginalIdealTwistLocalBasisRefinement p hp P hP U m)

/- Independent ordinary diagnostic cut; no desired equation is assumed. -/
private def actualOriginalIdealTwistPointStoredVectorMixedHEq102
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let J := closedImmersionModule q
  let T := positiveSheafOfModules (grading I) 2
  let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
  let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
  let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
  exact fun (m : J.val.obj (op U)) => by
    exact basisCutTrans102%
      (actualOriginalIdealTwistPointNamedLeftSymmetry102 p hp P hP m)
      (actualOriginalIdealTwistPointSourceTheoremHEq102 p hp P hP m)

meta section
open Lean Meta Elab Term

/- The homogeneous equality is built from the checked HEq's own vector.
Ordinary kernel checking verifies the required carrier compatibility. -/
elab "basisStoredVectorEq103% " "(" supplied:term ")" : term =>
    Term.withoutErrToSorry do
  let suppliedProof ← appliedCutProof102 supplied
  let args ← appliedCutHEq102 suppliedProof
  let level ← getLevel args[0]!
  let proof := mkAppN (mkConst ``eq_of_heq [level])
    #[args[0]!, args[1]!, args[3]!, suppliedProof]
  logInfo "StoredVector103 emitted ordinary Eq from the final HEq's own vector."
  return proof

/- Prove compatibility of the named equality's actual proposition with
exact embedded endpoints, then transport through that proved equality. -/
elab "basisStoredVectorCompatible105% " "(" twisted:term ")"
    "(" untwisted:term ")" "(" supplied:term ")" : term =>
    Term.withoutErrToSorry do
  let twistedProof ← appliedCutProof102 twisted
  let untwistedProof ← appliedCutProof102 untwisted
  let suppliedProof ← appliedCutProof102 supplied
  let twistedType ← CasselsBasisEmbeddedLocal091.equationHead092 (← inferType twistedProof) 8
  let untwistedType ← CasselsBasisEmbeddedLocal091.equationHead092 (← inferType untwistedProof) 8
  let some (_, _, twistedRhs) := twistedType.eq?
    | throwError "StoredVector103 expected the existing twisted chart equation."
  let some (_, _, untwistedRhs) := untwistedType.eq?
    | throwError "StoredVector103 expected the existing untwisted chart equation."
  let twistedRhs ← CasselsBasisEmbeddedLocal091.equationHead092 twistedRhs 8
  let untwistedRhs ← CasselsBasisEmbeddedLocal091.equationHead092 untwistedRhs 8
  let twistedArgs := twistedRhs.getAppArgs
  let untwistedArgs := untwistedRhs.getAppArgs
  unless twistedRhs.getAppFn.isConstOf ``actualPointLocalSectionClass &&
      untwistedRhs.getAppFn.isConstOf ``actualPointLocalSectionClass &&
      twistedArgs.size == 8 && untwistedArgs.size == 8 do
    throwError "StoredVector103 requires the exact two original section-class terms."
  let exactEquation ← mkEq twistedArgs[7]! untwistedArgs[7]!
  let sourceType ← CasselsBasisEmbeddedLocal091.equationHead092 (← inferType suppliedProof) 8
  Term.synthesizeSyntheticMVarsNoPostponing
  let exactEquation ← instantiateMVars exactEquation
  let sourceType ← instantiateMVars sourceType
  if exactEquation.hasMVar || exactEquation.hasLevelMVar ||
      sourceType.hasMVar || sourceType.hasLevelMVar then
    throwError "StoredVector105 unresolved extracted source or target proposition."
  let (heq, state) ←
    (CasselsBasisStructuralCertificate093.structuralHEq sourceType exactEquation
      96 #[] "compatibility105").run {}
  let typeEquation ← mkEqOfHEq heq
  let proof := mkAppN (mkConst ``Eq.mp [Level.zero])
    #[sourceType, exactEquation, typeEquation, suppliedProof]
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "StoredVector105 refuses unresolved or recovery transport."
  logInfo m!"StoredVector105 exact compatibility: proof leaves={state.proofLeaves}, abstract congruence steps={state.congrSteps}, binder steps={state.binderSteps}, unused traversal budget={state.remaining}."
  return proof

end

/- Ordinary named proof cut; exact original expressions are retained. -/
private def actualOriginalIdealTwistPointStoredFinalHEq103
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let J := closedImmersionModule q
  let T := positiveSheafOfModules (grading I) 2
  let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
  let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
  let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
  exact fun (m : J.val.obj (op U)) => by
    exact basisCutTrans102%
      (actualOriginalIdealTwistPointStoredVectorMixedHEq102 p hp P hP m)
      (actualOriginalIdealTwistPointLocalPart098_right p hp P hP m)

/- Ordinary named proof cut; exact original expressions are retained. -/
private def actualOriginalIdealTwistPointStoredFinalEquality103
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let J := closedImmersionModule q
  let T := positiveSheafOfModules (grading I) 2
  let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
  let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
  let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
  exact fun (m : J.val.obj (op U)) => by
    exact basisStoredVectorEq103%
      (actualOriginalIdealTwistPointStoredFinalHEq103 p hp P hP m)

/- Ordinary named proof cut; exact original expressions are retained. -/
private def actualOriginalIdealTwistPointStoredEmbeddedCompatibility105
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let J := closedImmersionModule q
  let T := positiveSheafOfModules (grading I) 2
  let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
  let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
  let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
  exact fun (m : J.val.obj (op U)) => by
    have ht := actualPointLocalChartSourceFactorization f j q C.factorization
      (schemeModuleTensor J T) (closedImmersionModule j)
      (actualOriginalNativeIdealTwistChartIso p hp P hP) U hU
      (actualModuleLocalTensorSection J T U m
        (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))
    have hj := actualPointLocalChartSourceFactorization f j q C.factorization
      J (closedImmersionModule j) (actualOriginalNativeUntwistedIdealChartIso p hp P hP)
      U hU m
    exact basisStoredVectorCompatible105% (ht) (hj)
      (actualOriginalIdealTwistPointStoredFinalEquality103 p hp P hP m)

universe v w

/-- Transport a law through checked equalities of two complete values. -/
private theorem actualLaw_of_two_storedValues107
    {A : Sort v} {B : Sort w} {a a' : A} {b b' : B}
    (ha : a = a') (hb : b = b') (L : A → B → Prop)
    (h : L a' b') : L a b := by
  cases ha
  cases hb
  exact h

meta section
open Lean Meta Elab Term

/-- Inspect only expression structure; never unfold a geometric value. -/
private partial def findStoredBuilder107 (e : Expr) (depth : Nat) : MetaM (Option Expr) := do
  if depth == 0 then throwError "FactoryTransport107 exhausted its fixed search depth."
  if e.getAppFn.isConstOf ``actualModulePointChartSourceFactorizationIso &&
      e.getAppArgs.size == 12 then return some e
  match e with
  | .app f a =>
    if let some builder ← findStoredBuilder107 f (depth - 1) then return some builder
    findStoredBuilder107 a (depth - 1)
  | .lam _ ty body _ | .forallE _ ty body _ =>
    if let some builder ← findStoredBuilder107 ty (depth - 1) then return some builder
    findStoredBuilder107 body (depth - 1)
  | .letE _ ty value body _ =>
    if let some builder ← findStoredBuilder107 ty (depth - 1) then return some builder
    if let some builder ← findStoredBuilder107 value (depth - 1) then return some builder
    findStoredBuilder107 body (depth - 1)
  | .proj _ _ major | .mdata _ major => findStoredBuilder107 major (depth - 1)
  | _ => return none

private def originalFactoryEquation107 (factory : Expr) :
    MetaM (Expr × Expr × Expr × Expr) := do
  let .const name levels := factory.getAppFn
    | throwError "FactoryTransport107 expects an original factory application."
  unless (name == ``actualOriginalQuadraticConormalPointChartIso ||
      name == ``actualOriginalUntwistedIdealPointChartIso) &&
      factory.getAppArgs.size == 7 && levels.length == 1 do
    throwError "FactoryTransport107 requires either original seven-argument point Iso."
  let equation ← getConstInfo (Name.str name "eq_def")
  unless equation.levelParams.length == levels.length do
    throwError "FactoryTransport107 stored equation universe vector differs."
  let proof := mkAppN (mkConst equation.name levels) factory.getAppArgs
  let ty ← CasselsBasisEmbeddedLocal091.equationHead092 (← inferType proof) 8
  let ty ← instantiateMVars ty
  let some (carrier, original, stored) := ty.eq?
    | throwError "FactoryTransport107 stored equation is not an equality."
  unless original.equal factory do
    throwError "FactoryTransport107 stored equation has a different original endpoint."
  if ty.hasMVar || ty.hasLevelMVar || proof.hasMVar || proof.hasLevelMVar then
    throwError "FactoryTransport107 unresolved stored factory equation."
  return (carrier, original, stored, proof)

/- Build the section law by substituting abstract Iso variables into the
existing proved equation. The G/map/section expressions stay exactly intact. -/
elab "basisOriginalFactories108% " "(" supplied:term ")"
    "(" twistedFactory:term ")" "(" untwistedFactory:term ")" : term =>
    Term.withoutErrToSorry do
  let sourceProof ← appliedCutProof102 supplied
  let leftFactory ← appliedCutProof102 twistedFactory
  let rightFactory ← appliedCutProof102 untwistedFactory
  let sourceType ← CasselsBasisEmbeddedLocal091.equationHead092 (← inferType sourceProof) 8
  let sourceType ← instantiateMVars sourceType
  let some (_, leftValue, rightValue) := sourceType.eq?
    | throwError "FactoryTransport107 existing section law is not an equality."
  let some leftBuilder ← findStoredBuilder107 leftValue 96
    | throwError "FactoryTransport107 left section value has no exact twelve-argument builder."
  let some rightBuilder ← findStoredBuilder107 rightValue 96
    | throwError "FactoryTransport107 right section value has no exact twelve-argument builder."
  if leftBuilder.hasLooseBVars || rightBuilder.hasLooseBVars then
    throwError "FactoryTransport107 refuses a builder under a loose binder."
  let (A, a, a', ha) ← originalFactoryEquation107 leftFactory
  let (B, b, b', hb) ← originalFactoryEquation107 rightFactory
  let predicate ← withLocalDeclD `Et A fun et => do
    withLocalDeclD `Ej B fun ej => do
      let body := sourceType.replace fun e =>
        if e.equal leftBuilder then some et
        else if e.equal rightBuilder then some ej
        else none
      mkLambdaFVars #[et, ej] body
  let premise ← instantiateMVars ((mkAppN predicate #[a', b']).headBeta)
  let conclusion ← instantiateMVars ((mkAppN predicate #[a, b]).headBeta)
  Term.synthesizeSyntheticMVarsNoPostponing
  let premise ← instantiateMVars premise
  let conclusion ← instantiateMVars conclusion
  if sourceType.hasMVar || sourceType.hasLevelMVar || premise.hasMVar ||
      premise.hasLevelMVar || conclusion.hasMVar || conclusion.hasLevelMVar then
    throwError "FactoryTransport107 unresolved section-law proposition."
  let (heq, state) ←
    (CasselsBasisStructuralCertificate093.structuralHEq sourceType premise
      96 #[] "factoryStoredPremise108").run {}
  let premiseEq ← mkEqOfHEq heq
  let storedLaw := mkAppN (mkConst ``Eq.mp [Level.zero])
    #[sourceType, premise, premiseEq, sourceProof]
  let helper ← getConstInfo ``actualLaw_of_two_storedValues107
  unless helper.levelParams.length == 2 do
    throwError "FactoryTransport107 abstract helper universe vector differs."
  let levelA ← getLevel A
  let levelB ← getLevel B
  let proof := mkAppN (mkConst helper.name [levelA, levelB])
    #[A, B, a, a', b, b', ha, hb, predicate, storedLaw]
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "FactoryTransport107 refuses unresolved or recovery proof terms."
  logInfo m!"FactoryTransport108 checked stored-premise certificate: proof leaves={state.proofLeaves}, confirmed fallback proofs={state.fallbackProofLeaves}, abstract congruence steps={state.congrSteps}, binder steps={state.binderSteps}, unused traversal budget={state.remaining}."
  return proof

end

/-- Replace only the right side of an equality by an ordinary proved application law. -/
private theorem actualEquality_of_rightApplication110
    {A : Sort u} {left right applied : A}
    (hr : right = applied) (h : left = applied) : left = right :=
  h.trans hr.symm

meta section
open Lean Meta Elab Tactic

/-- Find the exact concrete-category hom whose final morphism is a composition.
Projection heads are expressed by their declared projection functions; no
morphism, section, factory, or module object is unfolded. -/
private partial def findConcreteComposition110 (e : Expr) (depth : Nat) :
    MetaM (Option (Expr × Expr)) := do
  if depth == 0 then
    throwError "ExactComp110 exhausted its fixed expression-search depth."
  let e := CasselsBasisEmbeddedLocal091.stripSpineMetadata092 e
  let e ← CasselsBasisStructuralCertificate093.projectionAsApplication e
  if e.getAppFn.isConstOf ``ConcreteCategory.hom then
    let .inductInfo ind ← getConstInfo ``ConcreteCategory
      | throwError "ExactComp110 concrete-category metadata is not inductive."
    let homPrefixCount := ind.numParams + 1
    let args := e.getAppArgs
    if args.size == homPrefixCount + 3 then
      let comp ← CasselsBasisStructuralCertificate093.projectionAsApplication
        (CasselsBasisEmbeddedLocal091.stripSpineMetadata092 args[homPrefixCount + 2]!)
      if comp.getAppFn.isConstOf ``CategoryStruct.comp then
        return some (e, comp)
  match e with
  | .app f a =>
    if let some result ← findConcreteComposition110 a (depth - 1) then
      return some result
    findConcreteComposition110 f (depth - 1)
  | .mdata _ major => findConcreteComposition110 major (depth - 1)
  | _ => return none

/- Instantiate the ordinary class law with the goal's own class parameters,
objects, morphisms and sectionValue. No rewrite traversal or native carrier
unification is asked of the elaborator. The enclosing declaration's ordinary
kernel check verifies both the application law and the replacement. -/
elab "basisExactComposition110" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← CasselsBasisEmbeddedLocal091.equationHead092 (← goal.getType) 8
    let target ← instantiateMVars target
    let some (carrier, left, right) := target.eq?
      | throwError "ExactComp110 expects an equality goal."
    let rightView := CasselsBasisEmbeddedLocal091.stripSpineMetadata092 right
    let .app function sectionValue := rightView
      | throwError "ExactComp110 right side is not a stored sectionValue application: {CasselsBasisEmbeddedLocal091.equationDiagnostic092 rightView}"
    let some (hom, comp) ← findConcreteComposition110 function 96
      | throwError "ExactComp110 found no concrete hom of a composition in the exact right-side function: {CasselsBasisEmbeddedLocal091.equationDiagnostic092 function}"
    let .const _ levels := hom.getAppFn
      | throwError "ExactComp110 concrete hom has no declared projection head."
    let .inductInfo homInd ← getConstInfo ``ConcreteCategory
      | throwError "ExactComp110 concrete-category metadata is not inductive."
    let .inductInfo compInd ← getConstInfo ``CategoryStruct
      | throwError "ExactComp110 category-structure metadata is not inductive."
    let homPrefix := homInd.numParams + 1
    let compPrefix := compInd.numParams + 1
    let homArgs := hom.getAppArgs
    let compArgs := comp.getAppArgs
    unless homArgs.size == homPrefix + 3 && compArgs.size == compPrefix + 5 do
      throwError "ExactComp110 stored hom/composition argument vectors differ: hom={homArgs.size}, composition={compArgs.size}."
    let law ← getConstInfo ``ConcreteCategory.comp_apply
    unless law.levelParams.length == levels.length do
      throwError "ExactComp110 application-law universe vector differs from the stored hom."
    let lawArgs := homArgs.extract 0 homPrefix ++
      compArgs.extract compPrefix (compPrefix + 3) ++
      #[compArgs[compPrefix + 3]!, compArgs[compPrefix + 4]!, sectionValue]
    let compProof := mkAppN (mkConst law.name levels) lawArgs
    let proofType ← CasselsBasisEmbeddedLocal091.equationHead092 (← inferType compProof) 8
    let proofType ← instantiateMVars proofType
    let some (proofCarrier, oldRight, appliedRight) := proofType.eq?
      | throwError "ExactComp110 stored class law is not an equality."
    if target.hasMVar || target.hasLevelMVar || compProof.hasMVar ||
        compProof.hasLevelMVar || proofType.hasMVar || proofType.hasLevelMVar then
      throwError "ExactComp110 refuses unresolved target or application-law terms."
    let helper ← getConstInfo ``actualEquality_of_rightApplication110
    unless helper.levelParams.length == 1 do
      throwError "ExactComp110 abstract equality helper universe vector differs."
    let carrierLevel ← getLevel carrier
    let newType := mkAppN (mkConst ``Eq [carrierLevel]) #[carrier, left, appliedRight]
    let newGoal ← mkFreshExprSyntheticOpaqueMVar newType (← goal.getTag)
    let proof := mkAppN (mkConst helper.name [carrierLevel])
      #[carrier, left, right, appliedRight, compProof, newGoal]
    logInfo m!"ExactComp110 emitted the ordinary stored-vector class law: hom parameters={homPrefix}, composition parameters={compPrefix}, raw carrier match={proofCarrier.equal carrier}, raw right-side match={oldRight.equal right}."
    goal.assign proof
    replaceMainGoal [newGoal.mvarId!]

/-- Find only the original tensor-Iso hom node, keeping its actual stored
expression as the substitution key. No Iso or module value is unfolded. -/
private partial def findOriginalTensorHom113 (e : Expr) (depth : Nat) :
    MetaM (Option Expr) := do
  if depth == 0 then
    throwError "ExactContraction113 exhausted its fixed expression-search depth."
  let stored := CasselsBasisEmbeddedLocal091.stripSpineMetadata092 e
  let declared ← CasselsBasisStructuralCertificate093.projectionAsApplication stored
  if declared.getAppFn.isConstOf ``Iso.hom then
    let args := declared.getAppArgs
    if !args.isEmpty then
      let factory := CasselsBasisEmbeddedLocal091.stripSpineMetadata092 args.back!
      if factory.getAppFn.isConstOf ``actualPositiveTwistPullbackTensorIso &&
          factory.getAppArgs.size == 7 then
        return some stored
  match stored with
  | .app f a =>
    if let some result ← findOriginalTensorHom113 a (depth - 1) then
      return some result
    findOriginalTensorHom113 f (depth - 1)
  | .proj _ _ major | .mdata _ major => findOriginalTensorHom113 major (depth - 1)
  | _ => return none

/-- Read an existing proof's own equality vector, with pure head beta only
on its two endpoints. No expected carrier or endpoint is supplied. -/
private def ownEquality113 (proof : Expr) : MetaM (Expr × Expr × Expr) := do
  let ty ← CasselsBasisEmbeddedLocal091.equationHead092 (← inferType proof) 8
  let ty ← instantiateMVars ty
  let some (carrier, left, right) := ty.eq?
    | throwError "ExactContraction113 expected an ordinary equality proof."
  if ty.hasMVar || ty.hasLevelMVar then
    throwError "ExactContraction113 refuses an unresolved equality vector."
  return (carrier, left.consumeMData.headBeta, right.consumeMData.headBeta)

/- Apply the two established identities through the exact stored map/section
function. The final proof uses only ordinary congrArg, Eq.trans, and the
ordinary right-application equality helper. All argument vectors are explicit. -/
elab "basisExactTensorContraction113 " "(" supplied:term ")"
    "(" tensorIdentity:term ")" "(" contractionIdentity:term ")" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let sourceProof ← appliedCutProof102 supplied
    let tensorProof ← appliedCutProof102 tensorIdentity
    let contractionProof ← appliedCutProof102 contractionIdentity
    let target ← CasselsBasisEmbeddedLocal091.equationHead092 (← goal.getType) 8
    let target ← instantiateMVars target
    let some (carrier, left, right) := target.eq?
      | throwError "ExactContraction113 expects an equality goal."
    if target.hasMVar || target.hasLevelMVar then
      throwError "ExactContraction113 refuses an unresolved equality goal."
    let .app outerFunction innerValue :=
        CasselsBasisEmbeddedLocal091.stripSpineMetadata092 right
      | throwError "ExactContraction113 right side is not the exact outer map application."
    let some tensorNode ← findOriginalTensorHom113 innerValue 96
      | throwError "ExactContraction113 found no original tensor-Iso hom in the exact inner application."
    let (morphismCarrier, oldMorphism, newMorphism) ← ownEquality113 tensorProof
    let innerCarrier ← instantiateMVars (← inferType innerValue)
    let mapper ← withLocalDeclD `tensorHom morphismCarrier fun homValue => do
      let body := innerValue.replace fun e =>
        if e.equal tensorNode then some homValue else none
      mkLambdaFVars #[homValue] body
    let morphismLevel ← getLevel morphismCarrier
    let innerLevel ← getLevel innerCarrier
    let mappedTensor := mkAppN (mkConst ``congrArg [morphismLevel, innerLevel])
      #[morphismCarrier, innerCarrier, oldMorphism, newMorphism, mapper, tensorProof]
    let (mappedCarrier, mappedOld, mappedNew) ← ownEquality113 mappedTensor
    let (contractionCarrier, contractionOld, contractionNew) ← ownEquality113 contractionProof
    let innerProof := mkAppN (mkConst ``Eq.trans [innerLevel])
      #[mappedCarrier, mappedOld, mappedNew, contractionNew, mappedTensor, contractionProof]
    let (provedInnerCarrier, provedInnerOld, provedInnerNew) ← ownEquality113 innerProof
    let carrierLevel ← getLevel carrier
    let mappedContraction := mkAppN (mkConst ``congrArg [innerLevel, carrierLevel])
      #[provedInnerCarrier, carrier, provedInnerOld, provedInnerNew, outerFunction, innerProof]
    let (mappedOuterCarrier, mappedOuterOld, mappedOuterNew) ← ownEquality113 mappedContraction
    let (sourceCarrier, sourceLeft, sourceRight) ← ownEquality113 sourceProof
    let helper ← getConstInfo ``actualEquality_of_rightApplication110
    unless helper.levelParams.length == 1 do
      throwError "ExactContraction113 abstract helper universe vector differs."
    let proof := mkAppN (mkConst helper.name [carrierLevel])
      #[carrier, left, right, mappedOuterNew, mappedContraction, sourceProof]
    if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "ExactContraction113 refuses unresolved or recovery proof terms."
    logInfo m!"ExactContraction113 emitted ordinary tensor/contraction congruences: raw tensor hom={oldMorphism.equal tensorNode}, raw inner old={mappedOld.equal innerValue}, raw contraction carrier={mappedCarrier.equal contractionCarrier}, raw middle={mappedNew.equal contractionOld}, raw outer carrier={mappedOuterCarrier.equal carrier}, raw outer old={mappedOuterOld.equal right}, raw source carrier={sourceCarrier.equal carrier}, raw source left={sourceLeft.equal left}, raw source right={sourceRight.equal mappedOuterNew}."
    goal.assign proof
    replaceMainGoal []
    logInfo "BasisTail113: explicit tensor/contraction proof returned."

/- Independent ordinary declaration cuts below use these exact-vector
extractors. Each extractor emits an ordinary proof; no declaration is added
or accepted by a meta operation. -/
elab "basisCompositionLaw114% " "(" value:term ")" : term =>
    Term.withoutErrToSorry do
  let value ← appliedCutProof102 value
  let .app function sectionValue :=
      CasselsBasisEmbeddedLocal091.stripSpineMetadata092 value
    | throwError "KernelCuts114 composition value is not a section application."
  let some (hom, comp) ← findConcreteComposition110 function 96
    | throwError "KernelCuts114 composition value has no exact concrete hom/composition."
  let .const _ levels := hom.getAppFn
    | throwError "KernelCuts114 concrete hom has no declared projection head."
  let .inductInfo homInd ← getConstInfo ``ConcreteCategory
    | throwError "KernelCuts114 concrete-category metadata is not inductive."
  let .inductInfo compInd ← getConstInfo ``CategoryStruct
    | throwError "KernelCuts114 category-structure metadata is not inductive."
  let homPrefix := homInd.numParams + 1
  let compPrefix := compInd.numParams + 1
  let homArgs := hom.getAppArgs
  let compArgs := comp.getAppArgs
  unless homArgs.size == homPrefix + 3 && compArgs.size == compPrefix + 5 do
    throwError "KernelCuts114 class-law stored vectors differ."
  let law ← getConstInfo ``ConcreteCategory.comp_apply
  unless law.levelParams.length == levels.length do
    throwError "KernelCuts114 class-law stored universe vector differs."
  let proof := mkAppN (mkConst law.name levels)
    (homArgs.extract 0 homPrefix ++
      compArgs.extract compPrefix (compPrefix + 3) ++
      #[compArgs[compPrefix + 3]!, compArgs[compPrefix + 4]!, sectionValue])
  let (_, ownLeft, _) ← ownEquality113 proof
  logInfo m!"KernelCuts114 class-law ordinary proof emitted: raw original application match={ownLeft.equal value}."
  return proof

elab "basisInnerContraction114% " "(" suppliedValue:term ")"
    "(" tensorIdentity:term ")" "(" contractionIdentity:term ")" : term =>
    Term.withoutErrToSorry do
  let innerValue ← appliedCutProof102 suppliedValue
  let tensorProof ← appliedCutProof102 tensorIdentity
  let contractionProof ← appliedCutProof102 contractionIdentity
  let some tensorNode ← findOriginalTensorHom113 innerValue 96
    | throwError "KernelCuts114 inner value has no exact original tensor-Iso hom."
  let (morphismCarrier, oldMorphism, newMorphism) ← ownEquality113 tensorProof
  let innerCarrier ← instantiateMVars (← inferType innerValue)
  let mapper ← withLocalDeclD `tensorHom morphismCarrier fun homValue => do
    let body := innerValue.replace fun e =>
      if e.equal tensorNode then some homValue else none
    mkLambdaFVars #[homValue] body
  let morphismLevel ← getLevel morphismCarrier
  let innerLevel ← getLevel innerCarrier
  let mappedTensor := mkAppN (mkConst ``congrArg [morphismLevel, innerLevel])
    #[morphismCarrier, innerCarrier, oldMorphism, newMorphism, mapper, tensorProof]
  let (mappedCarrier, mappedOld, mappedNew) ← ownEquality113 mappedTensor
  let (contractionCarrier, contractionOld, contractionNew) ← ownEquality113 contractionProof
  let proof := mkAppN (mkConst ``Eq.trans [innerLevel])
    #[mappedCarrier, mappedOld, mappedNew, contractionNew, mappedTensor, contractionProof]
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "KernelCuts114 inner cut refuses an unresolved or recovery proof."
  logInfo m!"KernelCuts114 inner ordinary proof emitted: raw tensor hom={oldMorphism.equal tensorNode}, raw original inner={mappedOld.equal innerValue}, raw contraction carrier={mappedCarrier.equal contractionCarrier}, raw contraction middle={mappedNew.equal contractionOld}."
  return proof

elab "basisOuterContraction114% " "(" suppliedFunction:term ")"
    "(" suppliedProof:term ")" : term => Term.withoutErrToSorry do
  let outerFunction ← appliedCutProof102 suppliedFunction
  let innerProof ← appliedCutProof102 suppliedProof
  let (innerCarrier, innerOld, innerNew) ← ownEquality113 innerProof
  let outerCarrier ← instantiateMVars (← inferType (mkApp outerFunction innerOld))
  let innerLevel ← getLevel innerCarrier
  let outerLevel ← getLevel outerCarrier
  let proof := mkAppN (mkConst ``congrArg [innerLevel, outerLevel])
    #[innerCarrier, outerCarrier, innerOld, innerNew, outerFunction, innerProof]
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "KernelCuts114 outer cut refuses an unresolved or recovery proof."
  logInfo "KernelCuts114 outer ordinary congrArg proof emitted."
  return proof

elab "basisSourceTypeCompatibility114% " "(" suppliedSource:term ")"
    "(" suppliedLeft:term ")" "(" suppliedOuter:term ")" : term =>
    Term.withoutErrToSorry do
  let sourceProof ← appliedCutProof102 suppliedSource
  let leftValue ← appliedCutProof102 suppliedLeft
  let outerProof ← appliedCutProof102 suppliedOuter
  let sourceType ← CasselsBasisEmbeddedLocal091.equationHead092 (← inferType sourceProof) 8
  let sourceType ← instantiateMVars sourceType
  let (targetCarrier, _, targetRight) ← ownEquality113 outerProof
  let carrierLevel ← getLevel targetCarrier
  let targetType := mkAppN (mkConst ``Eq [carrierLevel])
    #[targetCarrier, leftValue, targetRight]
  let (heq, state) ←
    (CasselsBasisStructuralCertificate093.structuralHEq sourceType targetType
      96 #[] "sourceCompatibility114").run {}
  let proof ← mkEqOfHEq heq
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "KernelCuts114 source compatibility refuses unresolved or recovery proof."
  logInfo m!"KernelCuts114 source proposition compatibility emitted: proof leaves={state.proofLeaves}, confirmed fallback proofs={state.fallbackProofLeaves}, abstract congruence steps={state.congrSteps}, binder steps={state.binderSteps}, unused traversal budget={state.remaining}."
  return proof

elab "basisFinalCheckpoint110 " supplied:term : tactic => do
  logInfo "BasisTail110: entering final exact."
  evalTactic (← `(tactic| exact $supplied))
  logInfo "BasisTail110: final exact returned."

end

/- Independent ordinary kernel diagnostic cut; original vectors retained. -/
private def actualOriginalIdealTwistPointFactoryLaw114
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let J := closedImmersionModule q
  let T := positiveSheafOfModules (grading I) 2
  let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
  let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
  let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
  exact fun (m : J.val.obj (op U)) => by
    have ht := actualPointLocalChartSourceFactorization f j q C.factorization
      (schemeModuleTensor J T) (closedImmersionModule j)
      (actualOriginalNativeIdealTwistChartIso p hp P hP) U hU
      (actualModuleLocalTensorSection J T U m
        (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))
    have hj := actualPointLocalChartSourceFactorization f j q C.factorization
      J (closedImmersionModule j) (actualOriginalNativeUntwistedIdealChartIso p hp P hP)
      U hU m
    have hLocal := basisStoredVectorCompatible105% (ht) (hj)
      (actualOriginalIdealTwistPointStoredEmbeddedCompatibility105 p hp P hP m)
    rw [hLocal] at ht
    have hRaw := ht.trans hj.symm
    exact basisOriginalFactories108% (hRaw)
      (actualOriginalQuadraticConormalPointChartIso p hp P hP)
      (actualOriginalUntwistedIdealPointChartIso p hp P hP)

/- Independent ordinary kernel diagnostic cut; original vectors retained. -/
private def actualOriginalIdealTwistPointInnerContractionLaw114
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let J := closedImmersionModule q
  let T := positiveSheafOfModules (grading I) 2
  let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
  let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
  let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
  exact fun (m : J.val.obj (op U)) => by
    exact basisInnerContraction114%
      ((G.map ((actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
            (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
              ((Scheme.Modules.pullback q).obj T)
              (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom))
        (actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
          (actualModuleLocalTensorSection J T U m
            (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))))
      (actualPositiveTwistPullbackTensorIso_hom I q J 2)
      (actualOriginalPositiveTwoLocalBasisContraction p hp P hP J U hU m)

end PfaffianDescent
end

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

meta section
open Lean Meta Elab Term

/-- Refer to already kernel-checked cached proof declarations using their numeric private namespace. -/

private def stripSpineMetadata115 : Expr → Expr
  | .mdata _ e => stripSpineMetadata115 e
  | .app f a => .app (stripSpineMetadata115 f) a
  | e => e

private partial def equationHead115 (e : Expr) (fuel : Nat) : MetaM Expr := do
  let e ← instantiateMVars e
  let e := stripSpineMetadata115 ((stripSpineMetadata115 e).headBeta)
  if fuel == 0 then return e
  match e with
  | .letE _ _ value body _ => equationHead115 (body.instantiate1 value) (fuel - 1)
  | .fvar id =>
    let decl ← id.getDecl
    if let some value := decl.value? then equationHead115 value (fuel - 1)
    else return e
  | _ =>
    if e.getAppFn.isConstOf ``id && e.getAppArgs.size == 2 then
      equationHead115 e.getAppArgs[1]! (fuel - 1)
    else return e

private def projectionAsApplication115 (e : Expr) : MetaM Expr := do
  let .proj structName idx major := e.getAppFn | return e
  let some info := getStructureInfo? (← getEnv) structName
    | throwError "KernelCuts115 missing structure projection metadata."
  let some projName := info.getProjFn? idx
    | throwError "KernelCuts115 missing declared projection function."
  let ty ← instantiateMVars (← whnfD (← inferType major))
  let .const typeName levels := ty.getAppFn
    | throwError "KernelCuts115 projection source has no structure type."
  unless typeName == structName && !ty.hasMVar && !ty.hasLevelMVar do
    throwError "KernelCuts115 projection structure differs or has unresolved variables."
  let .inductInfo ind ← getConstInfo structName
    | throwError "KernelCuts115 projection source is not inductive."
  let params := ty.getAppArgs.extract 0 ind.numParams
  return mkAppN (mkApp (mkAppN (mkConst projName levels) params) major) e.getAppArgs

private def appliedTerm115 (stx : Syntax) : TermElabM Expr := do
  let term ← Term.elabTerm stx none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let term ← instantiateMVars term
  if term.hasMVar || term.hasLevelMVar || term.hasLooseBVars || term.hasSorry then
    throwError "KernelCuts115 refuses unresolved or recovery source terms."
  return term

private def ownEquality115 (proof : Expr) : MetaM (Expr × Expr × Expr) := do
  let ty ← equationHead115 (← inferType proof) 8
  let ty ← instantiateMVars ty
  let some (carrier, left, right) := ty.eq?
    | throwError "KernelCuts115 expected an ordinary equality proof."
  if ty.hasMVar || ty.hasLevelMVar then
    throwError "KernelCuts115 refuses an unresolved equality vector."
  return (carrier, left.consumeMData.headBeta, right.consumeMData.headBeta)

private partial def findConcreteComposition115 (e : Expr) (depth : Nat) :
    MetaM (Option (Expr × Expr)) := do
  if depth == 0 then throwError "KernelCuts115 exhausted its fixed expression-search depth."
  let e := stripSpineMetadata115 e
  let e ← projectionAsApplication115 e
  if e.getAppFn.isConstOf ``ConcreteCategory.hom then
    let .inductInfo ind ← getConstInfo ``ConcreteCategory
      | throwError "KernelCuts115 concrete-category metadata is not inductive."
    let homPrefixCount := ind.numParams + 1
    let args := e.getAppArgs
    if args.size == homPrefixCount + 3 then
      let comp ← projectionAsApplication115 (stripSpineMetadata115 args[homPrefixCount + 2]!)
      if comp.getAppFn.isConstOf ``CategoryStruct.comp then return some (e, comp)
  match e with
  | .app f a =>
    if let some result ← findConcreteComposition115 a (depth - 1) then return some result
    findConcreteComposition115 f (depth - 1)
  | .mdata _ major => findConcreteComposition115 major (depth - 1)
  | _ => return none

elab "basisCompositionLaw115% " "(" value:term ")" : term =>
    Term.withoutErrToSorry do
  let value ← appliedTerm115 value
  let .app function sectionValue :=
      stripSpineMetadata115 value
    | throwError "KernelCuts114 composition value is not a section application."
  let some (hom, comp) ← findConcreteComposition115 function 96
    | throwError "KernelCuts114 composition value has no exact concrete hom/composition."
  let .const _ levels := hom.getAppFn
    | throwError "KernelCuts114 concrete hom has no declared projection head."
  let .inductInfo homInd ← getConstInfo ``ConcreteCategory
    | throwError "KernelCuts114 concrete-category metadata is not inductive."
  let .inductInfo compInd ← getConstInfo ``CategoryStruct
    | throwError "KernelCuts114 category-structure metadata is not inductive."
  let homPrefix := homInd.numParams + 1
  let compPrefix := compInd.numParams + 1
  let homArgs := hom.getAppArgs
  let compArgs := comp.getAppArgs
  unless homArgs.size == homPrefix + 3 && compArgs.size == compPrefix + 5 do
    throwError "KernelCuts114 class-law stored vectors differ."
  let category ← equationHead115 compArgs[0]! 8
  let .const categoryName categoryLevels := category.getAppFn
    | throwError "KernelCuts115 stored category has no constant head."
  unless categoryName == ``ModuleCat && category.getAppArgs.size == 2 do
    throwError "KernelCuts115 requires the exact stored ModuleCat category and its R/Ring vector."
  let law ← getConstInfo ``ModuleCat.comp_apply
  -- Recover the law's formal universe vector from its own first object type.
  -- R and Ring are the first two binders; the next binder is object M.
  let .forallE _ _ afterR _ := law.type
    | throwError "KernelCuts115 module law has no R binder."
  let .forallE _ _ afterRing _ := afterR
    | throwError "KernelCuts115 module law has no Ring binder."
  let .forallE _ objectType _ _ := afterRing
    | throwError "KernelCuts115 module law has no first object binder."
  let .const formalName formalLevels := objectType.getAppFn
    | throwError "KernelCuts115 module law first object has no constant type head."
  unless formalName == ``ModuleCat && formalLevels.length == categoryLevels.length do
    throwError "KernelCuts115 module law object/category universe vectors differ."
  let mut levelAssignments : Array (Name × Level) := #[]
  for (formal, actual) in formalLevels.zip categoryLevels do
    let .param name := formal
      | throwError "KernelCuts115 module law object has a non-parameter universe."
    levelAssignments := levelAssignments.push (name, actual)
  let lawLevels ← law.levelParams.mapM fun name => do
    let some (_, actual) := levelAssignments.find? (fun pair => pair.1 == name)
      | throwError "KernelCuts115 module law has an unmatched universe parameter {name}."
    return actual
  let proof := mkAppN (mkConst law.name lawLevels)
    (category.getAppArgs ++
      compArgs.extract compPrefix (compPrefix + 3) ++
      #[compArgs[compPrefix + 3]!, compArgs[compPrefix + 4]!, sectionValue])
  let (_, ownLeft, _) ← ownEquality115 proof
  logInfo m!"KernelCuts115 ModuleCat class-law ordinary proof emitted: raw original application match={ownLeft.equal value}."
  return proof

elab "basisOuterContraction115% " "(" suppliedFunction:term ")"
    "(" suppliedProof:term ")" : term => Term.withoutErrToSorry do
  let outerApplication ← appliedTerm115 suppliedFunction
  let .app outerFunction _ :=
      stripSpineMetadata115 outerApplication
    | throwError "KernelCuts115 outer cut expects an exact mapped section application."
  let innerProof ← appliedTerm115 suppliedProof
  let (innerCarrier, innerOld, innerNew) ← ownEquality115 innerProof
  let outerCarrier ← instantiateMVars (← inferType (mkApp outerFunction innerOld))
  let innerLevel ← getLevel innerCarrier
  let outerLevel ← getLevel outerCarrier
  let proof := mkAppN (mkConst ``congrArg [innerLevel, outerLevel])
    #[innerCarrier, outerCarrier, innerOld, innerNew, outerFunction, innerProof]
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "KernelCuts114 outer cut refuses an unresolved or recovery proof."
  logInfo "KernelCuts115 outer ordinary congrArg proof emitted from the exact section application."
  return proof

end

private def actualOriginalIdealTwistPointClassCompositionLaw115
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let J := closedImmersionModule q
  let T := positiveSheafOfModules (grading I) 2
  let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
  let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
  let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
  exact fun (m : J.val.obj (op U)) => by
    exact basisCompositionLaw115%
      (((G.map ((actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
            (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
              ((Scheme.Modules.pullback q).obj T)
              (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom)) ≫
          G.map (actualOriginalUntwistedIdealPointChartIso p hp P hP).hom)
        (actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
          (actualModuleLocalTensorSection J T U m
            (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))))

private def actualOriginalIdealTwistPointOuterContractionLaw115
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let J := closedImmersionModule q
  let T := positiveSheafOfModules (grading I) 2
  let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
  let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
  let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
  exact fun (m : J.val.obj (op U)) => by
    exact basisOuterContraction115%
      ((G.map (actualOriginalUntwistedIdealPointChartIso p hp P hP).hom)
        (actualPointLocalSectionClass q J U hU m))
      (actualOriginalIdealTwistPointInnerContractionLaw114 p hp P hP m)

end PfaffianDescent
end

noncomputable section
namespace CasselsBasisResidue117
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

end CasselsBasisResidue117
end

namespace CasselsBasisStructuralCertificate117

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

end CasselsBasisStructuralCertificate117

meta section
namespace CasselsBasisStructuralCertificate117
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
      n == ``PfaffianDescent.closedImmersionIdealTwist || n == ``id
    | _ => false
  if !allowed then return e
  let some e' ← delta? e (fun n => isLocalLawName n ||
    n == ``AllCharacteristics.HomogeneousProjective.hypersurface ||
      n == ``PfaffianDescent.closedImmersionIdealTwist || n == ``id)
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
  let proof := mkAppN (mkConst ``CasselsBasisResidue117.native_commRing_eq levels) fieldArgs
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
  let proof := mkAppN (mkConst ``CasselsBasisResidue117.native_bundle_eq levels) ra
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
  let proof := mkAppN (mkConst ``CasselsBasisResidue117.native_carrier_eq levels) nativeArgs
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
  let proof := mkAppN (mkConst ``CasselsBasisResidue117.native_field_heq levels) la
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

end CasselsBasisStructuralCertificate117
end

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

meta section
open Lean Meta Elab Term

private def stripSpineMetadata117 : Expr → Expr
  | .mdata _ e => stripSpineMetadata117 e
  | .app f a => .app (stripSpineMetadata117 f) a
  | e => e

private partial def equationHead117 (e : Expr) (fuel : Nat) : MetaM Expr := do
  let e ← instantiateMVars e
  let e := stripSpineMetadata117 ((stripSpineMetadata117 e).headBeta)
  if fuel == 0 then return e
  match e with
  | .letE _ _ value body _ => equationHead117 (body.instantiate1 value) (fuel - 1)
  | .fvar id =>
    let decl ← id.getDecl
    if let some value := decl.value? then equationHead117 value (fuel - 1)
    else return e
  | _ =>
    if e.getAppFn.isConstOf ``id && e.getAppArgs.size == 2 then
      equationHead117 e.getAppArgs[1]! (fuel - 1)
    else return e

private def appliedTerm117 (stx : Syntax) : TermElabM Expr := do
  let term ← Term.elabTerm stx none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let term ← instantiateMVars term
  if term.hasMVar || term.hasLevelMVar || term.hasLooseBVars || term.hasSorry then
    throwError "KernelCuts117 refuses unresolved or recovery source terms."
  return term

private def ownEquality117 (proof : Expr) : MetaM (Expr × Expr × Expr) := do
  let ty ← equationHead117 (← inferType proof) 8
  let ty ← instantiateMVars ty
  let some (carrier, left, right) := ty.eq?
    | throwError "KernelCuts117 expected an ordinary equality proof."
  if ty.hasMVar || ty.hasLevelMVar then
    throwError "KernelCuts117 refuses an unresolved equality vector."
  return (carrier, left.consumeMData.headBeta, right.consumeMData.headBeta)

elab "basisSourceTypeCompatibility121% " "(" suppliedSource:term ")"
    "(" suppliedLeft:term ")" "(" suppliedOuter:term ")" : term =>
    Term.withoutErrToSorry do
  let sourceProof ← appliedTerm117 suppliedSource
  let leftValue ← appliedTerm117 suppliedLeft
  let outerProof ← appliedTerm117 suppliedOuter
  let sourceType ← equationHead117 (← inferType sourceProof) 8
  let sourceType ← instantiateMVars sourceType
  let (targetCarrier, _, targetRight) ← ownEquality117 outerProof
  let carrierLevel ← getLevel targetCarrier
  let targetType := mkAppN (mkConst ``Eq [carrierLevel])
    #[targetCarrier, leftValue, targetRight]
  let (heq, state) ←
    (CasselsBasisStructuralCertificate117.structuralHEq sourceType targetType
      96 #[] "sourceCompatibility121").run {}
  let proof ← mkEqOfHEq heq
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "KernelCuts117 source compatibility refuses unresolved or recovery proof."
  logInfo m!"KernelCuts121 source proposition compatibility emitted: native residue leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, confirmed fallback proofs={state.fallbackProofLeaves}, abstract congruence steps={state.congrSteps}, binder steps={state.binderSteps}, unused traversal budget={state.remaining}."
  return proof

end

private def actualOriginalIdealTwistPointSourceTypeCompatibility121
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let J := closedImmersionModule q
  let T := positiveSheafOfModules (grading I) 2
  let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
  let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
  let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
  exact fun (m : J.val.obj (op U)) => by
    exact basisSourceTypeCompatibility121%
      (actualOriginalIdealTwistPointFactoryLaw114 p hp P hP m)
      ((G.map (actualOriginalQuadraticConormalPointChartIso p hp P hP).hom)
        (actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
          (actualModuleLocalTensorSection J T U m
            (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))))
      (actualOriginalIdealTwistPointOuterContractionLaw115 p hp P hP m)

end PfaffianDescent
end

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Ordinary right-endpoint transport; every supplied endpoint remains explicit. -/
private theorem actualEquality_of_right122
    {A : Sort u} {left right applied : A}
    (hr : right = applied) (h : left = applied) : left = right :=
  h.trans hr.symm

meta section
open Lean Meta Elab Term

private def stripSpineMetadata122 : Expr → Expr
  | .mdata _ e => stripSpineMetadata122 e
  | .app f a => .app (stripSpineMetadata122 f) a
  | e => e

private partial def equationHead122 (e : Expr) (fuel : Nat) : MetaM Expr := do
  let e ← instantiateMVars e
  let e := stripSpineMetadata122 ((stripSpineMetadata122 e).headBeta)
  if fuel == 0 then return e
  match e with
  | .letE _ _ value body _ => equationHead122 (body.instantiate1 value) (fuel - 1)
  | .fvar id =>
    let decl ← id.getDecl
    if let some value := decl.value? then equationHead122 value (fuel - 1)
    else return e
  | _ =>
    if e.getAppFn.isConstOf ``id && e.getAppArgs.size == 2 then
      equationHead122 e.getAppArgs[1]! (fuel - 1)
    else return e

private def appliedTerm122 (stx : Syntax) : TermElabM Expr := do
  let term ← Term.elabTerm stx none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let term ← instantiateMVars term
  if term.hasMVar || term.hasLevelMVar || term.hasLooseBVars || term.hasSorry then
    throwError "KernelCuts122 refuses unresolved or recovery source terms."
  return term

private def ownEquality122 (proof : Expr) : MetaM (Expr × Expr × Expr) := do
  let ty ← equationHead122 (← inferType proof) 8
  let ty ← instantiateMVars ty
  let some (carrier, left, right) := ty.eq?
    | throwError "KernelCuts122 expected an ordinary equality proof."
  if ty.hasMVar || ty.hasLevelMVar then
    throwError "KernelCuts122 refuses an unresolved equality vector."
  return (carrier, left.consumeMData.headBeta, right.consumeMData.headBeta)

elab "basisSourceMp122% " "(" suppliedSource:term ")"
    "(" suppliedEquality:term ")" : term => Term.withoutErrToSorry do
  let sourceProof ← appliedTerm122 suppliedSource
  let typeProof ← appliedTerm122 suppliedEquality
  let (_, sourceProposition, targetProposition) ← ownEquality122 typeProof
  let sourceType ← equationHead122 (← inferType sourceProof) 8
  let proof := mkAppN (mkConst ``Eq.mp [Level.zero])
    #[sourceProposition, targetProposition, typeProof, sourceProof]
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "Assembly122 refuses unresolved or recovery source transport."
  logInfo m!"Assembly122 ordinary Eq.mp emitted: raw source proposition={sourceType.equal sourceProposition}."
  return proof

elab "basisRightTransport122% " "(" suppliedSource:term ")"
    "(" suppliedRight:term ")" : term => Term.withoutErrToSorry do
  let sourceProof ← appliedTerm122 suppliedSource
  let rightProof ← appliedTerm122 suppliedRight
  let (sourceCarrier, sourceLeft, sourceRight) ← ownEquality122 sourceProof
  let (rightCarrier, oldRight, newRight) ← ownEquality122 rightProof
  let carrierLevel ← getLevel rightCarrier
  let helper ← getConstInfo ``actualEquality_of_right122
  unless helper.levelParams.length == 1 do
    throwError "Assembly122 ordinary helper universe vector differs."
  let proof := mkAppN (mkConst helper.name [carrierLevel])
    #[rightCarrier, sourceLeft, oldRight, newRight, rightProof, sourceProof]
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "Assembly122 refuses unresolved or recovery right transport."
  logInfo m!"Assembly122 ordinary right-endpoint transport emitted: raw carrier={sourceCarrier.equal rightCarrier}, raw endpoint={sourceRight.equal newRight}."
  return proof

end

/- Separate ordinary assembly cut; normal kernel checking is required. -/
private def actualOriginalIdealTwistPointCertifiedFactoryLaw122
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let J := closedImmersionModule q
  let T := positiveSheafOfModules (grading I) 2
  let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
  let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
  let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
  exact fun (m : J.val.obj (op U)) => by
    exact basisSourceMp122%
      (actualOriginalIdealTwistPointFactoryLaw114 p hp P hP m)
      (actualOriginalIdealTwistPointSourceTypeCompatibility121 p hp P hP m)

/- Separate ordinary assembly cut; normal kernel checking is required. -/
private def actualOriginalIdealTwistPointMappedContractionSquare122
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let J := closedImmersionModule q
  let T := positiveSheafOfModules (grading I) 2
  let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
  let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
  let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
  exact fun (m : J.val.obj (op U)) => by
    exact basisRightTransport122%
      (actualOriginalIdealTwistPointCertifiedFactoryLaw122 p hp P hP m)
      (actualOriginalIdealTwistPointOuterContractionLaw115 p hp P hP m)

/- Separate ordinary assembly cut; normal kernel checking is required. -/
private def actualOriginalIdealTwistPointStoredMappedSquare122
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let J := closedImmersionModule q
  let T := positiveSheafOfModules (grading I) 2
  let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
  let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
  let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
  exact fun (m : J.val.obj (op U)) => by
    exact basisRightTransport122%
      (actualOriginalIdealTwistPointMappedContractionSquare122 p hp P hP m)
      (actualOriginalIdealTwistPointClassCompositionLaw115 p hp P hP m)

end PfaffianDescent
end

noncomputable section
namespace CasselsBasisResidue122
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

end CasselsBasisResidue122
end

namespace CasselsBasisStructuralCertificate122

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

end CasselsBasisStructuralCertificate122

meta section
namespace CasselsBasisStructuralCertificate122
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
      n == ``PfaffianDescent.closedImmersionIdealTwist || n == ``id
    | _ => false
  if !allowed then return e
  let some e' ← delta? e (fun n => isLocalLawName n ||
    n == ``AllCharacteristics.HomogeneousProjective.hypersurface ||
      n == ``PfaffianDescent.closedImmersionIdealTwist || n == ``id)
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
  let proof := mkAppN (mkConst ``CasselsBasisResidue122.native_commRing_eq levels) fieldArgs
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
  let proof := mkAppN (mkConst ``CasselsBasisResidue122.native_bundle_eq levels) ra
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
  let proof := mkAppN (mkConst ``CasselsBasisResidue122.native_carrier_eq levels) nativeArgs
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
  let proof := mkAppN (mkConst ``CasselsBasisResidue122.native_field_heq levels) la
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
  let proof := mkAppN (mkConst ``CasselsBasisResidue122.native_standard_bundle_eq levels) ra
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

end CasselsBasisStructuralCertificate122
end

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

meta section
open Lean Meta Elab Tactic

elab "basis_structural_exact124 " supplied:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← Term.elabTerm supplied none (catchExPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    let source ← instantiateMVars source
    let sourceType ← instantiateMVars (← inferType source)
    let target ← instantiateMVars (← goal.getType)
    let (heq, state) ←
      (CasselsBasisStructuralCertificate122.structuralHEq sourceType target
        96 #[] "public124").run {}
    let typeProof ← mkEqOfHEq heq
    let proof := mkAppN (mkConst ``Eq.mp [Level.zero])
      #[sourceType, target, typeProof, source]
    if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "Public124 refuses unresolved or recovery proof terms."
    logInfo m!"Public124 ordinary compatibility emitted: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruence steps={state.congrSteps}, binders={state.binderSteps}, unused traversal budget={state.remaining}."
    goal.assign proof
    replaceMainGoal []

/- Bounded syntactic head extraction for the actual proposition equality.
Metadata on the function spine is stripped before head-beta and each of the
already allowed let/local-let/id steps. No geometric definition is unfolded. -/
private def stripEqualitySpine128 : Expr → Expr
  | .mdata _ e => stripEqualitySpine128 e
  | .app f a => .app (stripEqualitySpine128 f) a
  | e => e

private partial def literalEqualityHead128 (e : Expr) (fuel : Nat) : MetaM Expr := do
  let e ← instantiateMVars e
  let e := stripEqualitySpine128 ((stripEqualitySpine128 e).headBeta)
  if fuel == 0 then return e
  match e with
  | .letE _ _ value body _ =>
    literalEqualityHead128 (body.instantiate1 value) (fuel - 1)
  | _ =>
    if let .fvar id := e.getAppFn then
      if let some value := (← id.getDecl).value? then
        return ← literalEqualityHead128 (mkAppN value e.getAppArgs) (fuel - 1)
    if e.getAppFn.isConstOf ``id && e.getAppArgs.size == 2 then
      literalEqualityHead128 e.getAppArgs[1]! (fuel - 1)
    else return e

private def literalHeadDiagnostic128 (e : Expr) : String :=
  let head := match e.getAppFn with
    | .const name _ => s!"constant {name}"
    | .fvar id => s!"local {id.name}"
    | .mdata .. => "metadata"
    | .lam .. => "lambda"
    | .forallE .. => "forall"
    | .letE .. => "let"
    | .proj name index _ => s!"projection {name}[{index}]"
    | _ => "other"
  s!"{head}; arguments={e.getAppArgs.size}; expression metavariables={e.hasMVar}; level metavariables={e.hasLevelMVar}"

/- Prove ONLY the proposition equality in the literal original telescope.
The left proposition is the cached proof's actual inferred type; the right is
read directly from this ordinary theorem's literal statement. -/
elab "basisLiteralTypeCompatibility130 " supplied:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← Term.elabTerm supplied none (catchExPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    let source ← instantiateMVars source
    let sourceType ← instantiateMVars (← inferType source)
    let goalType ← literalEqualityHead128 (← goal.getType) 8
    let some (_, expectedSource, literalTarget) := goalType.eq?
      | throwError "Literal130 expected an equality of the actual propositions after bounded head extraction: {literalHeadDiagnostic128 goalType}."
    let (heq, state) ←
      (CasselsBasisStructuralCertificate122.structuralHEq expectedSource literalTarget
        96 #[] "literalType130").run {}
    let proof ← mkEqOfHEq heq
    if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "Literal130 refuses unresolved or recovery compatibility terms."
    logInfo m!"Literal130 EXACT goal-vector proposition compatibility emitted: supplied source raw match={sourceType.equal expectedSource}, native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruence steps={state.congrSteps}, binders={state.binderSteps}, unused traversal budget={state.remaining}."
    goal.assign proof
    replaceMainGoal []

end

private theorem actualOriginalIdealTwistPointLiteralTypeCompatibility130
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
    let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
    let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
    ∀ m : J.val.obj (op U),
      (type_of% (actualOriginalIdealTwistPointStoredMappedSquare122 p hp P hP m)) =
      (
      G.map (actualOriginalQuadraticConormalPointChartIso p hp P hP).hom
        (actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
          (actualModuleLocalTensorSection J T U m
            (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))) =
      ((G.map ((actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
          (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
            ((Scheme.Modules.pullback q).obj T)
            (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom)) ≫
        G.map (actualOriginalUntwistedIdealPointChartIso p hp P hP).hom)
        (actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
          (actualModuleLocalTensorSection J T U m
            (actualOriginalPositiveTwoLocalBasisSection p hp P hP U)))) := by
  intro C I q J T f j U hU G m
  basisLiteralTypeCompatibility130 (actualOriginalIdealTwistPointStoredMappedSquare122 p hp P hP m)

private theorem actualOriginalIdealTwistPointAssociatedSquare130
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
    let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
    let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
    ∀ m : J.val.obj (op U),
      G.map (actualOriginalQuadraticConormalPointChartIso p hp P hP).hom
        (actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
          (actualModuleLocalTensorSection J T U m
            (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))) =
      ((G.map ((actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
          (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
            ((Scheme.Modules.pullback q).obj T)
            (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom)) ≫
        G.map (actualOriginalUntwistedIdealPointChartIso p hp P hP).hom)
        (actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
          (actualModuleLocalTensorSection J T U m
            (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))) := by
  intro C I q J T f j U hU G m
  basis_structural_exact124 (actualOriginalIdealTwistPointStoredMappedSquare122 p hp P hP m)

end PfaffianDescent
end

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u v w
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/- Exact ordinary abstract lemma already checked by root independently.
No project map or carrier is unfolded in this proof. -/
private theorem actualMapAssociatedApplication135
    {R : Type u} [Ring R] {C : Type v} [Category.{w} C]
    (F : C ⥤ ModuleCat.{u} R) {A B D E : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (x : F.obj A) :
    F.map (a ≫ b ≫ c) x = (F.map (a ≫ b) ≫ F.map c) x := by
  rw [← Category.assoc, Functor.map_comp]

meta section
open Lean Meta Elab Tactic

private def stripSpineMetadata135 : Expr → Expr
  | .mdata _ e => stripSpineMetadata135 e
  | .app f a => .app (stripSpineMetadata135 f) a
  | e => e

private partial def equationHead135 (e : Expr) (fuel : Nat) : MetaM Expr := do
  let e ← instantiateMVars e
  let e := stripSpineMetadata135 ((stripSpineMetadata135 e).headBeta)
  if fuel == 0 then return e
  match e with
  | .letE _ _ value body _ => equationHead135 (body.instantiate1 value) (fuel - 1)
  | .fvar id =>
    let decl ← id.getDecl
    if let some value := decl.value? then equationHead135 value (fuel - 1)
    else return e
  | _ =>
    if e.getAppFn.isConstOf ``id && e.getAppArgs.size == 2 then
      equationHead135 e.getAppArgs[1]! (fuel - 1)
    else return e

private def projectionAsApplication135 (e : Expr) : MetaM Expr := do
  let .proj structName idx major := e.getAppFn | return e
  let some info := getStructureInfo? (← getEnv) structName
    | throwError "Association135 missing structure projection metadata."
  let some projName := info.getProjFn? idx
    | throwError "Association135 missing declared projection function."
  let ty ← instantiateMVars (← whnfD (← inferType major))
  let .const typeName levels := ty.getAppFn
    | throwError "Association135 projection source has no structure type."
  unless typeName == structName && !ty.hasMVar && !ty.hasLevelMVar do
    throwError "Association135 projection structure differs or has unresolved variables."
  let .inductInfo ind ← getConstInfo structName
    | throwError "Association135 projection source is not inductive."
  let params := ty.getAppArgs.extract 0 ind.numParams
  return mkAppN (mkApp (mkAppN (mkConst projName levels) params) major) e.getAppArgs

/- Search the section's application function argument-first. The exact mapped
morphism is the final argument of its declared concrete hom projection. -/
private def applicationHead135 (e : Expr) : String :=
  let head := match e.getAppFn with
    | .const name _ => s!"constant {name}"
    | .fvar id => s!"local {id.name}"
    | .proj name index _ => s!"projection {name}[{index}]"
    | .lam .. => "lambda"
    | .letE .. => "let"
    | .mdata .. => "metadata"
    | _ => "other"
  s!"{head}; arguments={e.getAppArgs.size}"

private def applicationEdges135 (e : Expr) : String :=
  let args := e.getAppArgs
  if args.isEmpty then "no arguments"
  else if args.size == 1 then s!"arg[0]=({applicationHead135 args[0]!})"
  else s!"first=({applicationHead135 args[0]!}); last=({applicationHead135 args[args.size-1]!})"

private partial def findMappedMorphism135 (e : Expr) (depth : Nat) :
    MetaM (Option Expr) := do
  if depth == 0 then
    throwError "Association135 exhausted its fixed expression-search depth."
  let e := stripSpineMetadata135 e
  let e ← projectionAsApplication135 e
  -- Read the exact declared map independently of the coercion wrapper used
  -- to evaluate its ModuleCat morphism; partial application fragments do not
  -- qualify. This is a syntactic extraction, not a new equality assumption.
  if e.getAppFn.isConstOf ``CategoryTheory.Functor.map then
    let .inductInfo ind ← getConstInfo ``CategoryTheory.Functor
      | throwError "Association135 Functor metadata is not inductive."
    if e.getAppArgs.size == ind.numParams + 4 then return some e
  if e.getAppFn.isConstOf ``ConcreteCategory.hom then
    let .inductInfo ind ← getConstInfo ``ConcreteCategory
      | throwError "Association135 concrete-category metadata is not inductive."
    let homPrefixCount := ind.numParams + 1
    let args := e.getAppArgs
    if args.size == homPrefixCount + 3 then
      let mapped ← projectionAsApplication135
        (stripSpineMetadata135 args[homPrefixCount + 2]!)
      if mapped.getAppFn.isConstOf ``CategoryTheory.Functor.map then return some mapped
  match e with
  | .app f a =>
    if let some result ← findMappedMorphism135 a (depth - 1) then return some result
    findMappedMorphism135 f (depth - 1)
  | .mdata _ major => findMappedMorphism135 major (depth - 1)
  | _ => return none

/- Recover the ordinary lemma's universe parameters from the stored Functor
type, matching only raw universe syntax. No conversion is used for levels. -/
private partial def matchLevel135 (formal actual : Level)
    (assignments : Array (Name × Level)) (depth : Nat) :
    MetaM (Array (Name × Level)) := do
  if depth == 0 then throwError "Association135 exhausted fixed universe depth."
  match formal with
  | .param name =>
    if let some (_, prior) := assignments.find? (fun pair => pair.1 == name) then
      unless prior == actual do
        throwError "Association135 inconsistent raw universe assignment {name}."
      return assignments
    return assignments.push (name, actual)
  | .succ formal =>
    let .succ actual := actual
      | throwError "Association135 stored universe has a different successor shape."
    matchLevel135 formal actual assignments (depth - 1)
  | .max a b =>
    let .max c d := actual
      | throwError "Association135 stored universe has a different max shape."
    let assignments ← matchLevel135 a c assignments (depth - 1)
    matchLevel135 b d assignments (depth - 1)
  | .imax a b =>
    let .imax c d := actual
      | throwError "Association135 stored universe has a different imax shape."
    let assignments ← matchLevel135 a c assignments (depth - 1)
    matchLevel135 b d assignments (depth - 1)
  | .zero =>
    unless actual == .zero do throwError "Association135 stored universe differs from zero."
    return assignments
  | .mvar _ => throwError "Association135 refuses formal universe metavariables."

private def binderDomain135 (e : Expr) (index : Nat) : MetaM Expr := do
  match e, index with
  | .forallE _ domain _ _, 0 => return domain
  | .forallE _ _ body _, index + 1 => binderDomain135 body index
  | _, _ => throwError "Association135 ordinary helper binder vector differs."

elab "basisLiteralAssociation135" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← equationHead135 (← goal.getType) 8
    let some (carrier, originalValue, associatedValue) := target.eq?
      | throwError "Association135 requires the exact original/associated value equality."
    let .app function sectionValue := stripSpineMetadata135 originalValue
      | throwError "Association135 original mapped value is not a section application."
    let some mapped ← findMappedMorphism135 function 96
      | throwError "Association135 found no full declared CategoryTheory.Functor.map in the exact application function: {applicationHead135 function}; {applicationEdges135 function}."
    let .inductInfo functorInd ← getConstInfo ``CategoryTheory.Functor
      | throwError "Association135 Functor metadata is not inductive."
    let mapPrefixCount := functorInd.numParams + 1
    let mapArgs := mapped.getAppArgs
    unless mapArgs.size == mapPrefixCount + 3 do
      throwError "Association135 exact Functor.map argument vector differs."
    let sourceCategory := mapArgs[0]!
    let sourceInstance := mapArgs[1]!
    let moduleCategory ← equationHead135 mapArgs[2]! 8
    unless moduleCategory.getAppFn.isConstOf ``ModuleCat &&
        moduleCategory.getAppArgs.size == 2 do
      throwError "Association135 requires the stored ModuleCat R/Ring vector."
    let functor := mapArgs[mapPrefixCount - 1]!
    let outer ← projectionAsApplication135
      (stripSpineMetadata135 mapArgs[mapPrefixCount + 2]!)
    unless outer.getAppFn.isConstOf ``CategoryStruct.comp do
      throwError "Association135 original mapped morphism has no outer composition."
    let .inductInfo compInd ← getConstInfo ``CategoryStruct
      | throwError "Association135 category-structure metadata is not inductive."
    let compPrefixCount := compInd.numParams + 1
    let outerArgs := outer.getAppArgs
    unless outerArgs.size == compPrefixCount + 5 do
      throwError "Association135 outer composition argument vector differs."
    let inner ← projectionAsApplication135
      (stripSpineMetadata135 outerArgs[compPrefixCount + 4]!)
    unless inner.getAppFn.isConstOf ``CategoryStruct.comp &&
        inner.getAppArgs.size == compPrefixCount + 5 do
      throwError "Association135 requires the original right-associated three arrows."
    let innerArgs := inner.getAppArgs
    let helper ← getConstInfo ``actualMapAssociatedApplication135
    let formalFunctorType ← binderDomain135 helper.type 4
    let actualFunctorType ← equationHead135 (← inferType functor) 8
    let .const formalName formalLevels := formalFunctorType.getAppFn
      | throwError "Association135 abstract helper has no declared Functor type."
    let .const actualName actualLevels := actualFunctorType.getAppFn
      | throwError "Association135 stored functor has no declared Functor type."
    unless formalName == ``CategoryTheory.Functor && actualName == ``CategoryTheory.Functor &&
        formalLevels.length == actualLevels.length do
      throwError "Association135 formal/stored Functor universe vectors differ."
    let mut assignments : Array (Name × Level) := #[]
    for (formal, actual) in formalLevels.zip actualLevels do
      assignments ← matchLevel135 formal actual assignments 8
    let helperLevels ← helper.levelParams.mapM fun name => do
      let some (_, actual) := assignments.find? (fun pair => pair.1 == name)
        | throwError "Association135 unmatched ordinary helper universe {name}."
      return actual
    let proof := mkAppN (mkConst helper.name helperLevels)
      (moduleCategory.getAppArgs ++ #[sourceCategory, sourceInstance, functor,
        outerArgs[compPrefixCount]!, outerArgs[compPrefixCount + 1]!,
        innerArgs[compPrefixCount + 1]!, outerArgs[compPrefixCount + 2]!,
        outerArgs[compPrefixCount + 3]!, innerArgs[compPrefixCount + 3]!,
        innerArgs[compPrefixCount + 4]!, sectionValue])
    let proofType ← equationHead135 (← inferType proof) 8
    let some (ownCarrier, ownOriginal, ownAssociated) := proofType.eq?
      | throwError "Association135 ordinary application law is not an equality."
    if target.hasMVar || target.hasLevelMVar || proof.hasMVar ||
        proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "Association135 refuses unresolved or recovery proof terms."
    logInfo m!"Association135 ordinary exact-vector application emitted: raw carrier={ownCarrier.equal carrier}, raw original={ownOriginal.equal originalValue}, raw associated={ownAssociated.equal associatedValue}."
    goal.assign proof
    replaceMainGoal []

end

private theorem actualOriginalIdealTwistPointMappedAssociation135
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
    let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
    let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
    ∀ m : J.val.obj (op U),
      G.map ((actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
        (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
          ((Scheme.Modules.pullback q).obj T)
          (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom ≫
        (actualOriginalUntwistedIdealPointChartIso p hp P hP).hom)
        (actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
          (actualModuleLocalTensorSection J T U m
            (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))) =
      ((G.map ((actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
          (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
            ((Scheme.Modules.pullback q).obj T)
            (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom)) ≫
        G.map (actualOriginalUntwistedIdealPointChartIso p hp P hP).hom)
        (actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
          (actualModuleLocalTensorSection J T U m
            (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))) := by
  intro C I q J T f j U hU G m
  basisLiteralAssociation135

end PfaffianDescent
end

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

meta section
open Lean Meta Elab Term

end

lemma actualOriginalIdealTwistPointBasisSquare
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
    let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
    let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
    ∀ m : J.val.obj (op U),
      G.map (actualOriginalQuadraticConormalPointChartIso p hp P hP).hom
        (actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
          (actualModuleLocalTensorSection J T U m
            (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))) =
      G.map ((actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
        (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
          ((Scheme.Modules.pullback q).obj T)
          (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom ≫
        (actualOriginalUntwistedIdealPointChartIso p hp P hP).hom)
        (actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
          (actualModuleLocalTensorSection J T U m
            (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))) := by
  intro C I q J T f j U hU G m
  basis_structural_exact124
    (basisRightTransport122%
      (actualOriginalIdealTwistPointAssociatedSquare130 p hp P hP m)
      (actualOriginalIdealTwistPointMappedAssociation135 p hp P hP m))

lemma actualOriginalIdealTwistPointUntwistContraction
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
    let hU : q ⁻¹ᵁ U = ⊤ := actualFieldPointFactor_preimage_image_top f j q C.factorization
    let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
    ∀ m : J.val.obj (op U),
      G.map ((actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
        (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
          ((Scheme.Modules.pullback q).obj T)
          (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom)
        (actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
          (actualModuleLocalTensorSection J T U m
            (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))) =
      actualPointLocalSectionClass q J U hU m := by
  intro C I q J T f j U hU G m
  basis_structural_exact124 (actualOriginalIdealTwistPointInnerContractionLaw114 p hp P hP m)

end PfaffianDescent
end

