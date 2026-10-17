import Lean
import Lean.Util.Sorry
import Lean.Meta.Tactic.Delta
import Lean.Meta.Eqns
import PfaffianDescent.ActualModulePointChartSourceFactorization
import PfaffianDescent.ActualOriginalNativeQuadraticIdealSection

/- SOURCE ONLY / UNVERIFIED. The actual ORIGINAL point fiber of
I_(P,S)⊗O_S(2) maps to the SAME residue ideal point fiber, using the
internally derived chart factorization and actual native O2 chart generator. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist IdealSheafDataModule
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def actualOriginalQuadraticConormalPointChartIso
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    (Scheme.Modules.pullback q).obj
      (closedImmersionIdealTwist q (positiveSheafOfModules (grading I) 2)) ≅
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom C.residue))).obj
      (closedImmersionModule (Spec.map (CommRingCat.ofHom C.residue))) := by
  dsimp only
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let M := closedImmersionIdealTwist q (positiveSheafOfModules (grading I) 2)
  exact actualModulePointChartSourceFactorizationIso (chartι I C.index) j q C.factorization
    M (closedImmersionModule j) (actualOriginalNativeIdealTwistChartIso p hp P hP)

/- The full equation uses the factory's stored elaborated value as RHS.
No newly reconstructed whole-Iso equality is proved by conversion. -/
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let some equation ← getUnfoldEqnFor?
    ``actualOriginalQuadraticConormalPointChartIso (nonRec := true)
    | throwError "Original point chart factory has no stored unfold equation."
  logInfo m!"Original point chart stored equation: {equation}"

private def actualOriginalPointChartStoredEquationValue
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :=
  actualOriginalQuadraticConormalPointChartIso.eq_def p hp P hP

private opaque actualOriginalPointChartStoredEquationProof
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    type_of% (actualOriginalPointChartStoredEquationValue p hp P hP) :=
  actualOriginalPointChartStoredEquationValue p hp P hP

universe v

/- Whole-value equality transport is proved before any concrete scheme,
residue ring, point section or Iso is instantiated. -/
private theorem actualPointChartLaw_of_storedEquation
    {A : Sort v} {a b : A} (hab : a = b)
    (L : A → Prop) (h : L b) : L a := by
  cases hab
  exact h

/- Supplying only the checked stored equation fixes its EXACT RHS.
The section predicate and its proof remain unapplied. -/
private def actualOriginalPointChartStoredIsoTransferValue
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :=
  actualPointChartLaw_of_storedEquation
    (actualOriginalPointChartStoredEquationProof p hp P hP)

private opaque actualOriginalPointChartStoredIsoTransfer
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    type_of% (actualOriginalPointChartStoredIsoTransferValue p hp P hP) :=
  actualOriginalPointChartStoredIsoTransferValue p hp P hP

/- Select the literal section formula on the full Iso carrier that the
stored equation itself supplied, before supplying a section proof. -/
set_option backward.isDefEq.respectTransparency false in
private def actualOriginalPointChartSectionCriterionValue
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let M := closedImmersionIdealTwist q (positiveSheafOfModules (grading I) 2)
  letI : Algebra K (ChartRing I C.index) := (chartBaseMap I C.index).toAlgebra
  letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  exact actualOriginalPointChartStoredIsoTransfer p hp P hP
    (fun E =>
      (moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))).map E.hom
        (actualModulePointSectionClass q M
          (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)) =
      actualModulePointSectionClass j (closedImmersionModule j)
        (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue
          ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
            actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩))

private opaque actualOriginalPointChartSectionCriterion
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (actualOriginalPointChartSectionCriterionValue p hp P hP s) :=
  actualOriginalPointChartSectionCriterionValue p hp P hP s


end PfaffianDescent
end

meta section
namespace CasselsPointStoredVector077
open Lean Meta Elab Term

private def rejectUnresolved077 (e : Expr) : TermElabM Unit := do
  if e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
    throwError "077 refuses unresolved metavariables, loose bound variables or recovery proofs."

-- Pure forall substitution. No whnf, typeclass search or factory reduction.
private def instantiateBinders077 (type : Expr) (args : Array Expr) : TermElabM Expr := do
  let mut type := type
  for arg in args do
    let .forallE _ _ body _ := type.consumeMData
      | throwError "077 stored/API binder count did not match its argument vector."
    type := body.instantiate1 arg
  return type

-- Bound pure head beta/zeta and id removal; no other definition is unfolded.
private def peelStoredHead077 : Expr → Nat → Expr
  | e, 0 => e.consumeMData.headBeta
  | e, fuel + 1 =>
    let e := e.consumeMData.headBeta
    match e with
    | .letE _ _ value body _ => peelStoredHead077 (body.instantiate1 value) fuel
    | _ =>
      if e.getAppFn.isConstOf ``id && e.getAppArgs.size == 2 then
        peelStoredHead077 (e.getAppArgs[1]!) fuel
      else e

elab "storedPointFactorizationSection077% " "(" factory:term ")"
    "(" sourceSection:term ")" "(" chartSection:term ")" "(" square:term ")" : term =>
    Term.withoutErrToSorry do
  let factoryExpr ← Term.elabTerm factory none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let factoryExpr ← instantiateMVars factoryExpr
  rejectUnresolved077 factoryExpr
  let .const factoryName factoryLevels := factoryExpr.getAppFn
    | throwError "077 expects the original factory constant application."
  unless factoryName == ``PfaffianDescent.actualOriginalQuadraticConormalPointChartIso &&
      factoryExpr.getAppArgs.size == 7 && factoryLevels.length == 1 do
    throwError "077 expects the original factory's seven arguments and one universe."
  let some equationInfo := (← getEnv).find?
      ``PfaffianDescent.actualOriginalQuadraticConormalPointChartIso.eq_def
    | throwError "077 requires the ALREADY EXISTING stored original eq_def."
  unless equationInfo.levelParams.length == factoryLevels.length do
    throwError "077 stored equation universe arity differs from the factory."
  let equationType ← instantiateTypeLevelParams equationInfo.toConstantVal factoryLevels
  let equationType ← instantiateBinders077 equationType factoryExpr.getAppArgs
  let equationType := peelStoredHead077 equationType 32
  unless equationType.getAppFn.isConstOf ``Eq && equationType.getAppArgs.size == 3 do
    throwError "077 stored equation did not specialize to an equality."
  let rhs := peelStoredHead077 (equationType.getAppArgs[2]!) 32
  rejectUnresolved077 rhs
  let .const coreName coreLevels := rhs.getAppFn
    | throwError "077 stored RHS did not expose a constant factorization head."
  let coreArgs := rhs.getAppArgs
  unless coreName == ``PfaffianDescent.actualModulePointChartSourceFactorizationIso &&
      coreArgs.size == 12 && coreLevels == factoryLevels do
    throwError "077 stored RHS head={coreName}, arguments={coreArgs.size}, universes={coreLevels.length}; expected the twelve-argument original factorization Iso."
  let coreInfo ← getConstInfo coreName
  let sectionInfo ← getConstInfo ``PfaffianDescent.actualModulePointChartSourceFactorization_section
  unless coreInfo.levelParams.length == 1 && sectionInfo.levelParams.length == 1 do
    throwError "077 factorization APIs must each have exactly one universe."
  let mut proof := mkAppN (mkConst sectionInfo.name coreLevels) coreArgs
  let sectionType ← instantiateTypeLevelParams sectionInfo.toConstantVal coreLevels
  let mut remainingType ← instantiateBinders077 sectionType coreArgs
  for stx in [sourceSection.raw, chartSection.raw, square.raw] do
    let .forallE _ expectedType body _ := remainingType.consumeMData
      | throwError "077 section theorem did not have exactly the final three argument binders."
    let argument ← Term.elabTermEnsuringType stx (some expectedType) (catchExPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    let argument ← instantiateMVars argument
    rejectUnresolved077 argument
    proof := mkApp proof argument
    remainingType := body.instantiate1 argument
  rejectUnresolved077 proof
  rejectUnresolved077 remainingType
  remainingType := remainingType.consumeMData
  unless remainingType.getAppFn.isConstOf ``Eq && remainingType.getAppArgs.size == 3 do
    throwError "077 fully supplied section theorem did not conclude an equality."
  logInfo "077 emitted ordinary section theorem using the exact stored twelve-argument Iso vector."
  return proof

end CasselsPointStoredVector077
end

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist IdealSheafDataModule
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/- Elaborate v/t/native square against the stored API vector; do not
reconstruct or infer its L, Field, open-instance, q, j, M, N or whole Iso. -/
set_option backward.isDefEq.respectTransparency false in
private def actualOriginalStoredVectorPointSectionValue
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) := by
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  letI : Algebra K (ChartRing I C.index) := (chartBaseMap I C.index).toAlgebra
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom C.residue)) :=
    IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  exact storedPointFactorizationSection077%
    (actualOriginalQuadraticConormalPointChartIso p hp P hP)
    (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue
      ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩)
    (actualOriginalNativeQuadraticIdealChartSection_eq_native p hp P hP s)

private opaque actualOriginalStoredVectorPointSectionProof
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (actualOriginalStoredVectorPointSectionValue p hp P hP s) :=
  actualOriginalStoredVectorPointSectionValue p hp P hP s


end PfaffianDescent
end

noncomputable section
namespace CasselsPointResidueLeaves084
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

end CasselsPointResidueLeaves084
end

namespace CasselsPointStructuralCertificate086

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

end CasselsPointStructuralCertificate086

meta section
namespace CasselsPointStructuralCertificate086
open Lean Meta Elab Tactic

private def isLocalLawName (n : Name) : Bool :=
  match n with
  | .str _ s => s == "actualIdealChartLocalBasisLaw"
  | _ => false

/-- Only the already diagnosed predicate and identity/scheme aliases are
expanded. Native factories, choice and residue wrappers stay opaque. -/
private partial def normalizeHead (e : Expr) (fuel : Nat) : MetaM Expr := do
  let e := e.consumeMData.headBeta
  if fuel == 0 then return e
  if let .letE _ _ val body _ := e then
    return ← normalizeHead (body.instantiate1 val) (fuel - 1)
  let allowed := match e.getAppFn with
    | .const n _ => isLocalLawName n ||
      n == ``AllCharacteristics.HomogeneousProjective.hypersurface || n == ``id
    | _ => false
  if !allowed then return e
  let some e' ← delta? e (fun n => isLocalLawName n ||
    n == ``AllCharacteristics.HomogeneousProjective.hypersurface || n == ``id)
    | return e
  normalizeHead e' (fuel - 1)

/-- Turn a projection head into its declared projection function. No value
of the projected structure is unfolded. -/
private def projectionAsApplication (e : Expr) : MetaM Expr := do
  let .proj structName idx major := e.getAppFn | return e
  let some info := getStructureInfo? (← getEnv) structName
    | throwError "PointStructural086 cannot recover structure metadata for {structName}."
  let some projName := info.getProjFn? idx
    | throwError "PointStructural086 cannot recover projection {structName}[{idx}]."
  let ty ← whnfD (← inferType major)
  let .const typeName levels := ty.getAppFn
    | throwError "PointStructural086 projection source has no structure type."
  unless typeName == structName do
    throwError "PointStructural086 projection source structure differs: {structName} / {typeName}."
  let .inductInfo ind ← getConstInfo structName
    | throwError "PointStructural086 projection source is not inductive."
  let params := ty.getAppArgs.extract 0 ind.numParams
  return mkAppN (mkApp (mkAppN (mkConst projName levels) params) major) e.getAppArgs

/-- Recognize exactly the four residue wrapper boundaries diagnosed in080.
No geometric construction, stalk value, or residue-ring value is unfolded. -/
private def nativeResidueArguments? (e : Expr) : Option (List Level × Array Expr) :=
  let args := e.getAppArgs
  match e.getAppFn with
  | .const n levels =>
    if (n == ``AlgebraicGeometry.Scheme.residueField ||
        n == ``AlgebraicGeometry.Scheme.instFieldCarrierResidueField) &&
        args.size == 2 && levels.length == 1 then some (levels, args)
    else none
  | _ => none

private def wrapperLeaf? (left right : Expr) : MetaM (Option Expr) := do
  let la := left.getAppArgs
  let ra := right.getAppArgs
  let mut leaf : Option (Name × List Level × Array Expr × Bool) := none
  if left.getAppFn.isConstOf ``Field.toCommRing && la.size == 2 &&
      right.getAppFn.isConstOf ``CommRingCat.instCommRingObjForgetRingHomCarrier &&
      ra.size == 1 then
    if let some (levels, args) := nativeResidueArguments? la[1]! then
      leaf := some (``CasselsPointResidueLeaves084.native_commRing_eq,
        levels, args, false)
  else if left.getAppFn.isConstOf ``CommRingCat.of && la.size == 2 &&
      right.getAppFn.isConstOf ``AlgebraicGeometry.Scheme.residueField && ra.size == 2 then
    if let some (levels, args) := nativeResidueArguments? right then
      leaf := some (``CasselsPointResidueLeaves084.native_bundle_eq,
        levels, args, false)
  else if left.getAppFn.isConstOf ``CommRingCat.carrier && la.size == 1 &&
      right.getAppFn.isConstOf ``IsLocalRing.ResidueField && ra.size == 3 then
    if let some (levels, args) := nativeResidueArguments? la[0]! then
      leaf := some (``CasselsPointResidueLeaves084.native_carrier_eq,
        levels, args, false)
  else if left.getAppFn.isConstOf ``AlgebraicGeometry.Scheme.instFieldCarrierResidueField &&
      la.size == 2 && right.getAppFn.isConstOf ``IsLocalRing.ResidueField.field &&
      ra.size == 3 then
    if let some (levels, args) := nativeResidueArguments? left then
      leaf := some (``CasselsPointResidueLeaves084.native_field_heq,
        levels, args, true)
  let some (name, levels, args, alreadyHEq) := leaf | return none
  let proof := mkAppN (mkConst name levels) args
  if alreadyHEq then return some proof
  return some (← mkHEqOfEq proof)

private def diagnosticBool : LBool → String
  | .true => "true"
  | .false => "false"
  | .undef => "undef"

private def diagnosticHead (e : Expr) : String :=
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

private def diagnosticArguments (e : Expr) : String :=
  let args := e.getAppArgs
  if args.isEmpty then "none"
  else if args.size == 1 then s!"arg[0]={diagnosticHead args[0]!}"
  else s!"arg[0]={diagnosticHead args[0]!}; arg[1]={diagnosticHead args[1]!}"

private structure CertificateState where
  remaining : Nat := 1024
  pairs : Array (Expr × Expr × Expr) := #[]
  congruences : Array (Expr × Nat × CongrTheorem) := #[]
  proofLeaves : Nat := 0
  wrapperLeaves : Nat := 0
  congrSteps : Nat := 0
  binderSteps : Nat := 0

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
  if left0.equal right0 then return ← mkHEqRefl left0
  if let some (_, _, h) := locals.find? fun (l, r, _) =>
      l.equal left0 && r.equal right0 then
    return h
  if let some (_, _, h) := (← get).pairs.find? fun (l, r, _) =>
      l.equal left0 && r.equal right0 then
    return h
  if depth == 0 || (← get).remaining == 0 then
    throwError "PointStructural086 certificate traversal exhausted its explicit bound."
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
  if let some h ← wrapperLeaf? left right then
    modify fun s => { s with wrapperLeaves := s.wrapperLeaves + 1 }
    return ← cache left0 right0 h
  if let some h ← wrapperLeaf? right left then
    modify fun s => { s with wrapperLeaves := s.wrapperLeaves + 1 }
    return ← cache left0 right0 (← mkHEqSymm h)
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
    logInfo m!"PointStructural086 unsupported path: {path}"
    logInfo m!"PointStructural086 left boundary: {diagnosticHead left}"
    logInfo m!"PointStructural086 right boundary: {diagnosticHead right}"
    logInfo m!"PointStructural086 left first arguments: {diagnosticArguments left}"
    logInfo m!"PointStructural086 right first arguments: {diagnosticArguments right}"
    logInfo m!"PointStructural086 proofQuick classifications: left={diagnosticBool lp}, right={diagnosticBool rp}"
    throwError "PointStructural086 found an unsupported non-proof head boundary at {path}."
  let thm ← congruenceFor lh la.size
  let mut args := #[]
  for i in [:la.size] do
    let h ← structuralHEq la[i]! ra[i]! (depth - 1) locals (path ++ s!".arg[{i}]")
    let h ← match thm.argKinds[i]! with
      | .eq => mkEqOfHEq h
      | .heq => pure h
      | _ => throwError "PointStructural086 unexpected abstract congruence argument kind."
    args := args ++ #[la[i]!, ra[i]!, h]
  modify fun s => { s with congrSteps := s.congrSteps + 1 }
  cache left0 right0 (mkAppN thm.proof args)

/-- Certify the raw proof against the original criterion's actual premise,
apply that original criterion, then certify its result against the literal goal.
Both casts and the criterion application occur in the ordinary theorem body. -/
elab "cassels_point_criterion_exact086 " "(" criterionStx:term ")"
    "(" rawStx:term ")" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let criterion ← Term.elabTerm criterionStx none
    let raw ← Term.elabTerm rawStx none
    Term.synthesizeSyntheticMVarsNoPostponing
    let criterion ← instantiateMVars criterion
    let raw ← instantiateMVars raw
    let criterionType ← normalizeHead (← inferType criterion) 8
    let .forallE _ premise conclusion _ := criterionType
      | throwError "PointStructural086 expected the original criterion's raw-law premise."
    let rawType ← inferType raw
    let (rawHEq, firstState) ← (structuralHEq rawType premise 96 #[] "raw").run {}
    let rawEq ← mkEqOfHEq rawHEq
    let certifiedRaw := mkAppN (mkConst ``Eq.mp [Level.zero])
      #[rawType, premise, rawEq, raw]
    let completed := mkApp criterion certifiedRaw
    let completedType := conclusion.instantiate1 certifiedRaw
    let target ← goal.getType
    let (finalHEq, finalState) ← (structuralHEq completedType target 96 #[] "endpoint").run {}
    let finalEq ← mkEqOfHEq finalHEq
    let finalProof := mkAppN (mkConst ``Eq.mp [Level.zero])
      #[completedType, target, finalEq, completed]
    logInfo m!"PointStructural086 raw certificate: wrapper leaves={firstState.wrapperLeaves}, proof leaves={firstState.proofLeaves}, abstract congruence steps={firstState.congrSteps}, binder steps={firstState.binderSteps}, unused traversal budget={firstState.remaining}."
    logInfo m!"PointStructural086 endpoint certificate: wrapper leaves={finalState.wrapperLeaves}, proof leaves={finalState.proofLeaves}, abstract congruence steps={finalState.congrSteps}, binder steps={finalState.binderSteps}, unused traversal budget={finalState.remaining}."
    goal.assign finalProof
    replaceMainGoal []

end CasselsPointStructuralCertificate086
end

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist IdealSheafDataModule
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

lemma actualOriginalQuadraticConormalPointChartIso_section
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := closedImmersionIdealTwist q (positiveSheafOfModules (grading I) 2)
    letI : Algebra K (ChartRing I C.index) := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom C.residue)) :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    (moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))).map
      (actualOriginalQuadraticConormalPointChartIso p hp P hP).hom
      (actualModulePointSectionClass q M
        (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)) =
    actualModulePointSectionClass (Spec.map (CommRingCat.ofHom C.residue))
      (closedImmersionModule (Spec.map (CommRingCat.ofHom C.residue)))
      (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue
        ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
          actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩) := by
  cassels_point_criterion_exact086
    (actualOriginalPointChartSectionCriterion p hp P hP s)
    (actualOriginalStoredVectorPointSectionProof p hp P hP s)

end PfaffianDescent
end
