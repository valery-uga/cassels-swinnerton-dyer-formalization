import PfaffianDescent.ActualP3QuadraticDictionaryFactorNaturality
import PfaffianDescent.ActualOriginalPositiveTwoNativeJetHZeroKernel

/-! SOURCE ONLY / UNVERIFIED. SAME original point, SAME embedded dual jet,
and actual ambient ideal-sheaf H0 inclusion, independently of global Phi.
The square is derived from the genuine native kernel equivalence and
accepted augmentation/naturality, with no supplied comparison input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroReductionFactorization005
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K
      ((hypersurface p hp).residueField P.1) ((hypersurface p hp).residueField P.1)).toRingHom) ≫
      (actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell ≫
        quotientProjMap (equationIdeal p hp)) =
      (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp) := by
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K
    ((hypersurface p hp).residueField P.1) ((hypersurface p hp).residueField P.1)).toRingHom)
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  let a : hypersurface p hp ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
    quotientProjMap (equationIdeal p hp)
  have hred : r ≫ d = (hypersurface p hp).fromSpecResidueField P.1 :=
    actualOriginalPositiveTwoNativeJetEmbedding_reduction p hp P hP ell
  exact (Category.assoc r d a).symm.trans
    (congrArg (fun f : Spec (CommRingCat.of ((hypersurface p hp).residueField P.1)) ⟶
      hypersurface p hp => f ≫ a) hred)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The genuine induced H0(I_d(2)) -> H0(I_P(2)) map. The factorization
of the original reduced point through d is the proved native reduction. -/
def actualOriginalPositiveTwoNativeJetHZeroSheafInclusion
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)) →ₗ[K]
      ActualOriginalPointIdealQuadraticSections p hp P := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫
    quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  exact actualAmbientClosedIdealTwistHZeroFactorInclusion
    (ambientToBase (R := K) (σ := Fin 4)) i r q hfac
    (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The existing kernel equivalence preserves the original polynomial,
by its actual native construction and value-preserving dictionary. -/
lemma actualOriginalPositiveTwoNativeJetHZeroKernelEquiv_polynomial
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
    (p3ActualIdealQuadraticIntrinsicLinearEquiv
      ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp))
      ((actualOriginalPositiveTwoNativeJetHZeroKernelEquiv p hp P hP ell hell s).val)).val =
      (p3ActualIdealQuadraticIntrinsicLinearEquiv
        (d ≫ quotientProjMap (equationIdeal p hp)) s).val := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let E2 := ActualOriginalPositiveTwoFiber p hp P
  letI : Module K E2 := Module.compHom E2 (algebraMap K L)
  letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  let EP := p3ActualIdealQuadraticIntrinsicLinearEquiv
    ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp))
  let EZ := p3ActualIdealQuadraticIntrinsicLinearEquiv
    (d ≫ quotientProjMap (equationIdeal p hp))
  dsimp only [actualOriginalPositiveTwoNativeJetHZeroKernelEquiv,
    LinearEquiv.trans_apply, submoduleKernelThroughLinearEquiv]
  exact congrArg (fun z : intrinsicFullQuadraticSystem
    ((hypersurface p hp).fromSpecResidueField P.1 ≫
      quotientProjMap (equationIdeal p hp)) => z.val) (EP.apply_symm_apply _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSections_eq_of_polynomial_eq003
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)) [IsClosedImmersion i]
    (a b : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)))
    (h : (p3ActualIdealQuadraticIntrinsicLinearEquiv i a).val =
      (p3ActualIdealQuadraticIntrinsicLinearEquiv i b).val) : a = b :=
  (p3ActualIdealQuadraticIntrinsicLinearEquiv i).injective (Subtype.ext h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private abbrev nativeHZeroSheafInclusion_map_proposition006
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) : Prop :=
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    actualOriginalPositiveTwoNativeJetHZeroSheafInclusion p hp P hP ell hell =
      actualAmbientClosedIdealTwistHZeroFactorInclusion
        (ambientToBase (R := K) (σ := Fin 4)) i r q hfac
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)


meta section
open Lean Meta Elab Tactic

/-- Beta/zeta of the stored value only; no native factory or map is unfolded. -/
private def nativeHZeroHeadZeta006 : Nat → Expr → Expr
  | 0, e => e.consumeMData.headBeta
  | fuel + 1, e =>
      let e := e.consumeMData.headBeta
      match e with
      | .letE _ _ value body _ => nativeHZeroHeadZeta006 fuel (body.instantiate1 value)
      | _ => e

private def nativeHZeroHeadLabel006 (e : Expr) : String :=
  match e.consumeMData.getAppFn with
  | .const n _ => n.toString
  | .fvar _ => "local"
  | .lam .. => "lambda"
  | .forallE .. => "forall"
  | .letE .. => "let"
  | .proj n i _ => n.toString ++ ".projection" ++ toString i
  | _ => "other"

private def nativeHZeroStoredVectors006 (supplied : Syntax) : Term.TermElabM (Array Expr) := do
  let proposition ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let proposition ← instantiateMVars proposition
  let proposition ← whnf proposition
  let some (carrier, original, right) := proposition.consumeMData.headBeta.eq?
    | throwError "NativeHZero006 expected the actual inclusion-map equality."
  unless original.getAppFn.isConstOf ``actualOriginalPositiveTwoNativeJetHZeroSheafInclusion &&
      original.getAppArgs.size == 9 do
    throwError "NativeHZero006 refused a different original inclusion head/vector."
  let some stored ← delta? original
      (fun n => n == ``actualOriginalPositiveTwoNativeJetHZeroSheafInclusion)
    | throwError "NativeHZero006 missing the ONE stored inclusion VALUE."
  let stored := nativeHZeroHeadZeta006 32 stored
  let storedType ← instantiateMVars (← inferType stored)
  let rightType ← instantiateMVars (← inferType right)
  for e in #[carrier, original, right, stored, storedType, rightType] do
    if e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "NativeHZero006 refused unresolved/recovery stored vector."
  let leftArgs := stored.getAppArgs
  let rightArgs := right.getAppArgs
  logInfo m!"NativeHZero006 stored VALUE/RHS heads={nativeHZeroHeadLabel006 stored}/{nativeHZeroHeadLabel006 right}; arities={leftArgs.size}/{rightArgs.size}; own types raw-match={storedType.equal rightType}."
  if stored.getAppFn.equal right.getAppFn && leftArgs.size == rightArgs.size then
    for i in [:leftArgs.size] do
      logInfo m!"NativeHZero006 argument[{i}] raw-match={leftArgs[i]!.equal rightArgs[i]!}; heads={nativeHZeroHeadLabel006 leftArgs[i]!}/{nativeHZeroHeadLabel006 rightArgs[i]!}."
  return #[carrier, original, stored, right, storedType, rightType]

/-- Three bounded ordinary cuts, each built from the actual own stored vectors. -/
elab "native_hzero_map_split006% " index:num supplied:term : term => do
  let v ← nativeHZeroStoredVectors006 supplied
  match index.getNat with
  | 0 => mkEq v[1]! v[2]!
  | 1 => mkEq v[4]! v[5]!
  | 2 => mkHEq v[2]! v[3]!
  | _ => throwError "NativeHZero006 cut index out of range."

elab "native_hzero_map_definition006" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, original, stored) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.eq?
    | throwError "NativeHZero006 expected original/own-VALUE Eq."
  unless original.getAppFn.isConstOf ``actualOriginalPositiveTwoNativeJetHZeroSheafInclusion &&
      original.getAppArgs.size == 9 do
    throwError "NativeHZero006 refused another original map."
  let some expanded ← delta? original
      (fun n => n == ``actualOriginalPositiveTwoNativeJetHZeroSheafInclusion)
    | throwError "NativeHZero006 missing guarded declaration delta."
  unless stored.equal (nativeHZeroHeadZeta006 32 expanded) do
    throwError "NativeHZero006 refused another stored VALUE."
  goal.assign (← mkEqRefl original)
  replaceMainGoal []

elab "native_hzero_map_value006" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, stored, _, right) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.heq?
    | throwError "NativeHZero006 expected stored-VALUE/native-RHS HEq."
  unless stored.getAppFn.isConstOf ``actualAmbientClosedIdealTwistHZeroFactorInclusion &&
      right.getAppFn.isConstOf ``actualAmbientClosedIdealTwistHZeroFactorInclusion do
    throwError "NativeHZero006 expected the actual generic factor maps, not another map."
  goal.assign (← mkHEqRefl stored)
  replaceMainGoal []

/-- Ordinary equality transport from the separately checked actual endpoints. -/
elab "native_hzero_map_assemble006 " suppliedDefinition:term ", " suppliedValue:term : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let target ← if target.getAppFn.isConstOf ``nativeHZeroSheafInclusion_map_proposition006 then do
      let some expanded ← delta? target
          (fun n => n == ``nativeHZeroSheafInclusion_map_proposition006)
        | throwError "NativeHZero009 missing exact own proposition delta."
      pure (nativeHZeroHeadZeta006 32 expanded)
    else pure target
  let some (_, original, right) := target.consumeMData.headBeta.eq?
    | throwError "NativeHZero006 expected original map equality."
  let definition ← Term.elabTerm suppliedDefinition none (catchExPostpone := false)
  let value ← Term.elabTerm suppliedValue none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let definition ← instantiateMVars definition
  let value ← instantiateMVars value
  let some (_, definitionLeft, stored) :=
      (← instantiateMVars (← inferType definition)).consumeMData.headBeta.eq?
    | throwError "NativeHZero006 expected checked own definition equality."
  let some (_, valueLeft, _, valueRight) :=
      (← instantiateMVars (← inferType value)).consumeMData.headBeta.heq?
    | throwError "NativeHZero006 expected checked own stored-VALUE HEq."
  logInfo m!"NativeHZero009 assembly raw matches: goal/original={original.equal definitionLeft}; stored/valueLeft={stored.equal valueLeft}; goal/valueRight={right.equal valueRight}."
  for (label, left, rightEndpoint) in
      #[("original", original, definitionLeft), ("stored", stored, valueLeft), ("right", right, valueRight)] do
    let la := left.getAppArgs
    let ra := rightEndpoint.getAppArgs
    logInfo m!"NativeHZero009 {label} heads/arity={left.getAppFn}/{rightEndpoint.getAppFn}, {la.size}/{ra.size}."
    if left.getAppFn.equal rightEndpoint.getAppFn && la.size == ra.size then
      for i in [:la.size] do
        unless la[i]!.equal ra[i]! do
          logInfo m!"NativeHZero009 {label} different argument[{i}] heads={la[i]!.getAppFn}/{ra[i]!.getAppFn}."
  unless original.equal definitionLeft && stored.equal valueLeft && right.equal valueRight do
    throwError "NativeHZero006 refused different assembled endpoints."
  let proof ← mkEqOfHEq (← mkHEqTrans (← mkHEqOfEq definition) value)
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeHZero006 refused unresolved/recovery ordinary transport."
  goal.assign proof
  replaceMainGoal []


/-- Record ONLY actual head beta/zeta nodes of the untouched payload. -/
private def nativeHZeroPayloadTrace008 : Nat → Expr → Expr × Array (Name × String × String)
  | 0, e => (e, #[])
  | fuel + 1, e =>
      let e := e.consumeMData.headBeta
      match e with
      | .letE name type value body _ =>
          let (last, rest) := nativeHZeroPayloadTrace008 fuel (body.instantiate1 value)
          (last, #[(name, nativeHZeroHeadLabel006 type, nativeHZeroHeadLabel006 value)] ++ rest)
      | _ => (e, #[])

/-- Extract exactly the ACTUAL stored id2 wrapper and its untouched inner vector. -/
private def nativeHZeroStoredIdVectors007 (supplied : Syntax) : Term.TermElabM (Array Expr) := do
  let v ← nativeHZeroStoredVectors006 supplied
  let stored := v[2]!.consumeMData
  let args := stored.getAppArgs
  unless stored.getAppFn.isConstOf ``id && args.size == 2 do
    throwError "NativeHZero007 refused another stored wrapper: expected exactly id2."
  let idType := args[0]!
  let inner := args[1]!
  let innerType ← instantiateMVars (← inferType inner)
  let right := v[3]!
  logInfo m!"NativeHZero007 exact id2 inner/RHS heads={nativeHZeroHeadLabel006 inner}/{nativeHZeroHeadLabel006 right}; arities={inner.getAppArgs.size}/{right.getAppArgs.size}; idType/innerType raw-match={idType.equal innerType}."
  let isActualLet := match inner.consumeMData with | .letE .. => true | _ => false
  unless isActualLet &&
      right.getAppFn.isConstOf ``actualAmbientClosedIdealTwistHZeroFactorInclusion &&
      right.getAppArgs.size == 13 do
    throwError "NativeHZero008 refused another untouched payload: expected original let and RHS13."
  let (payload, steps) := nativeHZeroPayloadTrace008 32 inner
  logInfo m!"NativeHZero008 ACTUAL payload let-count={steps.size}; beta/zeta endpoint head={nativeHZeroHeadLabel006 payload}; arity={payload.getAppArgs.size}."
  for i in [:steps.size] do
    let step := steps[i]!
    logInfo m!"NativeHZero008 stored let[{i}] name={step.1}, type-head={step.2.1}, value-head={step.2.2}."
  for e in #[idType, inner, innerType] do
    if e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "NativeHZero007 refused unresolved/recovery exact id vector."
  return v ++ #[idType, inner, innerType]

/-- Exact endpoint of the SAME recorded payload, with the full map vector guarded. -/
private def nativeHZeroPayloadVectors008 (supplied : Syntax) : Term.TermElabM (Array Expr) := do
  let v ← nativeHZeroStoredIdVectors007 supplied
  let (payload, steps) := nativeHZeroPayloadTrace008 32 v[7]!
  unless !steps.isEmpty &&
      payload.getAppFn.isConstOf ``actualAmbientClosedIdealTwistHZeroFactorInclusion &&
      payload.getAppArgs.size == 13 do
    throwError "NativeHZero008 refused another payload endpoint or exhausted exact let telescope."
  if payload.hasMVar || payload.hasLevelMVar || payload.hasLooseBVars || payload.hasSorry then
    throwError "NativeHZero008 unresolved/recovery payload endpoint."
  let ia := payload.getAppArgs
  let ra := v[3]!.getAppArgs
  for i in [:ia.size] do
    logInfo m!"NativeHZero008 payload argument[{i}] raw-match={ia[i]!.equal ra[i]!}; heads={nativeHZeroHeadLabel006 ia[i]!}/{nativeHZeroHeadLabel006 ra[i]!}."
  return v ++ #[payload]

elab "native_hzero_id_split007% " index:num supplied:term : term => do
  match index.getNat with
  | 0 =>
      let v ← nativeHZeroStoredIdVectors007 supplied
      mkHEq v[2]! v[7]!
  | 1 =>
      let v ← nativeHZeroStoredIdVectors007 supplied
      mkHEq v[7]! v[3]!
  | 2 =>
      let v ← nativeHZeroPayloadVectors008 supplied
      mkHEq v[7]! v[9]!
  | 3 =>
      let v ← nativeHZeroPayloadVectors008 supplied
      mkHEq v[9]! v[3]!
  | _ => throwError "NativeHZero008 id/payload cut index out of range."

/-- Ordinary id computation with EXACT original type/value argument vector. -/
elab "native_hzero_id_wrapper007" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, stored, _, inner) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.heq?
    | throwError "NativeHZero007 expected actual id-wrapper HEq."
  let args := stored.getAppArgs
  unless stored.getAppFn.isConstOf ``id && args.size == 2 && args[1]!.equal inner do
    throwError "NativeHZero007 refused changed wrapper/type/value argument vector."
  let isActualLet := match inner.consumeMData with | .letE .. => true | _ => false
  unless isActualLet do
    throwError "NativeHZero008 refused another original id payload: expected diagnosed let."
  goal.assign (← mkHEqRefl stored)
  replaceMainGoal []

/-- Only exact head beta/zeta of the original stored payload is computed. -/
elab "native_hzero_payload_beta_zeta008" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, originalPayload, _, payload) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.heq?
    | throwError "NativeHZero008 expected exact payload beta/zeta HEq."
  let (actual, steps) := nativeHZeroPayloadTrace008 32 originalPayload
  unless !steps.isEmpty && actual.equal payload &&
      payload.getAppFn.isConstOf ``actualAmbientClosedIdealTwistHZeroFactorInclusion &&
      payload.getAppArgs.size == 13 do
    throwError "NativeHZero008 refused different actual payload/type/vector computation."
  goal.assign (← mkHEqRefl originalPayload)
  replaceMainGoal []

/-- Remaining native map comparison begins ONLY after the exact id wrapper. -/
elab "native_hzero_payload_native008" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, inner, _, right) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.heq?
    | throwError "NativeHZero007 expected exact inner-map/RHS HEq."
  unless inner.getAppFn.isConstOf ``actualAmbientClosedIdealTwistHZeroFactorInclusion &&
      inner.getAppArgs.size == 13 &&
      right.getAppFn.isConstOf ``actualAmbientClosedIdealTwistHZeroFactorInclusion &&
      right.getAppArgs.size == 13 do
    throwError "NativeHZero007 refused another generic-map head/full vector."
  goal.assign (← mkHEqRefl inner)
  replaceMainGoal []

elab "native_hzero_id_assemble007 " suppliedWrapper:term ", " suppliedInner:term : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, stored, _, right) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.heq?
    | throwError "NativeHZero007 expected stored-VALUE/RHS HEq."
  let wrapper ← Term.elabTerm suppliedWrapper none (catchExPostpone := false)
  let inner ← Term.elabTerm suppliedInner none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let wrapper ← instantiateMVars wrapper
  let inner ← instantiateMVars inner
  let some (_, wrapperLeft, _, wrapperRight) :=
      (← instantiateMVars (← inferType wrapper)).consumeMData.headBeta.heq?
    | throwError "NativeHZero007 expected checked wrapper HEq."
  let some (_, innerLeft, _, innerRight) :=
      (← instantiateMVars (← inferType inner)).consumeMData.headBeta.heq?
    | throwError "NativeHZero007 expected checked inner-map HEq."
  unless stored.equal wrapperLeft && wrapperRight.equal innerLeft && right.equal innerRight do
    throwError "NativeHZero007 refused changed exact intermediate vectors."
  let proof ← instantiateMVars (← mkHEqTrans wrapper inner)
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeHZero007 refused unresolved/recovery wrapper transport."
  goal.assign proof
  replaceMainGoal []

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeHZeroSheafInclusion_ownDefinitionEq006
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    native_hzero_map_split006% 0 (nativeHZeroSheafInclusion_map_proposition006 p hp P hP ell hell) := by
  native_hzero_map_definition006

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeHZeroSheafInclusion_exactIdWrapperHEq007
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    native_hzero_id_split007% 0 (nativeHZeroSheafInclusion_map_proposition006 p hp P hP ell hell) := by
  native_hzero_id_wrapper007

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeHZeroSheafInclusion_payloadBetaZetaHEq008
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    native_hzero_id_split007% 2 (nativeHZeroSheafInclusion_map_proposition006 p hp P hP ell hell) := by
  native_hzero_payload_beta_zeta008

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeHZeroSheafInclusion_payloadNativeHEq008
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    native_hzero_id_split007% 3 (nativeHZeroSheafInclusion_map_proposition006 p hp P hP ell hell) := by
  native_hzero_payload_native008

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeHZeroSheafInclusion_exactInnerHEq007
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    native_hzero_id_split007% 1 (nativeHZeroSheafInclusion_map_proposition006 p hp P hP ell hell) := by
  native_hzero_id_assemble007
    (nativeHZeroSheafInclusion_payloadBetaZetaHEq008 p hp P hP ell hell),
    (nativeHZeroSheafInclusion_payloadNativeHEq008 p hp P hP ell hell)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeHZeroSheafInclusion_ownCarrierEq006
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    native_hzero_map_split006% 1 (nativeHZeroSheafInclusion_map_proposition006 p hp P hP ell hell) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeHZeroSheafInclusion_ownValueHEq006
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    native_hzero_map_split006% 2 (nativeHZeroSheafInclusion_map_proposition006 p hp P hP ell hell) := by
  native_hzero_id_assemble007
    (nativeHZeroSheafInclusion_exactIdWrapperHEq007 p hp P hP ell hell),
    (nativeHZeroSheafInclusion_exactInnerHEq007 p hp P hP ell hell)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_factor_map005
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    actualOriginalPositiveTwoNativeJetHZeroSheafInclusion p hp P hP ell hell =
      actualAmbientClosedIdealTwistHZeroFactorInclusion
        (ambientToBase (R := K) (σ := Fin 4)) i r q hfac
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2) := by
  change nativeHZeroSheafInclusion_map_proposition006 p hp P hP ell hell
  native_hzero_map_assemble006
    (nativeHZeroSheafInclusion_ownDefinitionEq006 p hp P hP ell hell),
    (nativeHZeroSheafInclusion_ownValueHEq006 p hp P hP ell hell)


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_factor_apply005
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      actualOriginalPositiveTwoNativeJetHZeroSheafInclusion p hp P hP ell hell s =
      actualAmbientClosedIdealTwistHZeroFactorInclusion
        (ambientToBase (R := K) (σ := Fin 4)) i r q hfac
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2) s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  intro s
  exact congrArg (fun f :
    SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)) →ₗ[K]
      ActualOriginalPointIdealQuadraticSections p hp P => f s)
    (nativeHZeroSheafInclusion_factor_map005 p hp P hP ell hell)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_dictionaryCongruence010
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      (p3ActualIdealQuadraticIntrinsicLinearEquiv q
        (actualOriginalPositiveTwoNativeJetHZeroSheafInclusion p hp P hP ell hell s)).val =
      (p3ActualIdealQuadraticIntrinsicLinearEquiv q
        (actualAmbientClosedIdealTwistHZeroFactorInclusion
          (ambientToBase (R := K) (σ := Fin 4)) i r q hfac
          (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2) s)).val := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  exact congrArg (fun v : ActualOriginalPointIdealQuadraticSections p hp P =>
    (p3ActualIdealQuadraticIntrinsicLinearEquiv
      ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)) v).val)
    (nativeHZeroSheafInclusion_factor_apply005 p hp P hP ell hell s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private abbrev nativeHZeroSheafInclusion_naturality_proposition011
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) : Prop :=
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      (p3ActualIdealQuadraticIntrinsicLinearEquiv q
        (actualAmbientClosedIdealTwistHZeroFactorInclusion
          (ambientToBase (R := K) (σ := Fin 4)) i r q hfac
          (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2) s)).val =
      (p3ActualIdealQuadraticIntrinsicLinearEquiv i s).val

meta section
open Lean Meta Elab Tactic

/-- Instantiate the EXISTING law from the exact original factor-map13/evaluation6 vectors. -/
private def nativeHZeroNaturalityVectors011 (supplied : Syntax) (suppliedSection : Syntax) :
    Term.TermElabM (Array Expr) := do
  let proposition ← Term.elabTerm supplied none (catchExPostpone := false)
  let sectionValue ← Term.elabTerm suppliedSection none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let proposition ← instantiateMVars proposition
  let sectionValue ← instantiateMVars sectionValue
  unless proposition.getAppFn.isConstOf ``nativeHZeroSheafInclusion_naturality_proposition011 &&
      proposition.getAppArgs.size == 9 do
    throwError "NativeHZero011 refused another original native naturality proposition9."
  let some expanded ← delta? proposition
      (fun n => n == ``nativeHZeroSheafInclusion_naturality_proposition011)
    | throwError "NativeHZero011 missing guarded original proposition delta."
  let expanded := nativeHZeroHeadZeta006 32 expanded
  let .forallE _ _ conclusion _ := expanded
    | throwError "NativeHZero011 expected original sectionValue binder."
  let target := conclusion.instantiate1 sectionValue
  let some (_, left, _) := target.consumeMData.headBeta.eq?
    | throwError "NativeHZero011 expected original native polynomial equality."
  let some factor := left.find? (fun e =>
      e.getAppFn.isConstOf ``actualAmbientClosedIdealTwistHZeroFactorInclusion &&
        e.getAppArgs.size == 13)
    | throwError "NativeHZero011 missing EXACT original factor-map13 in left endpoint."
  let some evaluation := left.find? (fun e =>
      e.getAppFn.isConstOf ``DFunLike.coe && e.getAppArgs.size == 6 &&
        e.getAppArgs[4]!.consumeMData.equal factor.consumeMData)
    | throwError "NativeHZero011 missing exact factor-map evaluation6."
  unless evaluation.getAppArgs[5]!.consumeMData.equal sectionValue.consumeMData do
    throwError "NativeHZero011 refused a different original source sectionValue."
  let fa := factor.getAppArgs
  unless fa[5]!.getAppFn.isConstOf ``AllCharacteristics.HomogeneousProjective.ambientToBase &&
      fa[12]!.getAppFn.isConstOf ``ProjectiveNegativeTwist.positiveSheafOfModules do
    throwError "NativeHZero011 refused another original ambient base/twist."
  let .const _ levels := factor.getAppFn
    | throwError "NativeHZero011 expected stored factor universes."
  let factorInfo ← getConstInfo ``actualAmbientClosedIdealTwistHZeroFactorInclusion
  let lawInfo ← getConstInfo ``p3ActualIdealQuadraticIntrinsicLinearEquiv_factor_naturality
  unless factorInfo.levelParams == lawInfo.levelParams do
    throwError "NativeHZero011 refused different declared law/factor universe vectors."
  let law := mkAppN
    (mkConst ``p3ActualIdealQuadraticIntrinsicLinearEquiv_factor_naturality levels)
    #[fa[0]!, fa[1]!, fa[3]!, fa[4]!, fa[6]!, fa[7]!, fa[8]!, fa[9]!,
      fa[10]!, fa[11]!, sectionValue]
  let lawType ← instantiateMVars (← inferType law)
  for e in #[target, factor, evaluation, sectionValue, law, lawType] do
    if e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "NativeHZero011 refused unresolved/recovery actual law vector."
  logInfo m!"NativeHZero011 actual generic law11 own type/native proposition raw-match={lawType.equal target}."
  if let some (lc, ll, lr) := lawType.consumeMData.headBeta.eq? then
    let some (tc, tl, tr) := target.consumeMData.headBeta.eq?
      | throwError "NativeHZero011 lost original target Eq."
    logInfo m!"NativeHZero011 own/native carrier,left,right raw matches={lc.equal tc}/{ll.equal tl}/{lr.equal tr}."
    for (label, l, r) in #[("carrier", lc, tc), ("left", ll, tl), ("right", lr, tr)] do
      logInfo m!"NativeHZero011 {label} heads/arities={nativeHZeroHeadLabel006 l}/{nativeHZeroHeadLabel006 r},{l.getAppArgs.size}/{r.getAppArgs.size}."
      if l.getAppFn.equal r.getAppFn && l.getAppArgs.size == r.getAppArgs.size then
        let la := l.getAppArgs
        let ra := r.getAppArgs
        for i in [:la.size] do
          unless la[i]!.equal ra[i]! do
            logInfo m!"NativeHZero011 {label} differing argument[{i}] heads={nativeHZeroHeadLabel006 la[i]!}/{nativeHZeroHeadLabel006 ra[i]!}."
  return #[target, law, lawType]

elab "native_hzero_naturality_own011% " supplied:term " at " sectionValue:term : term => do
  let v ← nativeHZeroNaturalityVectors011 supplied sectionValue
  return v[1]!

elab "native_hzero_naturality_type011% " supplied:term " at " sectionValue:term : term => do
  let v ← nativeHZeroNaturalityVectors011 supplied sectionValue
  mkEq v[2]! v[0]!

/-- Ordinary bounded proposition conversion; the kernel must check it. -/
elab "native_hzero_naturality_type_refl011" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, sourceType, _) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.eq?
    | throwError "NativeHZero011 expected own-law/native proposition Eq."
  goal.assign (← mkEqRefl sourceType)
  replaceMainGoal []

/-- Apply ONLY the separately checked proposition conversion to the exact own law. -/
elab "native_hzero_naturality_transport011 " suppliedLaw:term ", " suppliedType:term : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let law ← Term.elabTerm suppliedLaw none (catchExPostpone := false)
  let typeEq ← Term.elabTerm suppliedType none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let law ← instantiateMVars law
  let typeEq ← instantiateMVars typeEq
  let lawType ← instantiateMVars (← inferType law)
  let some (_, typeLeft, typeRight) :=
      (← instantiateMVars (← inferType typeEq)).consumeMData.headBeta.eq?
    | throwError "NativeHZero011 expected checked proposition Eq."
  logInfo m!"NativeHZero011 transport own/target raw matches={lawType.equal typeLeft}/{target.equal typeRight}."
  unless lawType.equal typeLeft && target.equal typeRight do
    throwError "NativeHZero011 refused changed actual proposition endpoints."
  let proof := mkAppN (mkConst ``Eq.mp [Level.zero]) #[lawType, target, typeEq, law]
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeHZero011 refused unresolved/recovery ordinary transport."
  goal.assign proof
  replaceMainGoal []


/-- The ACTUAL diagnosed Subtype.val3 / DFunLike.coe6 endpoint boundaries. -/
private def nativeHZeroNaturalityEndpoints012 (supplied : Syntax) (suppliedSection : Syntax) :
    Term.TermElabM (Array Expr) := do
  let v ← nativeHZeroNaturalityVectors011 supplied suppliedSection
  let some (carrier, ll, lr) := v[2]!.consumeMData.headBeta.eq?
    | throwError "NativeHZero012 expected exact own-law Eq."
  let some (nativeCarrier, tl, tr) := v[0]!.consumeMData.headBeta.eq?
    | throwError "NativeHZero012 expected exact native Eq."
  unless carrier.equal nativeCarrier do
    throwError "NativeHZero012 refused changed polynomial carrier."
  for endpoint in #[ll, lr, tl, tr] do
    unless endpoint.getAppFn.isConstOf ``Subtype.val && endpoint.getAppArgs.size == 3 do
      throwError "NativeHZero012 refused another endpoint: expected Subtype.val3."
  let la := ll.getAppArgs
  let ta := tl.getAppArgs
  let ra := lr.getAppArgs
  let na := tr.getAppArgs
  unless la[0]!.equal ta[0]! && ra[0]!.equal na[0]! && ra[1]!.equal na[1]! do
    throwError "NativeHZero012 refused changed actual endpoint carrier or diagnosed SAME right predicate."
  for (label, l, r) in #[("leftValue", la[2]!, ta[2]!), ("rightValue", ra[2]!, na[2]!)] do
    unless l.getAppFn.isConstOf ``DFunLike.coe && l.getAppArgs.size == 6 &&
        r.getAppFn.isConstOf ``DFunLike.coe && r.getAppArgs.size == 6 do
      throwError "NativeHZero012 refused another stored dictionary value: expected evaluation6."
    let aa := l.getAppArgs
    let bb := r.getAppArgs
    for i in [:6] do
      logInfo m!"NativeHZero012 {label} evaluation argument[{i}] raw-match={aa[i]!.equal bb[i]!}; heads={nativeHZeroHeadLabel006 aa[i]!}/{nativeHZeroHeadLabel006 bb[i]!}."
    let f := aa[4]!
    let g := bb[4]!
    logInfo m!"NativeHZero012 {label} dictionary factory heads/arity={nativeHZeroHeadLabel006 f}/{nativeHZeroHeadLabel006 g},{f.getAppArgs.size}/{g.getAppArgs.size}."
    if f.getAppFn.equal g.getAppFn && f.getAppArgs.size == g.getAppArgs.size then
      let fa := f.getAppArgs
      let ga := g.getAppArgs
      for i in [:fa.size] do
        unless fa[i]!.equal ga[i]! do
          logInfo m!"NativeHZero012 {label} dictionary argument[{i}] differs: {nativeHZeroHeadLabel006 fa[i]!}/{nativeHZeroHeadLabel006 ga[i]!}."
  return #[v[0]!, v[2]!, carrier, ll, lr, tl, tr, la[1]!, ta[1]!, la[2]!, ta[2]!, ra[2]!, na[2]!]

elab "native_hzero_naturality_endpoint012% " index:num supplied:term " at " sectionValue:term : term => do
  let v ← nativeHZeroNaturalityEndpoints012 supplied sectionValue
  match index.getNat with
  | 0 => mkEq v[7]! v[8]!
  | 1 => mkHEq v[9]! v[10]!
  | 2 => mkHEq v[11]! v[12]!
  | 3 => mkEq v[3]! v[5]!
  | 4 => mkEq v[4]! v[6]!
  | _ => throwError "NativeHZero012 endpoint cut index out of range."

/-- Each cut is an ordinary bounded reflexivity check, not a trusted conversion. -/
elab "native_hzero_naturality_endpoint_refl012" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
  let proof ← match target.eq?, target.heq? with
    | some (_, left, _), _ => mkEqRefl left
    | _, some (_, left, _, _) => mkHEqRefl left
    | _, _ => throwError "NativeHZero012 expected the exact predicate Eq or dictionary-value HEq."
  goal.assign proof
  replaceMainGoal []

private def nativeHZeroSubtypeEndpointCongr012 (target predicate value : Expr) : MetaM Expr := do
  let some (_, left, right) := target.consumeMData.headBeta.eq?
    | throwError "NativeHZero012 expected original polynomial endpoint Eq."
  unless left.getAppFn.isConstOf ``Subtype.val && right.getAppFn.equal left.getAppFn &&
      left.getAppArgs.size == 3 && right.getAppArgs.size == 3 do
    throwError "NativeHZero012 refused changed endpoint projection heads/vectors."
  let la := left.getAppArgs
  let ra := right.getAppArgs
  let some (_, pl, pr) := (← instantiateMVars (← inferType predicate)).consumeMData.headBeta.eq?
    | throwError "NativeHZero012 expected checked predicate Eq."
  let some (_, vl, _, vr) := (← instantiateMVars (← inferType value)).consumeMData.headBeta.heq?
    | throwError "NativeHZero012 expected checked dictionary-value HEq."
  unless la[0]!.equal ra[0]! && la[1]!.equal pl && ra[1]!.equal pr &&
      la[2]!.equal vl && ra[2]!.equal vr do
    throwError "NativeHZero012 refused different actual subtype projection arguments."
  let thm ← mkHCongrWithArity left.getAppFn 3
  let hs := #[(← mkHEqRefl la[0]!), (← mkHEqOfEq predicate), value]
  let mut arguments := #[]
  for i in [:3] do
    let h ← match thm.argKinds[i]! with
      | .eq => mkEqOfHEq hs[i]!
      | .heq => pure hs[i]!
      | _ => throwError "NativeHZero012 unexpected Subtype.val3 congruence kind."
    arguments := arguments ++ #[la[i]!, ra[i]!, h]
  mkEqOfHEq (mkAppN thm.proof arguments)

elab "native_hzero_naturality_left_projection012 " suppliedPredicate:term ", " suppliedValue:term : tactic => withMainContext do
  let goal ← getMainGoal
  let predicate ← Term.elabTerm suppliedPredicate none (catchExPostpone := false)
  let value ← Term.elabTerm suppliedValue none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let predicate ← instantiateMVars predicate
  let value ← instantiateMVars value
  let proof ← nativeHZeroSubtypeEndpointCongr012 (← instantiateMVars (← goal.getType)) predicate value
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeHZero012 unresolved/recovery ordinary left projection congruence."
  goal.assign proof
  replaceMainGoal []

elab "native_hzero_naturality_right_projection012 " suppliedValue:term : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some (_, left, right) := target.consumeMData.headBeta.eq?
    | throwError "NativeHZero012 expected right polynomial endpoint Eq."
  unless left.getAppFn.isConstOf ``Subtype.val && right.getAppFn.equal left.getAppFn &&
      left.getAppArgs.size == 3 && right.getAppArgs.size == 3 &&
      left.getAppArgs[1]!.equal right.getAppArgs[1]! do
    throwError "NativeHZero012 refused changed SAME right predicate vector."
  let predicate ← mkEqRefl left.getAppArgs[1]!
  let value ← Term.elabTerm suppliedValue none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  let proof ← instantiateMVars (← nativeHZeroSubtypeEndpointCongr012 target predicate value)
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeHZero012 unresolved/recovery ordinary right projection congruence."
  goal.assign proof
  replaceMainGoal []

/-- Ordinary Eq3 congruence, using ONLY separately checked whole endpoint equations. -/
elab "native_hzero_naturality_proposition012 " suppliedLeft:term ", " suppliedRight:term : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, ownType, nativeType) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.eq?
    | throwError "NativeHZero012 expected own/native proposition equality."
  let some (carrier, ll, lr) := ownType.consumeMData.headBeta.eq?
    | throwError "NativeHZero012 expected original own-law Eq3."
  let some (nativeCarrier, tl, tr) := nativeType.consumeMData.headBeta.eq?
    | throwError "NativeHZero012 expected original native Eq3."
  let left ← Term.elabTerm suppliedLeft none (catchExPostpone := false)
  let right ← Term.elabTerm suppliedRight none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let left ← instantiateMVars left
  let right ← instantiateMVars right
  let some (_, cl, ct) := (← instantiateMVars (← inferType left)).consumeMData.headBeta.eq?
    | throwError "NativeHZero012 expected checked whole-left Eq."
  let some (_, cr, cu) := (← instantiateMVars (← inferType right)).consumeMData.headBeta.eq?
    | throwError "NativeHZero012 expected checked whole-right Eq."
  unless carrier.equal nativeCarrier && ll.equal cl && tl.equal ct && lr.equal cr && tr.equal cu do
    throwError "NativeHZero012 refused changed Eq3 own/checked/native vectors."
  let thm ← mkHCongrWithArity ownType.getAppFn 3
  let la := #[carrier, ll, lr]
  let ra := #[nativeCarrier, tl, tr]
  let hs := #[(← mkHEqRefl carrier), (← mkHEqOfEq left), (← mkHEqOfEq right)]
  let mut arguments := #[]
  for i in [:3] do
    let h ← match thm.argKinds[i]! with
      | .eq => mkEqOfHEq hs[i]!
      | .heq => pure hs[i]!
      | _ => throwError "NativeHZero012 unexpected Eq3 congruence kind."
    arguments := arguments ++ #[la[i]!, ra[i]!, h]
  let proof ← instantiateMVars (← mkEqOfHEq (mkAppN thm.proof arguments))
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeHZero012 unresolved/recovery ordinary proposition congruence."
  goal.assign proof
  replaceMainGoal []


/-- Exact dictionary5 specimens; only actually diagnosed Spec/proof differences are allowed. -/
private def nativeHZeroDictionaryVectors013 (supplied : Syntax) (suppliedSection : Syntax) :
    Term.TermElabM (Array Expr) := do
  let v ← nativeHZeroNaturalityEndpoints012 supplied suppliedSection
  let f := v[9]!.getAppArgs[4]!
  let g := v[10]!.getAppArgs[4]!
  let rf := v[11]!.getAppArgs[4]!
  let rg := v[12]!.getAppArgs[4]!
  for x in #[f, g, rf, rg] do
    unless x.getAppFn.isConstOf ``p3ActualIdealQuadraticIntrinsicLinearEquiv &&
        x.getAppArgs.size == 5 do
      throwError "NativeHZero013 refused a changed original dictionary5."
  let fa := f.getAppArgs
  let ga := g.getAppArgs
  let rfa := rf.getAppArgs
  let rga := rg.getAppArgs
  unless fa[0]!.equal ga[0]! && fa[1]!.equal ga[1]! && fa[3]!.equal ga[3]! do
    throwError "NativeHZero013 refused another original K/field/point map."
  for i in [:4] do
    unless rfa[i]!.equal rga[i]! do
      throwError "NativeHZero013 refused a changed right dictionary data argument."
  for x in #[fa[2]!, ga[2]!] do
    unless x.getAppFn.isConstOf ``AlgebraicGeometry.Spec && x.getAppArgs.size == 1 do
      throwError "NativeHZero013 refused another actual native Spec1 specimen."
  let ringLeft := fa[2]!.getAppArgs[0]!
  let ringRight := ga[2]!.getAppArgs[0]!
  logInfo m!"NativeHZero013 EXACT Spec rings heads/arity={nativeHZeroHeadLabel006 ringLeft}/{nativeHZeroHeadLabel006 ringRight},{ringLeft.getAppArgs.size}/{ringRight.getAppArgs.size}."
  for (label, ring) in #[("ownRing", ringLeft), ("nativeRing", ringRight)] do
    let args := ring.getAppArgs
    for i in [:args.size] do
      logInfo m!"NativeHZero013 {label} argument[{i}] head/arity={nativeHZeroHeadLabel006 args[i]!},{args[i]!.getAppArgs.size}."
  return v ++ #[f, g, rf, rg, ringLeft, ringRight]

elab "native_hzero_dictionary_cut013% " index:num supplied:term " at " sectionValue:term : term => do
  let v ← nativeHZeroDictionaryVectors013 supplied sectionValue
  let la := v[9]!.getAppArgs
  let ra := v[10]!.getAppArgs
  match index.getNat with
  | 0 => mkEq v[17]! v[18]!
  | 1 => mkEq v[13]!.getAppArgs[2]! v[14]!.getAppArgs[2]!
  | 2 => mkHEq v[13]!.getAppArgs[4]! v[14]!.getAppArgs[4]!
  | 3 => mkHEq v[13]! v[14]!
  | 4 => mkEq la[0]! ra[0]!
  | 5 => mkEq la[1]! ra[1]!
  | 6 => mkHEq la[2]! ra[2]!
  | 7 => mkHEq la[3]! ra[3]!
  | 8 => mkHEq la[5]! ra[5]!
  | _ => throwError "NativeHZero013 dictionary/coercion cut index out of range."

elab "native_hzero_spec_congr013 " suppliedRing:term : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, left, right) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.eq?
    | throwError "NativeHZero013 expected exact Spec equality."
  unless left.getAppFn.isConstOf ``AlgebraicGeometry.Spec && right.getAppFn.equal left.getAppFn &&
      left.getAppArgs.size == 1 && right.getAppArgs.size == 1 do
    throwError "NativeHZero013 refused changed original Spec1 vectors."
  let ring ← Term.elabTerm suppliedRing none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let ring ← instantiateMVars ring
  let some (_, rl, rr) := (← instantiateMVars (← inferType ring)).consumeMData.headBeta.eq?
    | throwError "NativeHZero013 expected checked original ring equality."
  unless rl.equal left.getAppArgs[0]! && rr.equal right.getAppArgs[0]! do
    throwError "NativeHZero013 refused replacement original ring specimens."
  let proof ← instantiateMVars (← mkCongrArg left.getAppFn ring)
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeHZero013 unresolved/recovery Spec congruence."
  goal.assign proof
  replaceMainGoal []

elab "native_hzero_closed_proof013" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, left, _, right) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.heq?
    | throwError "NativeHZero013 expected original closed-immersion proof HEq."
  let lt ← instantiateMVars (← inferType left)
  let rt ← instantiateMVars (← inferType right)
  unless (← isProp lt) && (← isProp rt) do
    throwError "NativeHZero013 refused to identify non-proof data/actions."
  let proof := mkAppN (mkConst ``proof_irrel_heq) #[lt, rt, left, right]
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeHZero013 unresolved/recovery original proof-irrelevance term."
  goal.assign proof
  replaceMainGoal []

/-- Ordinary heterogeneous congruence for the SAME guarded application vector. -/
private def nativeHZeroApplicationCongr013 (left right : Expr) (hs : Array Expr) : MetaM Expr := do
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless left.getAppFn.equal right.getAppFn && la.size == ra.size && hs.size == la.size do
    throwError "NativeHZero013 refused changed congruence head/full vector."
  let thm ← mkHCongrWithArity left.getAppFn la.size
  let mut args := #[]
  for i in [:la.size] do
    let some (_, hl, _, hr) := (← instantiateMVars (← inferType hs[i]!)).consumeMData.headBeta.heq?
      | throwError "NativeHZero013 expected exact checked congruence HEq argument."
    unless hl.equal la[i]! && hr.equal ra[i]! do
      throwError "NativeHZero013 refused changed congruence argument[{i}]."
    let h ← match thm.argKinds[i]! with
      | .eq => mkEqOfHEq hs[i]!
      | .heq => pure hs[i]!
      | _ => throwError "NativeHZero013 unexpected actual congruence argument kind."
    args := args ++ #[la[i]!, ra[i]!, h]
  return mkAppN thm.proof args

elab "native_hzero_dictionary_congr013 " suppliedSpec:term ", " suppliedProof:term : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, left, _, right) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.heq?
    | throwError "NativeHZero013 expected actual dictionary HEq."
  unless left.getAppFn.isConstOf ``p3ActualIdealQuadraticIntrinsicLinearEquiv &&
      right.getAppFn.equal left.getAppFn && left.getAppArgs.size == 5 && right.getAppArgs.size == 5 do
    throwError "NativeHZero013 refused changed dictionary5 head/vector."
  let spec ← Term.elabTerm suppliedSpec none (catchExPostpone := false)
  let closed ← Term.elabTerm suppliedProof none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let spec ← instantiateMVars spec
  let closed ← instantiateMVars closed
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless la[0]!.equal ra[0]! && la[1]!.equal ra[1]! && la[3]!.equal ra[3]! do
    throwError "NativeHZero013 refused changed original field/map data."
  let hs := #[(← mkHEqRefl la[0]!), (← mkHEqRefl la[1]!), (← mkHEqOfEq spec),
    (← mkHEqRefl la[3]!), closed]
  let proof ← instantiateMVars (← nativeHZeroApplicationCongr013 left right hs)
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeHZero013 unresolved/recovery dictionary congruence."
  goal.assign proof
  replaceMainGoal []

elab "native_hzero_left_evaluation013 " p0:term ", " p1:term ", " p2:term ", " p3:term ", " p4:term ", " p5:term : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, left, _, right) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.heq?
    | throwError "NativeHZero013 expected actual evaluation HEq."
  unless left.getAppFn.isConstOf ``DFunLike.coe && right.getAppFn.equal left.getAppFn &&
      left.getAppArgs.size == 6 && right.getAppArgs.size == 6 do
    throwError "NativeHZero013 refused changed exact evaluation6."
  let mut hs := #[]
  for (i, stx) in #[(0, p0), (1, p1), (2, p2), (3, p3), (4, p4), (5, p5)] do
    let h ← Term.elabTerm stx none (catchExPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    let h ← instantiateMVars h
    let h ← if i < 2 then mkHEqOfEq h else pure h
    hs := hs.push h
  let proof ← instantiateMVars (← nativeHZeroApplicationCongr013 left right hs)
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeHZero013 unresolved/recovery original evaluation congruence."
  goal.assign proof
  replaceMainGoal []


/-- Exact ORIGINAL inner factor evaluation6 and its full factor-map13 vector. -/
private def nativeHZeroFactorEvaluationVectors014 (supplied : Syntax) (suppliedSection : Syntax) :
    Term.TermElabM (Array Expr) := do
  let v ← nativeHZeroDictionaryVectors013 supplied suppliedSection
  let left := v[9]!.getAppArgs[5]!
  let right := v[10]!.getAppArgs[5]!
  for x in #[left, right] do
    unless x.getAppFn.isConstOf ``DFunLike.coe && x.getAppArgs.size == 6 do
      throwError "NativeHZero014 refused another ORIGINAL inner evaluation6."
  let la := left.getAppArgs
  let ra := right.getAppArgs
  let f := la[4]!
  let g := ra[4]!
  for x in #[f, g] do
    unless x.getAppFn.isConstOf ``actualAmbientClosedIdealTwistHZeroFactorInclusion &&
        x.getAppArgs.size == 13 do
      throwError "NativeHZero014 refused another ORIGINAL factor-map13."
  unless f.getAppFn.equal g.getAppFn do
    throwError "NativeHZero014 refused different ORIGINAL factor universes."
  let fa := f.getAppArgs
  let ga := g.getAppArgs
  for a in #[fa, ga] do
    unless a[5]!.getAppFn.isConstOf ``AllCharacteristics.HomogeneousProjective.ambientToBase &&
        a[12]!.getAppFn.isConstOf ``ProjectiveNegativeTwist.positiveSheafOfModules do
      throwError "NativeHZero014 refused another actual ambient base/twist."
  let sectionTerm ← Term.elabTerm suppliedSection none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let sectionTerm ← instantiateMVars sectionTerm
  unless la[5]!.consumeMData.equal sectionTerm.consumeMData &&
      ra[5]!.consumeMData.equal sectionTerm.consumeMData do
    throwError "NativeHZero014 refused a changed original supplied source section."
  for i in [:6] do
    logInfo m!"NativeHZero014 inner evaluation argument[{i}] raw-match={la[i]!.equal ra[i]!}; heads/arities={nativeHZeroHeadLabel006 la[i]!}/{nativeHZeroHeadLabel006 ra[i]!},{la[i]!.getAppArgs.size}/{ra[i]!.getAppArgs.size}."
  for i in [:13] do
    logInfo m!"NativeHZero014 EXACT factor13 argument[{i}] raw-match={fa[i]!.equal ga[i]!}; heads/arities={nativeHZeroHeadLabel006 fa[i]!}/{nativeHZeroHeadLabel006 ga[i]!},{fa[i]!.getAppArgs.size}/{ga[i]!.getAppArgs.size}."
  return #[left, right]

elab "native_hzero_factor_cut014% " index:num supplied:term " at " sectionValue:term : term => do
  let v ← nativeHZeroFactorEvaluationVectors014 supplied sectionValue
  let la := v[0]!.getAppArgs
  let ra := v[1]!.getAppArgs
  let i := index.getNat
  unless i < 6 do
    throwError "NativeHZero014 inner evaluation cut index out of range."
  if i < 2 then mkEq la[i]! ra[i]! else mkHEq la[i]! ra[i]!

elab "native_hzero_factor_diagnostic014 " supplied:term " at " sectionValue:term : tactic => withMainContext do
  let _ ← nativeHZeroFactorEvaluationVectors014 supplied sectionValue
  let goal ← getMainGoal
  goal.assign (mkConst ``True.intro)
  replaceMainGoal []

/-- Reflexivity ONLY for the raw-identical original full factor-map13 vector. -/
elab "native_hzero_factor_map_refl014" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, left, _, right) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.heq?
    | throwError "NativeHZero014 expected exact original factor-map HEq."
  unless left.getAppFn.isConstOf ``actualAmbientClosedIdealTwistHZeroFactorInclusion &&
      right.getAppFn.equal left.getAppFn && left.getAppArgs.size == 13 && right.getAppArgs.size == 13 do
    throwError "NativeHZero014 refused changed ORIGINAL factor-map13 head/vector."
  let la := left.getAppArgs
  let ra := right.getAppArgs
  for i in [:13] do
    unless la[i]!.equal ra[i]! do
      throwError "NativeHZero014 original factor13 argument[{i}] differs; use the actual vector diagnostic for a separate ordinary cut."
  goal.assign (← mkHEqRefl left)
  replaceMainGoal []

elab "native_hzero_factor_input_refl014" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, left, _, right) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.heq?
    | throwError "NativeHZero014 expected original source-section HEq."
  unless left.equal right do
    throwError "NativeHZero014 refused a changed raw original source section."
  goal.assign (← mkHEqRefl left)
  replaceMainGoal []

/-- Reuse ordinary evaluation6 congruence with the EXACT inner factor-vector cuts. -/
elab "native_hzero_factor_evaluation014 " p0:term ", " p1:term ", " p2:term ", " p3:term ", " p4:term ", " p5:term : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, left, _, right) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.heq?
    | throwError "NativeHZero014 expected actual inner factor-evaluation HEq."
  unless left.getAppFn.isConstOf ``DFunLike.coe && right.getAppFn.equal left.getAppFn &&
      left.getAppArgs.size == 6 && right.getAppArgs.size == 6 do
    throwError "NativeHZero014 refused changed exact inner evaluation6."
  let mut hs := #[]
  for (i, stx) in #[(0, p0), (1, p1), (2, p2), (3, p3), (4, p4), (5, p5)] do
    let h ← Term.elabTerm stx none (catchExPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    let h ← instantiateMVars h
    let h ← if i < 2 then mkHEqOfEq h else pure h
    hs := hs.push h
  let proof ← instantiateMVars (← nativeHZeroApplicationCongr013 left right hs)
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeHZero014 unresolved/recovery original inner evaluation congruence."
  goal.assign proof
  replaceMainGoal []



/-- The EXACT diagnosed ambient-Proj7 / positive-twist8 differences of the original map13. -/
private def nativeHZeroFactorObjectVectors015 (supplied : Syntax) (suppliedSection : Syntax) :
    Term.TermElabM (Array Expr) := do
  let v ← nativeHZeroFactorEvaluationVectors014 supplied suppliedSection
  let f := v[0]!.getAppArgs[4]!
  let g := v[1]!.getAppArgs[4]!
  let fa := f.getAppArgs
  let ga := g.getAppArgs
  for i in [:13] do
    if i != 2 && i != 12 then
      unless fa[i]!.equal ga[i]! do
        throwError "NativeHZero015 refused a change in original raw-identical map13 argument[{i}]."
  for x in #[fa[2]!, ga[2]!] do
    unless x.getAppFn.isConstOf ``AlgebraicGeometry.Proj && x.getAppArgs.size == 7 do
      throwError "NativeHZero015 refused another ORIGINAL ambient Proj7."
  for x in #[fa[12]!, ga[12]!] do
    unless x.getAppFn.isConstOf ``ProjectiveNegativeTwist.positiveSheafOfModules &&
        x.getAppArgs.size == 8 do
      throwError "NativeHZero015 refused another ORIGINAL positive twist8."
  for (label, left, right) in #[
      ("ambientProj", fa[2]!, ga[2]!), ("positiveTwist", fa[12]!, ga[12]!)] do
    unless left.getAppFn.equal right.getAppFn do
      throwError "NativeHZero015 refused different original {label} constant universes."
    let la := left.getAppArgs
    let ra := right.getAppArgs
    for i in [:la.size] do
      logInfo m!"NativeHZero015 {label} EXACT argument[{i}] raw-match={la[i]!.equal ra[i]!}; heads/arities={nativeHZeroHeadLabel006 la[i]!}/{nativeHZeroHeadLabel006 ra[i]!},{la[i]!.getAppArgs.size}/{ra[i]!.getAppArgs.size}."
      let aa := la[i]!.getAppArgs
      let bb := ra[i]!.getAppArgs
      if la[i]!.getAppFn.equal ra[i]!.getAppFn && aa.size == bb.size then
        for j in [:aa.size] do
          logInfo m!"NativeHZero015 {label} EXACT argument[{i}][{j}] raw-match={aa[j]!.equal bb[j]!}; heads/arities={nativeHZeroHeadLabel006 aa[j]!}/{nativeHZeroHeadLabel006 bb[j]!},{aa[j]!.getAppArgs.size}/{bb[j]!.getAppArgs.size}."
  return #[f, g, fa[2]!, ga[2]!, fa[12]!, ga[12]!]

elab "native_hzero_factor_object015% " index:num supplied:term " at " sectionValue:term : term => do
  let v ← nativeHZeroFactorObjectVectors015 supplied sectionValue
  match index.getNat with
  | 0 => mkEq v[2]! v[3]!
  | 1 => mkHEq v[4]! v[5]!
  | _ => throwError "NativeHZero015 original factor-object cut index out of range."

/-- Ordinary full map13 congruence; retain all eleven actual raw-identical arguments. -/
elab "native_hzero_factor_factory015 " suppliedAmbient:term ", " suppliedTwist:term : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, left, _, right) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.heq?
    | throwError "NativeHZero015 expected exact original factor-map13 HEq."
  unless left.getAppFn.isConstOf ``actualAmbientClosedIdealTwistHZeroFactorInclusion &&
      right.getAppFn.equal left.getAppFn && left.getAppArgs.size == 13 && right.getAppArgs.size == 13 do
    throwError "NativeHZero015 refused changed ORIGINAL map13 head/full vector."
  let la := left.getAppArgs
  let ra := right.getAppArgs
  for i in [:13] do
    if i != 2 && i != 12 then
      unless la[i]!.equal ra[i]! do
        throwError "NativeHZero015 refused changed ORIGINAL raw-identical map13 argument[{i}]."
  let ambient ← Term.elabTerm suppliedAmbient none (catchExPostpone := false)
  let twist ← Term.elabTerm suppliedTwist none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let ambient ← instantiateMVars ambient
  let twist ← instantiateMVars twist
  let mut hs := #[]
  for i in [:13] do
    let h ← if i == 2 then mkHEqOfEq ambient else
      if i == 12 then pure twist else mkHEqRefl la[i]!
    hs := hs.push h
  let proof ← instantiateMVars (← nativeHZeroApplicationCongr013 left right hs)
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeHZero015 unresolved/recovery original map13 congruence."
  goal.assign proof
  replaceMainGoal []


end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_naturalityOwnLaw011
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      type_of% (native_hzero_naturality_own011% (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  exact native_hzero_naturality_own011% (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_leftPredicateEq012
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_naturality_endpoint012% 0 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_rightDictionaryValueHEq012
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_naturality_endpoint012% 2 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_exactPointRingEq013
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_dictionary_cut013% 0 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_exactPointSpecEq013
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_dictionary_cut013% 1 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_spec_congr013 (nativeHZeroSheafInclusion_exactPointRingEq013 p hp P hP ell hell s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_exactPointClosedProofHEq013
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_dictionary_cut013% 2 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_closed_proof013

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_exactPointDictionaryHEq013
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_dictionary_cut013% 3 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_dictionary_congr013
    (nativeHZeroSheafInclusion_exactPointSpecEq013 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_exactPointClosedProofHEq013 p hp P hP ell hell s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_exactDictionaryTypeEq013
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_dictionary_cut013% 4 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_exactSectionCarrierEq013
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_dictionary_cut013% 5 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_exactDictionaryFamilyHEq013
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_dictionary_cut013% 6 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_exactDictionaryFunLikeHEq013
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_dictionary_cut013% 7 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_factorEvaluationVectorsDiagnostic014
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      True := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_factor_diagnostic014 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_exactFactorEvaluationTypeEq014
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_factor_cut014% 0 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_exactFactorEvaluationSourceEq014
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_factor_cut014% 1 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_exactFactorEvaluationFamilyHEq014
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_factor_cut014% 2 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_exactFactorEvaluationFunLikeHEq014
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_factor_cut014% 3 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_exactFactorAmbientProjEq015
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_factor_object015% 0 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_exactFactorPositiveTwistHEq015
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_factor_object015% 1 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_exactFactorEvaluationMapHEq014
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_factor_cut014% 4 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_factor_factory015
    (nativeHZeroSheafInclusion_exactFactorAmbientProjEq015 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_exactFactorPositiveTwistHEq015 p hp P hP ell hell s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_exactFactorEvaluationInputHEq014
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_factor_cut014% 5 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_factor_input_refl014

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_exactFactorSectionHEq013
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_dictionary_cut013% 8 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_factor_evaluation014
    (nativeHZeroSheafInclusion_exactFactorEvaluationTypeEq014 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_exactFactorEvaluationSourceEq014 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_exactFactorEvaluationFamilyHEq014 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_exactFactorEvaluationFunLikeHEq014 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_exactFactorEvaluationMapHEq014 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_exactFactorEvaluationInputHEq014 p hp P hP ell hell s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_leftDictionaryValueHEq012
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_naturality_endpoint012% 1 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_left_evaluation013
    (nativeHZeroSheafInclusion_exactDictionaryTypeEq013 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_exactSectionCarrierEq013 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_exactDictionaryFamilyHEq013 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_exactDictionaryFunLikeHEq013 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_exactPointDictionaryHEq013 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_exactFactorSectionHEq013 p hp P hP ell hell s)


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_leftPolynomialEndpointEq012
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_naturality_endpoint012% 3 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_naturality_left_projection012
    (nativeHZeroSheafInclusion_leftPredicateEq012 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_leftDictionaryValueHEq012 p hp P hP ell hell s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_rightPolynomialEndpointEq012
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_naturality_endpoint012% 4 (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_naturality_right_projection012
    (nativeHZeroSheafInclusion_rightDictionaryValueHEq012 p hp P hP ell hell s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_naturalityTypeEq011
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_naturality_type011% (nativeHZeroSheafInclusion_naturality_proposition011 p hp P hP ell hell) at s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_naturality_proposition012
    (nativeHZeroSheafInclusion_leftPolynomialEndpointEq012 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_rightPolynomialEndpointEq012 p hp P hP ell hell s)


meta section
open Lean Meta Elab Tactic

/-- ONLY the exact checked own-law10 / type-equation10 original application vectors. -/
private def nativeHZeroNaturalityMPVectors016 (suppliedLaw suppliedType : Syntax) :
    Term.TermElabM (Array Expr) := do
  let law ← Term.elabTerm suppliedLaw none (catchExPostpone := false)
  let typeEq ← Term.elabTerm suppliedType none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let law ← instantiateMVars law
  let typeEq ← instantiateMVars typeEq
  unless law.getAppFn.isConstOf ``nativeHZeroSheafInclusion_naturalityOwnLaw011 &&
      typeEq.getAppFn.isConstOf ``nativeHZeroSheafInclusion_naturalityTypeEq011 &&
      law.getAppArgs.size == 10 && typeEq.getAppArgs.size == 10 do
    throwError "NativeHZero016 refused another original law10/type-equation10."
  let la := law.getAppArgs
  let ta := typeEq.getAppArgs
  for i in [:10] do
    logInfo m!"NativeHZero016 EXACT ownlaw/typeEq argument[{i}] raw-match={la[i]!.equal ta[i]!}; heads/arities={nativeHZeroHeadLabel006 la[i]!}/{nativeHZeroHeadLabel006 ta[i]!},{la[i]!.getAppArgs.size}/{ta[i]!.getAppArgs.size}."
    unless la[i]!.equal ta[i]! do
      throwError "NativeHZero016 refused changed original law/type-equation argument[{i}]."
  let lawType ← instantiateMVars (← inferType law)
  let typeEqType ← instantiateMVars (← inferType typeEq)
  let some (typeCarrier, sourceType, nativeType) := typeEqType.consumeMData.headBeta.eq?
    | throwError "NativeHZero016 expected original checked proposition Eq."
  unless typeCarrier.isSort && typeCarrier.sortLevel!.isZero do
    throwError "NativeHZero016 refused an equality outside the actual proposition carrier."
  logInfo m!"NativeHZero016 exact MP source/law raw-match={sourceType.equal lawType}; source/native heads/arities={nativeHZeroHeadLabel006 sourceType}/{nativeHZeroHeadLabel006 nativeType},{sourceType.getAppArgs.size}/{nativeType.getAppArgs.size}."
  unless sourceType.equal lawType do
    throwError "NativeHZero016 refused another exact stored MP source type."
  for (label, endpoint) in #[
      ("ownLawType", lawType), ("typeEqType", typeEqType), ("nativeTarget", nativeType)] do
    logInfo m!"NativeHZero016 ACTUAL {label}: {endpoint}."
  let proof := mkAppN (mkConst ``Eq.mp [Level.zero]) #[sourceType, nativeType, typeEq, law]
  let ownType ← instantiateMVars (← inferType proof)
  logInfo m!"NativeHZero016 ACTUAL MP ownType/nativeTarget raw-match={ownType.equal nativeType}; type={ownType}."
  unless ownType.equal nativeType do
    throwError "NativeHZero016 refused a changed own MP target type."
  for e in #[law, typeEq, lawType, typeEqType, sourceType, nativeType, proof, ownType] do
    if e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "NativeHZero016 refused unresolved/recovery original MP vector."
  return #[law, typeEq, lawType, typeEqType, sourceType, nativeType, proof, ownType]

elab "native_hzero_naturality_mp_type016% " suppliedLaw:term ", " suppliedType:term : term => do
  let v ← nativeHZeroNaturalityMPVectors016 suppliedLaw suppliedType
  return v[7]!

elab "native_hzero_naturality_mp016% " suppliedLaw:term ", " suppliedType:term : term => do
  let v ← nativeHZeroNaturalityMPVectors016 suppliedLaw suppliedType
  return v[6]!

elab "native_hzero_naturality_mp_diagnostic016 " suppliedLaw:term ", " suppliedType:term : tactic => withMainContext do
  let _ ← nativeHZeroNaturalityMPVectors016 suppliedLaw suppliedType
  let goal ← getMainGoal
  goal.assign (mkConst ``True.intro)
  replaceMainGoal []

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_naturalityMPDiagnostic016
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      True := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  native_hzero_naturality_mp_diagnostic016 (nativeHZeroSheafInclusion_naturalityOwnLaw011 p hp P hP ell hell s), (nativeHZeroSheafInclusion_naturalityTypeEq011 p hp P hP ell hell s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_naturalityOwnMP016
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_naturality_mp_type016% (nativeHZeroSheafInclusion_naturalityOwnLaw011 p hp P hP ell hell s), (nativeHZeroSheafInclusion_naturalityTypeEq011 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
  let i := d ≫ quotientProjMap (equationIdeal p hp)
  let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
  have hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
  intro s
  exact native_hzero_naturality_mp016% (nativeHZeroSheafInclusion_naturalityOwnLaw011 p hp P hP ell hell s), (nativeHZeroSheafInclusion_naturalityTypeEq011 p hp P hP ell hell s)


meta section
open Lean Meta Elab Tactic

/-- Use ONLY the ordinary separately checked exact original MP constant. -/
elab "native_hzero_naturality_mp_exact016 " supplied:term : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let proof ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  unless proof.getAppFn.isConstOf ``nativeHZeroSheafInclusion_naturalityOwnMP016 &&
      proof.getAppArgs.size == 10 do
    throwError "NativeHZero016 refused a changed original own-MP10 constant."
  let ownType ← instantiateMVars (← inferType proof)
  logInfo m!"NativeHZero016 FINAL exact ownMP/target raw-match={ownType.equal target}."
  unless ownType.equal target do
    logInfo m!"NativeHZero016 ACTUAL final own MP type: {ownType}."
    logInfo m!"NativeHZero016 ACTUAL final target type: {target}."
    throwError "NativeHZero016 refused changed final original native endpoints."
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeHZero016 unresolved/recovery own-MP application."
  goal.assign proof
  replaceMainGoal []

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private abbrev nativeHZeroSheafInclusion_originalWholeHeader017
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) : Prop :=
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    let r := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K L L).toRingHom)
    let i := d ≫ quotientProjMap (equationIdeal p hp)
    let q := (hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)
    let hfac : r ≫ i = q := nativeHZeroReductionFactorization005 p hp P hP ell
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      (p3ActualIdealQuadraticIntrinsicLinearEquiv q
        (actualAmbientClosedIdealTwistHZeroFactorInclusion
          (ambientToBase (R := K) (σ := Fin 4)) i r q hfac
          (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2) s)).val =
      (p3ActualIdealQuadraticIntrinsicLinearEquiv i s).val


meta section
open Lean Meta Elab Tactic

/-- Exact original full law9 / full native header9, preserving their stored Pi/let types. -/
private def nativeHZeroWholeVectors017 (suppliedLaw suppliedTarget : Syntax) :
    Term.TermElabM (Array Expr) := do
  let law ← Term.elabTerm suppliedLaw none (catchExPostpone := false)
  let target ← Term.elabTerm suppliedTarget none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let law ← instantiateMVars law
  let target ← instantiateMVars target
  unless law.getAppFn.isConstOf ``nativeHZeroSheafInclusion_naturalityOwnMP016 &&
      target.getAppFn.isConstOf ``nativeHZeroSheafInclusion_originalWholeHeader017 &&
      law.getAppArgs.size == 9 && target.getAppArgs.size == 9 do
    throwError "NativeHZero017 refused another ORIGINAL whole law9/header9."
  let la := law.getAppArgs
  let ta := target.getAppArgs
  for i in [:9] do
    logInfo m!"NativeHZero017 EXACT whole law/header argument[{i}] raw-match={la[i]!.equal ta[i]!}; heads/arities={nativeHZeroHeadLabel006 la[i]!}/{nativeHZeroHeadLabel006 ta[i]!},{la[i]!.getAppArgs.size}/{ta[i]!.getAppArgs.size}."
    unless la[i]!.equal ta[i]! do
      throwError "NativeHZero017 refused changed original whole law/header argument[{i}]."
  let ownType ← instantiateMVars (← inferType law)
  let some storedTarget ← delta? target
      (fun n => n == ``nativeHZeroSheafInclusion_originalWholeHeader017)
    | throwError "NativeHZero017 missing exact ORIGINAL whole header delta."
  logInfo m!"NativeHZero017 ACTUAL stored whole own type: {ownType}."
  logInfo m!"NativeHZero017 ACTUAL stored whole native header: {storedTarget}."
  logInfo m!"NativeHZero017 untouched whole own/native raw-match={ownType.equal storedTarget}; heads/arities={nativeHZeroHeadLabel006 ownType}/{nativeHZeroHeadLabel006 storedTarget},{ownType.getAppArgs.size}/{storedTarget.getAppArgs.size}."
  for (label, expression) in #[("ownWhole", ownType), ("nativeWhole", storedTarget)] do
    let mut current := expression
    for j in [:32] do
      match current with
      | .letE n t value body _ =>
        logInfo m!"NativeHZero017 {label} stored let[{j}] name={n}; type/value heads/arities={nativeHZeroHeadLabel006 t}/{nativeHZeroHeadLabel006 value},{t.getAppArgs.size}/{value.getAppArgs.size}."
        current := body
      | .forallE n domain body _ =>
        logInfo m!"NativeHZero017 {label} stored Pi[{j}] name={n}; domain head/arity={nativeHZeroHeadLabel006 domain},{domain.getAppArgs.size}."
        current := body
      | _ =>
        logInfo m!"NativeHZero017 {label} stored endpoint[{j}] head/arity={nativeHZeroHeadLabel006 current},{current.getAppArgs.size}."
        break
  for e in #[law, target, ownType, storedTarget] do
    if e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "NativeHZero017 refused unresolved/recovery ORIGINAL whole type vectors."
  return #[law, target, ownType, storedTarget]

elab "native_hzero_whole_type017% " suppliedLaw:term ", " suppliedTarget:term : term => do
  let v ← nativeHZeroWholeVectors017 suppliedLaw suppliedTarget
  mkEq v[2]! v[1]!

elab "native_hzero_whole_diagnostic017 " suppliedLaw:term ", " suppliedTarget:term : tactic => withMainContext do
  let _ ← nativeHZeroWholeVectors017 suppliedLaw suppliedTarget
  let goal ← getMainGoal
  goal.assign (mkConst ``True.intro)
  replaceMainGoal []

/-- Ordinary separately bounded conversion of the ORIGINAL whole Pi/let header. -/
elab "native_hzero_whole_type_refl017" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, ownType, target) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.eq?
    | throwError "NativeHZero017 expected ORIGINAL whole proposition Eq."
  unless target.getAppFn.isConstOf ``nativeHZeroSheafInclusion_originalWholeHeader017 &&
      target.getAppArgs.size == 9 do
    throwError "NativeHZero017 refused another original whole native header9."
  goal.assign (← mkEqRefl ownType)
  replaceMainGoal []

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_wholeHeaderDiagnostic017
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) : True := by
  native_hzero_whole_diagnostic017 (nativeHZeroSheafInclusion_naturalityOwnMP016 p hp P hP ell hell), (nativeHZeroSheafInclusion_originalWholeHeader017 p hp P hP ell hell)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_wholeHeaderTypeEq017
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    native_hzero_whole_type017% (nativeHZeroSheafInclusion_naturalityOwnMP016 p hp P hP ell hell), (nativeHZeroSheafInclusion_originalWholeHeader017 p hp P hP ell hell) := by
  native_hzero_whole_type_refl017


meta section
open Lean Meta Elab Tactic

elab "native_hzero_whole_transport017 " suppliedLaw:term ", " suppliedType:term : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let law ← Term.elabTerm suppliedLaw none (catchExPostpone := false)
  let typeEq ← Term.elabTerm suppliedType none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let law ← instantiateMVars law
  let typeEq ← instantiateMVars typeEq
  unless law.getAppFn.isConstOf ``nativeHZeroSheafInclusion_naturalityOwnMP016 &&
      typeEq.getAppFn.isConstOf ``nativeHZeroSheafInclusion_wholeHeaderTypeEq017 &&
      law.getAppArgs.size == 9 && typeEq.getAppArgs.size == 9 do
    throwError "NativeHZero017 refused changed ORIGINAL whole law/type-equation9."
  let la := law.getAppArgs
  let ta := typeEq.getAppArgs
  for i in [:9] do
    unless la[i]!.equal ta[i]! do
      throwError "NativeHZero017 refused changed ORIGINAL whole source argument[{i}]."
  let ownType ← instantiateMVars (← inferType law)
  let some (_, typeLeft, typeRight) :=
      (← instantiateMVars (← inferType typeEq)).consumeMData.headBeta.eq?
    | throwError "NativeHZero017 expected separately checked ORIGINAL whole type Eq."
  logInfo m!"NativeHZero017 WHOLE source/target raw matches={ownType.equal typeLeft}/{target.equal typeRight}."
  unless ownType.equal typeLeft && target.equal typeRight do
    throwError "NativeHZero017 refused changed ORIGINAL whole MP endpoints."
  let proof := mkAppN (mkConst ``Eq.mp [Level.zero]) #[ownType, target, typeEq, law]
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeHZero017 unresolved/recovery ORIGINAL whole MP."
  goal.assign proof
  replaceMainGoal []

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_originalWholeMP017
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    nativeHZeroSheafInclusion_originalWholeHeader017 p hp P hP ell hell := by
  native_hzero_whole_transport017 (nativeHZeroSheafInclusion_naturalityOwnMP016 p hp P hP ell hell),
    (nativeHZeroSheafInclusion_wholeHeaderTypeEq017 p hp P hP ell hell)

/-- The exact proved whole native law; infer its original telescope without a duplicate wrapper. -/
private abbrev nativeHZeroSheafInclusion_dictionaryNaturality010 :=
  @nativeHZeroSheafInclusion_originalWholeMP017


meta section
open Lean Meta Elab Tactic

/-- EXACT existing original dictionary congruence10 and actual whole-naturality10. -/
private def nativeHZeroPolynomialVectors019 (suppliedCongruence suppliedNaturality : Syntax) :
    Term.TermElabM (Array Expr) := do
  let congruence ← Term.elabTerm suppliedCongruence none (catchExPostpone := false)
  let naturality ← Term.elabTerm suppliedNaturality none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let congruence ← instantiateMVars congruence
  let naturality ← instantiateMVars naturality
  unless congruence.getAppFn.isConstOf ``nativeHZeroSheafInclusion_dictionaryCongruence010 &&
      naturality.getAppFn.isConstOf ``nativeHZeroSheafInclusion_dictionaryNaturality010 &&
      congruence.getAppArgs.size == 10 && naturality.getAppArgs.size == 10 do
    throwError "NativeHZero019 refused another original congruence10/naturality10."
  let ca := congruence.getAppArgs
  let na := naturality.getAppArgs
  for i in [:10] do
    logInfo m!"NativeHZero019 EXACT congruence/naturality argument[{i}] raw-match={ca[i]!.equal na[i]!}; heads/arities={nativeHZeroHeadLabel006 ca[i]!}/{nativeHZeroHeadLabel006 na[i]!},{ca[i]!.getAppArgs.size}/{na[i]!.getAppArgs.size}."
    unless ca[i]!.equal na[i]! do
      throwError "NativeHZero019 refused changed original congruence/naturality argument[{i}]."
  let congruenceType ← instantiateMVars (← inferType congruence)
  let naturalityType ← instantiateMVars (← inferType naturality)
  let some (carrier, left, midLeft) := congruenceType.consumeMData.headBeta.eq?
    | throwError "NativeHZero019 expected original congruence polynomial Eq."
  let some (nativeCarrier, midRight, right) := naturalityType.consumeMData.headBeta.eq?
    | throwError "NativeHZero019 expected original naturality polynomial Eq."
  logInfo m!"NativeHZero019 EXACT polynomial carrier/middle raw-match={carrier.equal nativeCarrier}/{midLeft.equal midRight}."
  unless carrier.equal nativeCarrier do
    throwError "NativeHZero019 refused changed original polynomial carrier/actions."
  logInfo m!"NativeHZero019 ACTUAL congruence type: {congruenceType}."
  logInfo m!"NativeHZero019 ACTUAL naturality type: {naturalityType}."
  for (label, x) in #[("middleCongruence", midLeft), ("middleNaturality", midRight)] do
    logInfo m!"NativeHZero019 {label} EXACT head/arity={nativeHZeroHeadLabel006 x},{x.getAppArgs.size}."
  let mut ll := midLeft
  let mut rr := midRight
  for depth in [:4] do
    unless ll.getAppFn.equal rr.getAppFn && ll.getAppArgs.size == rr.getAppArgs.size do
      logInfo m!"NativeHZero019 exact middle trace stops at depth[{depth}]: different original heads/arities."
      break
    let la := ll.getAppArgs
    let ra := rr.getAppArgs
    for i in [:la.size] do
      logInfo m!"NativeHZero019 middle[{depth}] EXACT argument[{i}] raw-match={la[i]!.equal ra[i]!}; heads/arities={nativeHZeroHeadLabel006 la[i]!}/{nativeHZeroHeadLabel006 ra[i]!},{la[i]!.getAppArgs.size}/{ra[i]!.getAppArgs.size}."
    if ll.getAppFn.isConstOf ``Subtype.val && la.size == 3 then
      ll := la[2]!
      rr := ra[2]!
    else if ll.getAppFn.isConstOf ``DFunLike.coe && la.size == 6 then
      -- Both dictionary5 and true factor13 remain ORIGINAL terms. Print their complete vectors.
      for slot in #[4, 5] do
        let l := la[slot]!
        let r := ra[slot]!
        if l.getAppFn.equal r.getAppFn && l.getAppArgs.size == r.getAppArgs.size then
          let aa := l.getAppArgs
          let bb := r.getAppArgs
          for j in [:aa.size] do
            logInfo m!"NativeHZero019 middle[{depth}][{slot}] EXACT argument[{j}] raw-match={aa[j]!.equal bb[j]!}; heads/arities={nativeHZeroHeadLabel006 aa[j]!}/{nativeHZeroHeadLabel006 bb[j]!},{aa[j]!.getAppArgs.size}/{bb[j]!.getAppArgs.size}."
      ll := la[5]!
      rr := ra[5]!
    else
      break
  for e in #[congruence, naturality, carrier, nativeCarrier, left, midLeft, midRight, right] do
    if e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "NativeHZero019 refused unresolved/recovery original polynomial vectors."
  return #[congruence, naturality, carrier, left, midLeft, midRight, right]


/-- FRESH actual congruence/naturality middle; NEVER reuse the earlier endpoint specimens. -/
private def nativeHZeroMiddleVectors020 (suppliedCongruence suppliedNaturality : Syntax) :
    Term.TermElabM (Array Expr) := do
  let v ← nativeHZeroPolynomialVectors019 suppliedCongruence suppliedNaturality
  let ml := v[4]!
  let mr := v[5]!
  for x in #[ml, mr] do
    unless x.getAppFn.isConstOf ``Subtype.val && x.getAppArgs.size == 3 do
      throwError "NativeHZero020 refused a changed ORIGINAL middle Subtype3."
  let ma := ml.getAppArgs
  let mb := mr.getAppArgs
  unless ma[0]!.equal mb[0]! do
    throwError "NativeHZero020 refused a changed ORIGINAL middle polynomial carrier."
  let ol := ma[2]!
  let outerRight := mb[2]!
  for x in #[ol, outerRight] do
    unless x.getAppFn.isConstOf ``DFunLike.coe && x.getAppArgs.size == 6 do
      throwError "NativeHZero020 refused changed ORIGINAL middle outer evaluation6."
  let dl := ol.getAppArgs[4]!
  let dr := outerRight.getAppArgs[4]!
  for x in #[dl, dr] do
    unless x.getAppFn.isConstOf ``p3ActualIdealQuadraticIntrinsicLinearEquiv &&
        x.getAppArgs.size == 5 do
      throwError "NativeHZero020 refused changed ORIGINAL middle dictionary5."
  unless dl.getAppFn.equal dr.getAppFn do
    throwError "NativeHZero020 refused changed ORIGINAL dictionary universes."
  for i in [:3] do
    unless dl.getAppArgs[i]!.equal dr.getAppArgs[i]! do
      throwError "NativeHZero020 refused changed ORIGINAL raw-identical dictionary argument[{i}]."
  let il := ol.getAppArgs[5]!
  let ir := outerRight.getAppArgs[5]!
  for x in #[il, ir] do
    unless x.getAppFn.isConstOf ``DFunLike.coe && x.getAppArgs.size == 6 do
      throwError "NativeHZero020 refused changed ORIGINAL middle inner evaluation6."
  let fl := il.getAppArgs[4]!
  let fr := ir.getAppArgs[4]!
  for x in #[fl, fr] do
    unless x.getAppFn.isConstOf ``actualAmbientClosedIdealTwistHZeroFactorInclusion &&
        x.getAppArgs.size == 13 do
      throwError "NativeHZero020 refused changed ORIGINAL middle factor13."
  unless fl.getAppFn.equal fr.getAppFn do
    throwError "NativeHZero020 refused changed ORIGINAL factor universes."
  for i in #[0, 1, 4, 5, 9] do
    unless fl.getAppArgs[i]!.equal fr.getAppArgs[i]! do
      throwError "NativeHZero020 refused changed ORIGINAL raw-identical factor argument[{i}]."
  let sectionValue := v[0]!.getAppArgs[9]!
  unless il.getAppArgs[5]!.equal sectionValue && ir.getAppArgs[5]!.equal sectionValue do
    throwError "NativeHZero020 refused a changed ORIGINAL supplied source section."
  for (label, l, r) in #[
      ("dictionaryPointMap", dl.getAppArgs[3]!, dr.getAppArgs[3]!),
      ("factorAmbient", fl.getAppArgs[2]!, fr.getAppArgs[2]!),
      ("factorSourceSpec", fl.getAppArgs[3]!, fr.getAppArgs[3]!),
      ("factorImmersion", fl.getAppArgs[6]!, fr.getAppArgs[6]!),
      ("factorReduction", fl.getAppArgs[7]!, fr.getAppArgs[7]!),
      ("factorPointMap", fl.getAppArgs[8]!, fr.getAppArgs[8]!),
      ("factorPositiveTwist", fl.getAppArgs[12]!, fr.getAppArgs[12]!)] do
    logInfo m!"NativeHZero020 {label} ORIGINAL heads/arities={nativeHZeroHeadLabel006 l}/{nativeHZeroHeadLabel006 r},{l.getAppArgs.size}/{r.getAppArgs.size}."
    let la := l.getAppArgs
    let ra := r.getAppArgs
    if l.getAppFn.equal r.getAppFn && la.size == ra.size then
      for i in [:la.size] do
        logInfo m!"NativeHZero020 {label} EXACT nested argument[{i}] raw-match={la[i]!.equal ra[i]!}; heads/arities={nativeHZeroHeadLabel006 la[i]!}/{nativeHZeroHeadLabel006 ra[i]!},{la[i]!.getAppArgs.size}/{ra[i]!.getAppArgs.size}."
        let aa := la[i]!.getAppArgs
        let bb := ra[i]!.getAppArgs
        if la[i]!.getAppFn.equal ra[i]!.getAppFn && aa.size == bb.size then
          for j in [:aa.size] do
            logInfo m!"NativeHZero020 {label} EXACT nested argument[{i}][{j}] raw-match={aa[j]!.equal bb[j]!}; heads/arities={nativeHZeroHeadLabel006 aa[j]!}/{nativeHZeroHeadLabel006 bb[j]!}."
  return #[ma[0]!, ml, mr, ma[1]!, mb[1]!, ol, outerRight, dl, dr, il, ir, fl, fr]

elab "native_hzero_middle_cut020% " stage:num index:num suppliedCongruence:term ", " suppliedNaturality:term : term => do
  let v ← nativeHZeroMiddleVectors020 suppliedCongruence suppliedNaturality
  let i := index.getNat
  match stage.getNat with
  | 0 =>
    unless i == 0 do throwError "NativeHZero020 predicate index out of range."
    mkEq v[3]! v[4]!
  | 1 =>
    unless i < 6 do throwError "NativeHZero020 outer evaluation index out of range."
    let l := v[5]!.getAppArgs[i]!
    let r := v[6]!.getAppArgs[i]!
    if i < 2 then mkEq l r else mkHEq l r
  | 2 =>
    unless i == 3 || i == 4 do throwError "NativeHZero020 dictionary index out of range."
    mkHEq v[7]!.getAppArgs[i]! v[8]!.getAppArgs[i]!
  | 3 =>
    unless #[2, 3, 6, 7, 8, 10, 11, 12].contains i do
      throwError "NativeHZero020 factor13 cut index out of range."
    let l := v[11]!.getAppArgs[i]!
    let r := v[12]!.getAppArgs[i]!
    if i == 2 || i == 3 then mkEq l r else mkHEq l r
  | 4 =>
    unless i < 6 do throwError "NativeHZero020 inner evaluation index out of range."
    let l := v[9]!.getAppArgs[i]!
    let r := v[10]!.getAppArgs[i]!
    if i < 2 then mkEq l r else mkHEq l r
  | _ => throwError "NativeHZero020 original middle cut stage out of range."

/-- Fresh original vectors plus ordinary congruence; exact checked premises for EVERY differing slot. -/
elab "native_hzero_middle_congr020 " arity:num " using " "[" ps:term,+ "]" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
  let (left, right, toEq) ← match target.eq?, target.heq? with
    | some (_, l, r), _ => pure (l, r, true)
    | _, some (_, l, _, r) => pure (l, r, false)
    | _, _ => throwError "NativeHZero020 expected exact ORIGINAL middle Eq/HEq."
  let n := arity.getNat
  unless left.getAppFn.equal right.getAppFn && left.getAppArgs.size == n && right.getAppArgs.size == n do
    throwError "NativeHZero020 refused changed original application head/full arity."
  let la := left.getAppArgs
  let ra := right.getAppArgs
  let mut supplied := #[]
  for stx in ps.getElems do
    let h ← Term.elabTerm stx none (catchExPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    supplied := supplied.push (← instantiateMVars h)
  let mut hs := #[]
  if n == 3 then
    unless left.getAppFn.isConstOf ``Subtype.val && supplied.size == 2 && la[0]!.equal ra[0]! do
      throwError "NativeHZero020 refused changed ORIGINAL Subtype3 carrier/proofs."
    hs := #[(← mkHEqRefl la[0]!), (← mkHEqOfEq supplied[0]!), supplied[1]!]
  else if n == 5 then
    unless left.getAppFn.isConstOf ``p3ActualIdealQuadraticIntrinsicLinearEquiv && supplied.size == 2 do
      throwError "NativeHZero020 refused changed ORIGINAL dictionary5/proofs."
    for i in [:3] do
      unless la[i]!.equal ra[i]! do
        throwError "NativeHZero020 refused changed ORIGINAL raw dictionary argument[{i}]."
      hs := hs.push (← mkHEqRefl la[i]!)
    hs := hs ++ supplied
  else if n == 6 then
    unless left.getAppFn.isConstOf ``DFunLike.coe && supplied.size == 6 do
      throwError "NativeHZero020 refused changed ORIGINAL evaluation6/proofs."
    for i in [:6] do
      let h ← if i < 2 then mkHEqOfEq supplied[i]! else pure supplied[i]!
      hs := hs.push h
  else if n == 13 then
    unless left.getAppFn.isConstOf ``actualAmbientClosedIdealTwistHZeroFactorInclusion && supplied.size == 8 do
      throwError "NativeHZero020 refused changed ORIGINAL factor13/proofs."
    let differing := #[2, 3, 6, 7, 8, 10, 11, 12]
    let mut j := 0
    for i in [:13] do
      if differing.contains i then
        let h ← if i == 2 || i == 3 then mkHEqOfEq supplied[j]! else pure supplied[j]!
        hs := hs.push h
        j := j + 1
      else
        unless la[i]!.equal ra[i]! do
          throwError "NativeHZero020 refused changed ORIGINAL raw-identical factor argument[{i}]."
        hs := hs.push (← mkHEqRefl la[i]!)
  else
    throwError "NativeHZero020 unexpected actual middle application arity."
  let proof ← nativeHZeroApplicationCongr013 left right hs
  let proof ← if toEq then mkEqOfHEq proof else pure proof
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeHZero020 unresolved/recovery ORIGINAL middle congruence."
  goal.assign proof
  replaceMainGoal []

elab "native_hzero_middle_value020% " suppliedCongruence:term ", " suppliedNaturality:term : term => do
  let v ← nativeHZeroMiddleVectors020 suppliedCongruence suppliedNaturality
  mkHEq v[5]! v[6]!

elab "native_hzero_polynomial_cut019% " index:num suppliedCongruence:term ", " suppliedNaturality:term : term => do
  let v ← nativeHZeroPolynomialVectors019 suppliedCongruence suppliedNaturality
  match index.getNat with
  | 0 => mkEq v[4]! v[5]!
  | 1 => mkEq v[3]! v[6]!
  | _ => throwError "NativeHZero019 original polynomial cut index out of range."

elab "native_hzero_polynomial_diagnostic019 " suppliedCongruence:term ", " suppliedNaturality:term : tactic => withMainContext do
  let _ ← nativeHZeroPolynomialVectors019 suppliedCongruence suppliedNaturality
  let goal ← getMainGoal
  goal.assign (mkConst ``True.intro)
  replaceMainGoal []

elab "native_hzero_polynomial_chain019 " suppliedCongruence:term ", " suppliedNaturality:term ", " suppliedMiddle:term : tactic => withMainContext do
  let v ← nativeHZeroPolynomialVectors019 suppliedCongruence suppliedNaturality
  let middle ← Term.elabTerm suppliedMiddle none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let middle ← instantiateMVars middle
  let some (carrier, ml, mr) := (← instantiateMVars (← inferType middle)).consumeMData.headBeta.eq?
    | throwError "NativeHZero019 expected separately checked ORIGINAL middle Eq."
  unless carrier.equal v[2]! && ml.equal v[4]! && mr.equal v[5]! do
    throwError "NativeHZero019 refused replacement original polynomial middle endpoints."
  let goal ← getMainGoal
  let some (targetCarrier, targetLeft, targetRight) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.eq?
    | throwError "NativeHZero019 expected EXACT own polynomial-chain Eq."
  logInfo m!"NativeHZero021 EXACT own chain carrier/left/right raw matches={targetCarrier.equal v[2]!}/{targetLeft.equal v[3]!}/{targetRight.equal v[6]!}."
  for (label, suppliedEndpoint, goalEndpoint) in #[
      ("carrier", v[2]!, targetCarrier), ("left", v[3]!, targetLeft), ("right", v[6]!, targetRight)] do
    logInfo m!"NativeHZero021 {label} EXACT supplied/goal heads/arities={nativeHZeroHeadLabel006 suppliedEndpoint}/{nativeHZeroHeadLabel006 goalEndpoint},{suppliedEndpoint.getAppArgs.size}/{goalEndpoint.getAppArgs.size}."
    unless suppliedEndpoint.equal goalEndpoint do
      logInfo m!"NativeHZero021 ACTUAL {label} supplied expression: {suppliedEndpoint}."
      logInfo m!"NativeHZero021 ACTUAL {label} goal expression: {goalEndpoint}."
      let mut l := suppliedEndpoint
      let mut r := goalEndpoint
      for depth in [:4] do
        unless l.getAppFn.equal r.getAppFn && l.getAppArgs.size == r.getAppArgs.size do
          logInfo m!"NativeHZero021 {label} ORIGINAL nested comparison stops at depth[{depth}]."
          break
        let la := l.getAppArgs
        let ra := r.getAppArgs
        for j in [:la.size] do
          logInfo m!"NativeHZero021 {label}[{depth}] EXACT argument[{j}] raw-match={la[j]!.equal ra[j]!}; heads/arities={nativeHZeroHeadLabel006 la[j]!}/{nativeHZeroHeadLabel006 ra[j]!},{la[j]!.getAppArgs.size}/{ra[j]!.getAppArgs.size}."
        if l.getAppFn.isConstOf ``Subtype.val && la.size == 3 then
          l := la[2]!
          r := ra[2]!
        else if l.getAppFn.isConstOf ``DFunLike.coe && la.size == 6 then
          for slot in #[4, 5] do
            let ll := la[slot]!
            let rr := ra[slot]!
            if ll.getAppFn.equal rr.getAppFn && ll.getAppArgs.size == rr.getAppArgs.size then
              let aa := ll.getAppArgs
              let bb := rr.getAppArgs
              for j in [:aa.size] do
                logInfo m!"NativeHZero021 {label}[{depth}][{slot}] EXACT argument[{j}] raw-match={aa[j]!.equal bb[j]!}; heads/arities={nativeHZeroHeadLabel006 aa[j]!}/{nativeHZeroHeadLabel006 bb[j]!}."
          l := la[5]!
          r := ra[5]!
        else
          break
  unless targetCarrier.equal v[2]! && targetLeft.equal v[3]! && targetRight.equal v[6]! do
    throwError "NativeHZero019 refused changed ORIGINAL own chain endpoints."
  let proof ← instantiateMVars (← mkEqTrans (← mkEqTrans v[0]! middle) v[1]!)
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeHZero019 unresolved/recovery original polynomial trans chain."
  goal.assign proof
  replaceMainGoal []


/-- Expose ONLY the original head Pi/let telescope; never dsimp its polynomial projections. -/
elab "native_hzero_polynomial_head_telescope021" : tactic => withMainContext do
  let goal ← getMainGoal
  let original ← instantiateMVars (← goal.getType)
  let exposed := nativeHZeroHeadZeta006 32 original
  let .forallE _ _ _ _ := exposed
    | throwError "NativeHZero021 expected ORIGINAL source-section Pi after head beta/zeta."
  logInfo m!"NativeHZero021 original/exposed telescope heads/arities={nativeHZeroHeadLabel006 original}/{nativeHZeroHeadLabel006 exposed},{original.getAppArgs.size}/{exposed.getAppArgs.size}."
  if exposed.hasMVar || exposed.hasLevelMVar || exposed.hasLooseBVars || exposed.hasSorry then
    throwError "NativeHZero021 unresolved/recovery ORIGINAL exposed telescope."
  let goal ← goal.change exposed
  replaceMainGoal [goal]


end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_polynomialDiagnostic019
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      True := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_polynomial_diagnostic019 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middlePredicateEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 0 0 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleOuterTypeEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 1 0 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleOuterSourceEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 1 1 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleOuterFamilyHEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 1 2 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleOuterFunLikeHEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 1 3 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleDictionaryPointMapHEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 2 3 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleDictionaryClosedProofHEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 2 4 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_closed_proof013

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleFactorAmbientProjEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 3 2 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleFactorSourceSpecEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 3 3 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleFactorImmersionMapHEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 3 6 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleFactorReductionMapHEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 3 7 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleFactorPointMapHEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 3 8 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleFactorImmersionClosedProofHEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 3 10 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_closed_proof013

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleFactorPointClosedProofHEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 3 11 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_closed_proof013

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleFactorPositiveTwistHEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 3 12 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleInnerTypeEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 4 0 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleInnerSourceEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 4 1 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleInnerFamilyHEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 4 2 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleInnerFunLikeHEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 4 3 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_naturality_endpoint_refl012

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleInnerInputHEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 4 5 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_factor_input_refl014

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleDictionaryFactoryHEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 1 4 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_middle_congr020 5 using [
    (nativeHZeroSheafInclusion_middleDictionaryPointMapHEq020 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_middleDictionaryClosedProofHEq020 p hp P hP ell hell s)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleFactorFactoryHEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 4 4 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_middle_congr020 13 using [
    (nativeHZeroSheafInclusion_middleFactorAmbientProjEq020 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_middleFactorSourceSpecEq020 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_middleFactorImmersionMapHEq020 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_middleFactorReductionMapHEq020 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_middleFactorPointMapHEq020 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_middleFactorImmersionClosedProofHEq020 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_middleFactorPointClosedProofHEq020 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_middleFactorPositiveTwistHEq020 p hp P hP ell hell s)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleInnerValueHEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_cut020% 1 5 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_middle_congr020 6 using [
    (nativeHZeroSheafInclusion_middleInnerTypeEq020 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_middleInnerSourceEq020 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_middleInnerFamilyHEq020 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_middleInnerFunLikeHEq020 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_middleFactorFactoryHEq020 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_middleInnerInputHEq020 p hp P hP ell hell s)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_middleOuterValueHEq020
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_middle_value020% (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_middle_congr020 6 using [
    (nativeHZeroSheafInclusion_middleOuterTypeEq020 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_middleOuterSourceEq020 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_middleOuterFamilyHEq020 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_middleOuterFunLikeHEq020 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_middleDictionaryFactoryHEq020 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_middleInnerValueHEq020 p hp P hP ell hell s)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_polynomialMiddleEq019
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_polynomial_cut019% 0 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  native_hzero_middle_congr020 3 using [
    (nativeHZeroSheafInclusion_middlePredicateEq020 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_middleOuterValueHEq020 p hp P hP ell hell s)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_polynomialOwnChain019
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      native_hzero_polynomial_cut019% 1 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s) := by
  native_hzero_polynomial_head_telescope021
  intro s
  native_hzero_polynomial_chain019 (nativeHZeroSheafInclusion_dictionaryCongruence010 p hp P hP ell hell s), (nativeHZeroSheafInclusion_dictionaryNaturality010 p hp P hP ell hell s),
    (nativeHZeroSheafInclusion_polynomialMiddleEq019 p hp P hP ell hell s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private abbrev nativeHZeroSheafInclusion_originalPolynomialHeader019
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) : Prop :=
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
      (p3ActualIdealQuadraticIntrinsicLinearEquiv
        ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp))
        (actualOriginalPositiveTwoNativeJetHZeroSheafInclusion p hp P hP ell hell s)).val =
      (p3ActualIdealQuadraticIntrinsicLinearEquiv
        (d ≫ quotientProjMap (equationIdeal p hp)) s).val


meta section
open Lean Meta Elab Tactic

private def nativeHZeroPolynomialWholeVectors019 (suppliedLaw suppliedTarget : Syntax) :
    Term.TermElabM (Array Expr) := do
  let law ← Term.elabTerm suppliedLaw none (catchExPostpone := false)
  let target ← Term.elabTerm suppliedTarget none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let law ← instantiateMVars law
  let target ← instantiateMVars target
  unless law.getAppFn.isConstOf ``nativeHZeroSheafInclusion_polynomialOwnChain019 &&
      target.getAppFn.isConstOf ``nativeHZeroSheafInclusion_originalPolynomialHeader019 &&
      law.getAppArgs.size == 9 && target.getAppArgs.size == 9 do
    throwError "NativeHZero019 refused another ORIGINAL polynomial whole law/header9."
  for i in [:9] do
    unless law.getAppArgs[i]!.equal target.getAppArgs[i]! do
      throwError "NativeHZero019 refused changed ORIGINAL polynomial whole argument[{i}]."
  let ownType ← instantiateMVars (← inferType law)
  let some storedTarget ← delta? target
      (fun n => n == ``nativeHZeroSheafInclusion_originalPolynomialHeader019)
    | throwError "NativeHZero019 missing ORIGINAL polynomial whole header delta."
  logInfo m!"NativeHZero019 ACTUAL own polynomial whole type: {ownType}."
  logInfo m!"NativeHZero019 ACTUAL original polynomial whole header: {storedTarget}."
  logInfo m!"NativeHZero019 untouched polynomial whole raw-match={ownType.equal storedTarget}."
  for e in #[law, target, ownType, storedTarget] do
    if e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "NativeHZero019 refused unresolved/recovery ORIGINAL polynomial whole vectors."
  return #[law, target, ownType]

elab "native_hzero_polynomial_whole_type019% " suppliedLaw:term ", " suppliedTarget:term : term => do
  let v ← nativeHZeroPolynomialWholeVectors019 suppliedLaw suppliedTarget
  mkEq v[2]! v[1]!

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_polynomialWholeTypeEq019
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    native_hzero_polynomial_whole_type019% (nativeHZeroSheafInclusion_polynomialOwnChain019 p hp P hP ell hell), (nativeHZeroSheafInclusion_originalPolynomialHeader019 p hp P hP ell hell) := by
  native_hzero_naturality_endpoint_refl012


meta section
open Lean Meta Elab Tactic

elab "native_hzero_polynomial_whole_transport019 " suppliedLaw:term ", " suppliedType:term : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let law ← Term.elabTerm suppliedLaw none (catchExPostpone := false)
  let typeEq ← Term.elabTerm suppliedType none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let law ← instantiateMVars law
  let typeEq ← instantiateMVars typeEq
  unless law.getAppFn.isConstOf ``nativeHZeroSheafInclusion_polynomialOwnChain019 &&
      typeEq.getAppFn.isConstOf ``nativeHZeroSheafInclusion_polynomialWholeTypeEq019 &&
      law.getAppArgs.size == 9 && typeEq.getAppArgs.size == 9 do
    throwError "NativeHZero019 refused changed ORIGINAL polynomial whole law/type9."
  for i in [:9] do
    unless law.getAppArgs[i]!.equal typeEq.getAppArgs[i]! do
      throwError "NativeHZero019 refused changed ORIGINAL polynomial whole source argument[{i}]."
  let ownType ← instantiateMVars (← inferType law)
  let some (_, source, nativeTarget) :=
      (← instantiateMVars (← inferType typeEq)).consumeMData.headBeta.eq?
    | throwError "NativeHZero019 expected ORIGINAL checked polynomial whole type Eq."
  logInfo m!"NativeHZero019 polynomial WHOLE MP source/target raw-match={ownType.equal source}/{target.equal nativeTarget}."
  unless ownType.equal source && target.equal nativeTarget do
    throwError "NativeHZero019 refused changed ORIGINAL polynomial whole MP endpoints."
  let proof := mkAppN (mkConst ``Eq.mp [Level.zero]) #[source, nativeTarget, typeEq, law]
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeHZero019 unresolved/recovery ORIGINAL polynomial whole MP."
  goal.assign proof
  replaceMainGoal []

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma nativeHZeroSheafInclusion_originalPolynomialWholeMP019
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    nativeHZeroSheafInclusion_originalPolynomialHeader019 p hp P hP ell hell := by
  native_hzero_polynomial_whole_transport019 (nativeHZeroSheafInclusion_polynomialOwnChain019 p hp P hP ell hell),
    (nativeHZeroSheafInclusion_polynomialWholeTypeEq019 p hp P hP ell hell)

/-- Inferred alias of the genuinely proved ORIGINAL polynomial header, avoiding its duplicate wrapper. -/
private abbrev nativeHZeroSheafInclusion_polynomial003 :=
  @nativeHZeroSheafInclusion_originalPolynomialWholeMP019

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The literal native square: forgetting the native-Phi kernel gives
exactly the genuine sheaf-induced H0 inclusion, on every section. -/
lemma actualOriginalPositiveTwoNativeJetHZeroKernelEquiv_sheaf_square
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    ∀ s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)),
    (actualOriginalPositiveTwoNativeJetHZeroKernelEquiv p hp P hP ell hell s).val =
      actualOriginalPositiveTwoNativeJetHZeroSheafInclusion p hp P hP ell hell s := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro s
  exact nativeHZeroSections_eq_of_polynomial_eq003
    ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp))
    ((actualOriginalPositiveTwoNativeJetHZeroKernelEquiv p hp P hP ell hell s).val)
    (actualOriginalPositiveTwoNativeJetHZeroSheafInclusion p hp P hP ell hell s)
    ((actualOriginalPositiveTwoNativeJetHZeroKernelEquiv_polynomial p hp P hP ell hell s).trans
      (nativeHZeroSheafInclusion_polynomial003 p hp P hP ell hell s).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Whole K-linear-map form of the square, with the actual kernel subtype. -/
lemma actualOriginalPositiveTwoNativeJetHZeroKernelEquiv_sheaf_square_linearMap
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
    (LinearMap.ker ((ell.restrictScalars K).comp
      (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP))).subtype.comp
      (actualOriginalPositiveTwoNativeJetHZeroKernelEquiv p hp P hP ell hell).toLinearMap =
      actualOriginalPositiveTwoNativeJetHZeroSheafInclusion p hp P hP ell hell := by
  dsimp only
  apply LinearMap.ext
  intro s
  exact actualOriginalPositiveTwoNativeJetHZeroKernelEquiv_sheaf_square p hp P hP ell hell s

end PfaffianDescent
