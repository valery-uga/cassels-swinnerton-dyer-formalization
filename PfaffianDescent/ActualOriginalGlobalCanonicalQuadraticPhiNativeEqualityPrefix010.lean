import PfaffianDescent.ActualOriginalGlobalCanonicalQuadraticPhiNativeLinear
import PfaffianDescent.ActualOriginalPositiveTwoNativeTargetComparison
import PfaffianDescent.ActualOriginalIdealQuadraticPositiveTwoPhi

/- SOURCE ONLY / UNVERIFIED. The genuinely GLOBAL/chart-free original
Phi equals its internally derived SAME native-chart realization. Actual
source, twist and target comparisons are imported as proved theorems,
never supplied as certificates. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private lemma actualOriginalGlobalNativeEqualityMapPoint004
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
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
    let E := actualCubicPositiveTwoOriginalNativePointFiberEquiv p hp
      ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization
    E.toLinearMap (actualOriginalGlobalCanonicalQuadraticPhi p hp P s) =
      actualOriginalPositiveTwoContractedNativeDifferentialMap p hp P hP
        (actualOriginalGlobalCanonicalQuadraticPhi p hp P s) := by
  intro C R L E
  exact LinearMap.congr_fun
    (actualCubicPositiveTwoOriginalNativePointFiberEquiv_eq_contracted p hp P hP)
    (actualOriginalGlobalCanonicalQuadraticPhi p hp P s)

/- This ordinary alias retains the producer's OWN inferred local-let type.
No annotated E/d target or transitivity application is checked here. -/
private def actualOriginalGlobalNativeEqualityCoefficientOwn005
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :=
  actualOriginalGlobalCanonicalQuadraticPhi_native_contracted_coefficient p hp P hP s

meta section
open Lean Meta Elab Term

def originalNativeEqualityNoRecovery005 (value : Expr) : TermElabM Expr := do
  Term.synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  if value.hasMVar || value.hasLevelMVar || value.hasLooseBVars || value.hasSorry then
    throwError "NativeEquality005 unresolved or recovery expression."
  return value

/-- Only the inferred declaration type's OUTER local-let/beta spine is
exposed. No map, category, scalar dictionary or producer body is unfolded. -/
def originalNativeEqualityHeadLets005 (value : Expr) : TermElabM Expr := do
  let mut cursor := value
  for _ in [:32] do
    cursor := cursor.consumeMData.headBeta
    match cursor with
    | .letE _ _ assigned body _ => cursor := body.instantiate1 assigned
    | _ => return cursor
  throwError "NativeEquality005 original outer local-let spine exceeded32."

private structure NativeEqualityCarrierDiffState006 where
  remaining : Nat := 512
  leaves : Nat := 0
  stopped : Bool := false

private def nativeEqualityExprHead006 (e : Expr) : String :=
  let e := e.consumeMData
  let head := match e.getAppFn with
    | .const name levels => s!"const {name} levels={levels}"
    | .sort level => s!"sort {level}"
    | .fvar id => s!"fvar {id.name}"
    | .bvar index => s!"bvar {index}"
    | .proj name index _ => s!"projection {name}[{index}]"
    | .lam _ _ _ binder => s!"lambda binder={repr binder}"
    | .forallE _ _ _ binder => s!"forall binder={repr binder}"
    | .letE _ _ _ _ _ => "let"
    | .mvar id => s!"mvar {id.name}"
    | .lit value => s!"literal {repr value}"
    | .mdata _ _ => "metadata"
    | .app _ _ => "application"
  s!"{head}; arity={e.getAppArgs.size}"

private def nativeEqualityDiffLeaf006 (path : String) (left right : Expr) :
    StateT NativeEqualityCarrierDiffState006 TermElabM Unit := do
  let st ← get
  if st.leaves >= 16 then
    modify fun st => { st with stopped := true }
    return
  logInfo m!"NativeEquality006 DIFF {path}: LEFT[{nativeEqualityExprHead006 left}]; RIGHT[{nativeEqualityExprHead006 right}]."
  modify fun st => { st with leaves := st.leaves + 1 }

/-- Bounded structural comparison only. No expression is normalized except
consuming metadata, and no equality/typechecking API is invoked. -/
private partial def nativeEqualityCarrierDiff006 (left0 right0 : Expr)
    (path : String) (depth : Nat) :
    StateT NativeEqualityCarrierDiffState006 TermElabM Unit := do
  let st ← get
  if st.remaining == 0 || st.leaves >= 16 then
    modify fun st => { st with stopped := true }
    return
  modify fun st => { st with remaining := st.remaining - 1 }
  let left := left0.consumeMData
  let right := right0.consumeMData
  if left.equal right then return
  if depth == 0 then
    nativeEqualityDiffLeaf006 (path ++ ".DEPTH_BOUND") left right
    modify fun st => { st with stopped := true }
    return
  match left, right with
  | .app _ _, .app _ _ =>
    let la := left.getAppArgs
    let ra := right.getAppArgs
    if la.size != ra.size then
      nativeEqualityDiffLeaf006 (path ++ ".ARITY") left right
    else
      nativeEqualityCarrierDiff006 left.getAppFn right.getAppFn (path ++ ".head") (depth-1)
      for i in [:la.size] do
        nativeEqualityCarrierDiff006 la[i]! ra[i]! (path ++ s!".arg[{i}]") (depth-1)
  | .proj ln li lv, .proj rn ri rv =>
    if ln != rn || li != ri then
      nativeEqualityDiffLeaf006 (path ++ ".PROJECTION") left right
    else
      nativeEqualityCarrierDiff006 lv rv (path ++ ".projectionValue") (depth-1)
  | .lam _ ld lb li, .lam _ rd rb ri
  | .forallE _ ld lb li, .forallE _ rd rb ri =>
    if li != ri then nativeEqualityDiffLeaf006 (path ++ ".BINDER_INFO") left right
    nativeEqualityCarrierDiff006 ld rd (path ++ ".binderType") (depth-1)
    nativeEqualityCarrierDiff006 lb rb (path ++ ".binderBody") (depth-1)
  | .letE _ lt lv lb ln, .letE _ rt rv rb rn =>
    if ln != rn then nativeEqualityDiffLeaf006 (path ++ ".LET_FLAG") left right
    nativeEqualityCarrierDiff006 lt rt (path ++ ".letType") (depth-1)
    nativeEqualityCarrierDiff006 lv rv (path ++ ".letValue") (depth-1)
    nativeEqualityCarrierDiff006 lb rb (path ++ ".letBody") (depth-1)
  | _, _ => nativeEqualityDiffLeaf006 path left right

/-- Return only the exact carrier pair already stored in the original
accepted map/coefficient proofs. Keep all eight actual parameters literal. -/
private def nativeEqualityStoredCarriers006 (suppliedMap suppliedCoefficient : Syntax) :
    TermElabM (Expr × Expr) := do
  let mapProof ← originalNativeEqualityNoRecovery005
    (← Term.elabTerm suppliedMap none (catchExPostpone := false))
  let coefficientProof ← originalNativeEqualityNoRecovery005
    (← Term.elabTerm suppliedCoefficient none (catchExPostpone := false))
  unless mapProof.getAppFn.isConstOf ``actualOriginalGlobalNativeEqualityMapPoint004 &&
      coefficientProof.getAppFn.isConstOf ``actualOriginalGlobalNativeEqualityCoefficientOwn005 &&
      mapProof.getAppArgs.size == 8 && coefficientProof.getAppArgs.size == 8 do
    throwError "NativeEquality006 requires exact original MapPoint004/coefficientOwn005 eight-vectors."
  for i in [:8] do
    unless mapProof.getAppArgs[i]!.consumeMData.equal
        coefficientProof.getAppArgs[i]!.consumeMData do
      throwError "NativeEquality006 original eight-vector differs at{i}."
  let p ← originalNativeEqualityHeadLets005 (← inferType mapProof)
  let q ← originalNativeEqualityHeadLets005 (← inferType coefficientProof)
  let some (carrier, _, middle) := p.eq?
    | throwError "NativeEquality006 original map type is not literal Eq3."
  let some (otherCarrier, otherMiddle, _) := q.eq?
    | throwError "NativeEquality006 original coefficient type is not literal Eq3."
  unless middle.consumeMData.equal otherMiddle.consumeMData do
    throwError "NativeEquality006 original middle point changed from1769 raw identity."
  unless p.getAppFn.isConstOf ``Eq && q.getAppFn.isConstOf ``Eq &&
      p.getAppFn.constLevels! == q.getAppFn.constLevels! do
    throwError "NativeEquality006 original Eq universe vectors differ."
  return (carrier, otherCarrier)

elab "native_equality_carrier006% " suppliedMap:term
    " with_coefficient " suppliedCoefficient:term " as " mode:ident : term => do
  let (left, right) ← nativeEqualityStoredCarriers006 suppliedMap suppliedCoefficient
  match mode.getId with
  | `diagnostic =>
    logInfo m!"NativeEquality006 exact carrier heads: LEFT[{nativeEqualityExprHead006 left}]; RIGHT[{nativeEqualityExprHead006 right}]."
    logInfo m!"NativeEquality006 original RAW carrier equality={left.consumeMData.equal right.consumeMData}; original eight-vector and entire middle point RAW unchanged."
    let (_, state) ← (nativeEqualityCarrierDiff006 left right "carrier" 64).run {}
    logInfo m!"NativeEquality006 structural differences={state.leaves}; remaining512-node budget={state.remaining}; stopped={state.stopped}."
    return mkConst ``True.intro
  | `proposition =>
    originalNativeEqualityNoRecovery005 (← mkEq left right)
  | `refl =>
    -- This ordinary Eq.refl has its own inferred type. The declaration's
    -- EXACT left=right annotation must independently kernel-check.
    originalNativeEqualityNoRecovery005 (← mkEqRefl left)
  | _ => throwError "NativeEquality006 unknown diagnostic/proposition/refl mode."

end

private lemma actualOriginalGlobalNativeEqualityCarrierDiagnostic006
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) : True :=
  native_equality_carrier006%
    (actualOriginalGlobalNativeEqualityMapPoint004 p hp P hP s)
    with_coefficient (actualOriginalGlobalNativeEqualityCoefficientOwn005 p hp P hP s) as diagnostic

private lemma actualOriginalGlobalNativeEqualityCarrierEq006
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
  native_equality_carrier006%
    (actualOriginalGlobalNativeEqualityMapPoint004 p hp P hP s)
    with_coefficient (actualOriginalGlobalNativeEqualityCoefficientOwn005 p hp P hP s) as proposition :=
  native_equality_carrier006%
    (actualOriginalGlobalNativeEqualityMapPoint004 p hp P hP s)
    with_coefficient (actualOriginalGlobalNativeEqualityCoefficientOwn005 p hp P hP s) as refl


meta section
open Lean Meta Elab Term

/-- Construct ONLY the coefficient's exact carrier annotation. The carrier
comes literally from MapPoint004 and is anchored to coefficientOwn005 by
ordinary carrierEq006 on the SAME original eight-vector. Proof VALUE is
unchanged; ROOT must check that original proof in this annotation normally.
No Field dictionary body or proof-law structure is expanded/compared. -/
elab "native_equality_exact_coefficient_annotation009% " suppliedMap:term
    " with_coefficient " suppliedCoefficient:term " using_carrier " suppliedCarrier:term : term => do
  let (left, right) ← nativeEqualityStoredCarriers006 suppliedMap suppliedCoefficient
  let mapProof ← originalNativeEqualityNoRecovery005
    (← Term.elabTerm suppliedMap none (catchExPostpone := false))
  let coefficientProof ← originalNativeEqualityNoRecovery005
    (← Term.elabTerm suppliedCoefficient none (catchExPostpone := false))
  let carrierProof ← originalNativeEqualityNoRecovery005
    (← Term.elabTerm suppliedCarrier none (catchExPostpone := false))
  unless carrierProof.getAppFn.isConstOf ``actualOriginalGlobalNativeEqualityCarrierEq006 &&
      carrierProof.getAppArgs.size == 8 do
    throwError "NativeEquality009 requires original ordinary carrierEq006 eight-vector."
  for i in [:8] do
    unless carrierProof.getAppArgs[i]!.consumeMData.equal mapProof.getAppArgs[i]!.consumeMData do
      throwError "NativeEquality009 carrier proof changed original geometric/scalar/section vector at{i}."
  let carrierProp ← originalNativeEqualityHeadLets005 (← inferType carrierProof)
  let some (_, certLeft, certRight) := carrierProp.eq?
    | throwError "NativeEquality009 ordinary carrier certificate lost its Eq3."
  unless certLeft.consumeMData.equal left.consumeMData &&
      certRight.consumeMData.equal right.consumeMData do
    throwError "NativeEquality009 ordinary carrier certificate changed WHOLE actual endpoints."
  let p ← originalNativeEqualityHeadLets005 (← inferType mapProof)
  let q ← originalNativeEqualityHeadLets005 (← inferType coefficientProof)
  let some (mapCarrier, _, middle) := p.eq?
    | throwError "NativeEquality009 original map proof lost its literal Eq3."
  let some (coefficientCarrier, coefficientMiddle, last) := q.eq?
    | throwError "NativeEquality009 original coefficient proof lost its literal Eq3."
  unless mapCarrier.consumeMData.equal left.consumeMData &&
      coefficientCarrier.consumeMData.equal right.consumeMData &&
      middle.consumeMData.equal coefficientMiddle.consumeMData do
    throwError "NativeEquality009 original carrier pair or RAW middle point changed."
  unless p.getAppFn.isConstOf ``Eq && q.getAppFn.isConstOf ``Eq &&
      p.getAppFn.constLevels! == q.getAppFn.constLevels! &&
      left.getAppFn.isConstOf ``TensorProduct && right.getAppFn.isConstOf ``TensorProduct &&
      left.getAppArgs.size == 8 && right.getAppArgs.size == 8 do
    throwError "NativeEquality009 exact original Eq universes/TensorProduct8 carriers changed."
  --Select the ACTUAL stored map carrier; retain both coefficient endpoints
  --literally. This syntax selection proves nothing by itself. The declaration
  --VALUE below is the original coefficient proof, checked by ordinary kernel.
  let result := mkAppN q.getAppFn #[mapCarrier, coefficientMiddle, last]
  let resultArgs := result.getAppArgs
  unless resultArgs.size == 3 && resultArgs[0]!.equal p.getAppArgs[0]! &&
      resultArgs[1]!.equal q.getAppArgs[1]! && resultArgs[2]!.equal q.getAppArgs[2]! do
    throwError "NativeEquality009 exact carrier annotation changed original WHOLE endpoints."
  logInfo "NativeEquality009 exact coefficient annotation: original8/middle/last unchanged, literal MapPoint004 carrier, SAME whole ordinary carrierEq006 pair; original coefficient VALUE must ordinary-kernel-check. No Field-body proof-law syntax check."
  return result

end

private lemma actualOriginalGlobalNativeEqualityCoefficientAnnotated009
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
  native_equality_exact_coefficient_annotation009%
    (actualOriginalGlobalNativeEqualityMapPoint004 p hp P hP s)
    with_coefficient (actualOriginalGlobalNativeEqualityCoefficientOwn005 p hp P hP s)
    using_carrier (actualOriginalGlobalNativeEqualityCarrierEq006 p hp P hP s) :=
  actualOriginalGlobalNativeEqualityCoefficientOwn005 p hp P hP s

meta section
open Lean Meta Elab Term

/-- Join the exact original stored Eq vectors using ordinary Eq.trans.
The callback is syntax construction; ROOT must check the declaration normally. -/
elab "native_equality_stored_join009% " suppliedMap:term
    " with_coefficient " suppliedCoefficient:term : term => do
  let mapProof ← originalNativeEqualityNoRecovery005
    (← Term.elabTerm suppliedMap none (catchExPostpone := false))
  let coefficientProof ← originalNativeEqualityNoRecovery005
    (← Term.elabTerm suppliedCoefficient none (catchExPostpone := false))
  unless mapProof.getAppFn.isConstOf ``actualOriginalGlobalNativeEqualityMapPoint004 &&
      coefficientProof.getAppFn.isConstOf ``actualOriginalGlobalNativeEqualityCoefficientAnnotated009 &&
      mapProof.getAppArgs.size == 8 && coefficientProof.getAppArgs.size == 8 do
    throwError "NativeEquality009 requires ONLY original MapPoint004/coefficientAnnotated009 eight-vectors."
  for i in [:8] do
    unless mapProof.getAppArgs[i]!.consumeMData.equal
        coefficientProof.getAppArgs[i]!.consumeMData do
      throwError "NativeEquality009 original geometric/scalar/section vector differs at{i}."
  let p ← originalNativeEqualityHeadLets005 (← inferType mapProof)
  let q ← originalNativeEqualityHeadLets005 (← inferType coefficientProof)
  let some (carrier, first, middle) := p.eq?
    | throwError "NativeEquality009 original MapPoint004 type is not literal Eq3."
  let some (otherCarrier, otherMiddle, last) := q.eq?
    | throwError "NativeEquality009 original coefficient type is not literal Eq3."
  let carrierRaw := carrier.consumeMData.equal otherCarrier.consumeMData
  let middleRaw := middle.consumeMData.equal otherMiddle.consumeMData
  logInfo m!"NativeEquality009 stored Eq join RAW carrier={carrierRaw}, middle={middleRaw}."
  unless carrierRaw && middleRaw do
    throwError "NativeEquality009 refuses a conversion across different literal carriers/middle endpoints."
  let levels := p.getAppFn.constLevels!
  unless p.getAppFn.isConstOf ``Eq && q.getAppFn.isConstOf ``Eq &&
      levels.length == 1 && q.getAppFn.constLevels! == levels do
    throwError "NativeEquality009 original Eq universe vectors differ."
  let arguments := #[carrier, first, middle, last, mapProof, coefficientProof]
  let expectedDomains := #[mkSort levels[0]!, carrier, carrier, carrier, p, q]
  let info ← getConstInfo ``Eq.trans
  unless info.levelParams.length == levels.length do
    throwError "NativeEquality009 installed Eq.trans universe count differs."
  let mut lawType := info.instantiateTypeLevelParams levels
  for i in [:6] do
    let .forallE _ domain body _ := lawType.consumeMData
      | throwError "NativeEquality009 ordinary Eq.trans prefix ended at{i}."
    unless domain.consumeMData.equal expectedDomains[i]!.consumeMData do
      throwError "NativeEquality009 exact ordinary Eq.trans binder differs at{i}."
    lawType := body.instantiate1 arguments[i]!
  let result ← originalNativeEqualityNoRecovery005
    (mkAppN (mkConst ``Eq.trans levels) arguments)
  let resultType ← originalNativeEqualityNoRecovery005 (← inferType result)
  let expected := mkAppN (mkConst ``Eq levels) #[carrier, first, last]
  unless resultType.consumeMData.equal expected.consumeMData &&
      resultType.consumeMData.equal lawType.consumeMData do
    throwError "NativeEquality009 ordinary transitivity changed original WHOLE Eq endpoints/type."
  logInfo "NativeEquality009 exact stored six-vector Eq.trans: all original8 arguments and whole endpoints preserved."
  return result

end

private def actualOriginalGlobalNativeEqualityJoinedOwn009
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :=
  native_equality_stored_join009%
    (actualOriginalGlobalNativeEqualityMapPoint004 p hp P hP s)
    with_coefficient (actualOriginalGlobalNativeEqualityCoefficientAnnotated009 p hp P hP s)

lemma actualOriginalGlobalNativeEqualityGlobalPoint010
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
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
    let E := actualCubicPositiveTwoOriginalNativePointFiberEquiv p hp
      ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization
    let d : TensorProduct R L (KaehlerDifferential K R) :=
      actualResidueDifferentialDerivation (K := K) (R := R) (L := L)
        (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s)
    E (actualOriginalGlobalCanonicalQuadraticPhi p hp P s) = d :=
  actualOriginalGlobalNativeEqualityJoinedOwn009 p hp P hP s

lemma actualOriginalGlobalNativeEqualityNativePoint003
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
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
    let E := actualCubicPositiveTwoOriginalNativePointFiberEquiv p hp
      ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization
    let d : TensorProduct R L (KaehlerDifferential K R) :=
      actualResidueDifferentialDerivation (K := K) (R := R) (L := L)
        (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s)
    E (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s) = d := by
  intro C R L E d
  exact actualOriginalIdealQuadraticPositiveTwoPhi_native_coefficient p hp P hP s

universe vNativeEquality003 wNativeEquality003
theorem nativeEqualityInjectiveJoin003 {A : Sort vNativeEquality003}
    {B : Sort wNativeEquality003} (e : A → B) (hinj : Function.Injective e)
    (x y : A) (d : B) (hx : e x = d) (hy : e y = d) : x = y :=
  hinj (hx.trans hy.symm)


end PfaffianDescent
