import PfaffianDescent.ActualOriginalGlobalCanonicalQuadraticPhiNativeEqualityPrefix010

/- SOURCE ONLY / UNCHECKED downstream011. Prefix source/olean acceptance
is ROOT-owned; no original coefficient/map proof is duplicated in this file. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

meta section
open Lean Meta Elab Term

private structure NativeEqualityStoredPoint011 where
  proof : Expr
  proposition : Expr
  carrier : Expr
  mappedPoint : Expr
  commonPoint : Expr
  domain : Expr
  function : Expr
  equivalence : Expr
  point : Expr

/-- Read the actual E/coercion/domain/point/d from the original stored
ordinary equation. No E/category/map/scalar/endpoint is rebuilt or unfolded. -/
private def nativeEqualityStoredPoint011 (supplied : Syntax) (expected : Name) :
    TermElabM NativeEqualityStoredPoint011 := do
  let proof ← originalNativeEqualityNoRecovery005
    (← Term.elabTerm supplied none (catchExPostpone := false))
  unless proof.getAppFn.isConstOf expected && proof.getAppArgs.size == 8 do
    throwError "NativeEquality011 requires exact original point proof/eight-vector."
  let proposition ← originalNativeEqualityHeadLets005 (← inferType proof)
  let some (carrier, mappedPoint, commonPoint) := proposition.eq?
    | throwError "NativeEquality011 original point proof is not literal Eq3."
  let mappedPoint := mappedPoint.consumeMData
  let a := mappedPoint.getAppArgs
  unless mappedPoint.getAppFn.isConstOf ``DFunLike.coe && a.size == 6 &&
      a[4]!.consumeMData.getAppFn.isConstOf ``actualCubicPositiveTwoOriginalNativePointFiberEquiv do
    throwError "NativeEquality011 original mapped point lost its SAME actual native E/coercion."
  let function := mkAppN mappedPoint.getAppFn (a.extract 0 5)
  return ⟨proof, proposition, carrier, mappedPoint, commonPoint,
    a[1]!, function, a[4]!, a[5]!⟩

/-- Infer the installed E.injective application in its OWN type; separately
build the exact Injective TYPE of the stored equation's SAME actual function. -/
elab "native_equality_stored_injective011% " suppliedGlobal:term
    " as " mode:ident : term => do
  let g ← nativeEqualityStoredPoint011 suppliedGlobal
    ``actualOriginalGlobalNativeEqualityGlobalPoint010
  match mode.getId with
  | `proof =>
    let result ← originalNativeEqualityNoRecovery005
      (← mkAppM ``LinearEquiv.injective #[g.equivalence])
    unless result.getAppFn.isConstOf ``LinearEquiv.injective &&
        !result.getAppArgs.isEmpty &&
        result.getAppArgs.back!.consumeMData.equal g.equivalence.consumeMData do
      throwError "NativeEquality011 injectivity law changed the SAME original E."
    logInfo "NativeEquality011 ordinary installed LinearEquiv.injective on the original stored E; inferred law TYPE kept, no local-let reconstruction."
    return result
  | `proposition =>
    let levels := [← getLevel g.domain, ← getLevel g.carrier]
    let info ← getConstInfo ``Function.Injective
    unless info.levelParams.length == 2 do
      throwError "NativeEquality011 installed Function.Injective universe shape changed."
    let result := mkAppN (mkConst ``Function.Injective levels)
      #[g.domain, g.carrier, g.function]
    logInfo "NativeEquality011 exact Injective annotation on original stored domain/carrier/function; ordinary law proof must kernel-check in this TYPE."
    return result
  | _ => throwError "NativeEquality011 unknown proof/proposition mode."

end

private def actualOriginalGlobalNativeEqualityInjectiveOwn011
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :=
  native_equality_stored_injective011%
    (actualOriginalGlobalNativeEqualityGlobalPoint010 p hp P hP s) as proof

private lemma actualOriginalGlobalNativeEqualityInjectiveAnnotated011
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
  native_equality_stored_injective011%
    (actualOriginalGlobalNativeEqualityGlobalPoint010 p hp P hP s) as proposition :=
  actualOriginalGlobalNativeEqualityInjectiveOwn011 p hp P hP s

meta section
open Lean Meta Elab Term

/-- Consume the actual stored E x=d / E y=d and SAME E injectivity.
Only ordinary generic cancellation is specialized; every entire actual
vector/function/domain/carrier/common point/proof TYPE must RAW join. -/
elab "native_equality_stored_cancel011% " suppliedGlobal:term
    " with_native " suppliedNative:term " using_injective " suppliedInjective:term : term => do
  let g ← nativeEqualityStoredPoint011 suppliedGlobal
    ``actualOriginalGlobalNativeEqualityGlobalPoint010
  let n ← nativeEqualityStoredPoint011 suppliedNative
    ``actualOriginalGlobalNativeEqualityNativePoint003
  let hinj ← originalNativeEqualityNoRecovery005
    (← Term.elabTerm suppliedInjective none (catchExPostpone := false))
  unless hinj.getAppFn.isConstOf ``actualOriginalGlobalNativeEqualityInjectiveAnnotated011 &&
      hinj.getAppArgs.size == 8 do
    throwError "NativeEquality011 requires original stored annotated injectivity/eight-vector."
  for i in [:8] do
    unless g.proof.getAppArgs[i]!.consumeMData.equal n.proof.getAppArgs[i]!.consumeMData &&
        g.proof.getAppArgs[i]!.consumeMData.equal hinj.getAppArgs[i]!.consumeMData do
      throwError "NativeEquality011 cancellation changed original geometric/scalar/section vector at{i}."
  let domainRaw := g.domain.consumeMData.equal n.domain.consumeMData
  let carrierRaw := g.carrier.consumeMData.equal n.carrier.consumeMData
  let functionRaw := g.function.consumeMData.equal n.function.consumeMData
  let equivalenceRaw := g.equivalence.consumeMData.equal n.equivalence.consumeMData
  let commonPointRaw := g.commonPoint.consumeMData.equal n.commonPoint.consumeMData
  logInfo m!"NativeEquality011 stored cancellation RAW domain={domainRaw}, carrier={carrierRaw}, function={functionRaw}, SAME E={equivalenceRaw}, original d={commonPointRaw}."
  unless domainRaw && carrierRaw && functionRaw && equivalenceRaw && commonPointRaw do
    throwError "NativeEquality011 refuses cancellation across nonidentical original endpoints/function."
  let levels := [← getLevel g.domain, ← getLevel g.carrier]
  let injectiveType := mkAppN (mkConst ``Function.Injective levels)
    #[g.domain, g.carrier, g.function]
  let actualInjectiveType ← originalNativeEqualityHeadLets005 (← inferType hinj)
  unless actualInjectiveType.consumeMData.equal injectiveType.consumeMData do
    throwError "NativeEquality011 original injective proposition did not RAW join stored function TYPE."
  let info ← getConstInfo ``nativeEqualityInjectiveJoin003
  unless info.levelParams.length == 2 do
    throwError "NativeEquality011 original generic cancellation universe shape changed."
  let arguments := #[g.domain, g.carrier, g.function, hinj,
    g.point, n.point, g.commonPoint, g.proof, n.proof]
  let expectedDomains := #[mkSort levels[0]!, mkSort levels[1]!,
    (← mkArrow g.domain g.carrier), injectiveType,
    g.domain, g.domain, g.carrier, g.proposition, n.proposition]
  let mut lawType := info.instantiateTypeLevelParams levels
  for i in [:9] do
    let .forallE _ domain body _ := lawType.consumeMData
      | throwError "NativeEquality011 ordinary cancellation prefix ended at{i}."
    -- CoreM.mkArrow introduces a fresh binder NAME. Ignore only that outer
    -- name for A → B; preserve its annotation and RAW domain/codomain.
    -- All other eight expected argument domains still compare wholly RAW.
    let domainMatches := if i == 2 then
      match domain.consumeMData, expectedDomains[i]!.consumeMData with
      | .forallE _ actualDomain actualBody actualBinder,
        .forallE _ expectedDomain expectedBody expectedBinder =>
          actualBinder == expectedBinder &&
          actualDomain.consumeMData.equal expectedDomain.consumeMData &&
          actualBody.consumeMData.equal expectedBody.consumeMData
      | _, _ => false
    else domain.consumeMData.equal expectedDomains[i]!.consumeMData
    unless domainMatches do
      throwError "NativeEquality011 exact ordinary cancellation binder differs at{i}."
    lawType := body.instantiate1 arguments[i]!
  let result ← originalNativeEqualityNoRecovery005
    (mkAppN (mkConst ``nativeEqualityInjectiveJoin003 levels) arguments)
  let resultType ← originalNativeEqualityNoRecovery005 (← inferType result)
  -- Use the original function's stored domain, as in the specialized
  -- ordinary theorem. mkEq would independently infer the left point's
  -- TYPE and can rebuild a different definitional carrier alias.
  let expected := mkAppN (mkConst ``Eq [levels[0]!])
    #[g.domain, g.point, n.point]
  let resultRaw := resultType.consumeMData.equal expected.consumeMData
  let lawRaw := resultType.consumeMData.equal lawType.consumeMData
  let some (resultDomain, resultLeft, resultRight) := resultType.eq?
    | throwError "NativeEquality011 ordinary cancellation result is not literal Eq3."
  let resultDomainRaw := resultDomain.consumeMData.equal g.domain.consumeMData
  let resultLeftRaw := resultLeft.consumeMData.equal g.point.consumeMData
  let resultRightRaw := resultRight.consumeMData.equal n.point.consumeMData
  logInfo m!"NativeEquality011 cancellation result RAW whole={resultRaw}, instantiated law={lawRaw}, stored domain={resultDomainRaw}, original left={resultLeftRaw}, original right={resultRightRaw}."
  unless resultRaw && lawRaw && resultDomainRaw && resultLeftRaw && resultRightRaw do
    throwError "NativeEquality011 ordinary cancellation changed WHOLE original map/point equality."
  logInfo "NativeEquality011 exact ordinary nine-vector injective cancellation on original stored E/globalPhi/nativePhi/d; no local-let/tactic proof assembly."
  return result

end

private def actualOriginalGlobalNativeEqualityPointCancellationOwn011
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :=
  native_equality_stored_cancel011%
    (actualOriginalGlobalNativeEqualityGlobalPoint010 p hp P hP s)
    with_native (actualOriginalGlobalNativeEqualityNativePoint003 p hp P hP s)
    using_injective (actualOriginalGlobalNativeEqualityInjectiveAnnotated011 p hp P hP s)

private lemma actualOriginalGlobalNativeEqualityPointAssembly011
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    actualOriginalGlobalCanonicalQuadraticPhi p hp P s =
      actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s :=
  actualOriginalGlobalNativeEqualityPointCancellationOwn011 p hp P hP s

lemma actualOriginalGlobalCanonicalQuadraticPhi_eq_native
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    actualOriginalGlobalCanonicalQuadraticPhi p hp P s =
      actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s := by
  exact actualOriginalGlobalNativeEqualityPointAssembly011 p hp P hP s

lemma actualOriginalGlobalCanonicalQuadraticPhi_eq_native_linearMap
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let E2 := (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (actualCubicPositiveTwoDifferentials p hp))
    letI : Module K E2 := Module.compHom E2 (algebraMap K L)
    actualOriginalGlobalCanonicalQuadraticPhiLinearMap p hp P =
      actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP := by
  intro L E2
  apply DFunLike.ext
  intro s
  change actualOriginalGlobalCanonicalQuadraticPhi p hp P s =
    actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s
  exact actualOriginalGlobalCanonicalQuadraticPhi_eq_native p hp P hP s

end PfaffianDescent
