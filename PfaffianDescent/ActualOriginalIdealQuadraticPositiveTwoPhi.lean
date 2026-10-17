import Mathlib.Lean.Meta.Simp
import PfaffianDescent.ActualOriginalIdealChartTransportEquality
import PfaffianDescent.ActualOriginalIdealQuadraticNativeRestriction
import PfaffianDescent.ActualQuadraticDifferentialRestrictionKernel
import PfaffianDescent.ActualCubicPositiveTwoNativePointFiber

/- SOURCE ONLY / UNVERIFIED. Genuine original H0(I_P(2)) maps to genuine
original Omega(2) fiber using the internally selected ACTUAL native chart.
The native O(2) generator is used, not an unrelated fiber identification.
Across-different-chart independence is a separate pending theorem. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Chosen-native-chart realization of the manuscript's conormal quadratic
map. This name does not claim unproved independence of the chosen chart. -/
def actualOriginalIdealQuadraticPositiveTwoPhi
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
    ActualOriginalPointIdealQuadraticSections p hp P →ₗ[K] E2 := by
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let R := ChartRing (equationIdeal p hp) C.index
  letI aK : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  letI : SMul K R := aK.toSMul
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun C.base c).symm)
  let E2 := (moduleSpecΓFunctor (R := .of L)).obj
    ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
      (actualCubicPositiveTwoDifferentials p hp))
  letI : Module K E2 := Module.compHom E2 (algebraMap K L)
  letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
  let F := TensorProduct R L (KaehlerDifferential K R)
  letI : Module K F := TensorProduct.leftModule
  letI : IsScalarTower K L F := TensorProduct.isScalarTower_left
  let E : E2 ≃ₗ[L] F := actualCubicPositiveTwoOriginalNativePointFiberEquiv p hp
    ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization
  exact (E.symm.toLinearMap.restrictScalars K).comp
    (actualQuadraticDifferentialRestriction
      (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP))

meta section
open Lean Meta Elab

/-- Build the existing ordinary inverse law without a public native expected type. -/
syntax "ideal_phi_inverse008% " "(" term "," term ")" : term
elab_rules : term
  | `(ideal_phi_inverse008% ($suppliedE, $suppliedD)) => do
    logInfo "IdealPhiInverse008.00:beforeE"
    let e ← Term.elabTerm suppliedE none (catchExPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    logInfo "IdealPhiInverse008.01:afterE_beforeD"
    let d ← Term.elabTerm suppliedD none (catchExPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    let d ← instantiateMVars d
    logInfo "IdealPhiInverse008.02:afterD_beforeLaw"
    let proof ← mkAppM ``LinearEquiv.apply_symm_apply #[e, d]
    logInfo "IdealPhiInverse008.03:afterLaw"
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "IdealPhiInverse008 unresolved/recovery ordinary inverse-law proof."
    logInfo "IdealPhiInverse008.04:resolvedOrdinaryLaw"
    return proof

end

/-- Diagnostic: kernel-check only the inferred native proposition, without storing its proof. -/
private def actualOriginalIdealQuadraticPositiveTwoPhi_inverse_proposition008
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) : Prop :=
  type_of% (
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let R := ChartRing (equationIdeal p hp) C.index
    letI aK : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let E2 := (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (actualCubicPositiveTwoDifferentials p hp))
    letI : Module K E2 := Module.compHom E2 (algebraMap K L)
    letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
    let F := TensorProduct R L (KaehlerDifferential K R)
    letI : Module K F := TensorProduct.leftModule
    letI : IsScalarTower K L F := TensorProduct.isScalarTower_left
    let E : E2 ≃ₗ[L] F := actualCubicPositiveTwoOriginalNativePointFiberEquiv p hp
      ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization
    let d : F := actualResidueDifferentialDerivation (K := K) (R := R) (L := L)
      (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s)
    ideal_phi_inverse008% (E, d)
  )

meta section
open Lean Meta Elab Tactic

/-- Apply the existing inverse law to the exact E/d stored in the checked proposition. -/
elab "ideal_phi_stored_proposition012" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let target ← whnf target
  let some (_, left, right) := target.consumeMData.headBeta.eq?
    | throwError "IdealPhiStored012 expected the checked inverse proposition's equality."
  let left := left.consumeMData
  let la := left.getAppArgs
  unless left.getAppFn.isConstOf ``DFunLike.coe && la.size == 6 do
    throwError "IdealPhiStored012 expected the actual stored outer equivalence application."
  let e := la[4]!
  let inner := la[5]!.consumeMData
  let ia := inner.getAppArgs
  unless inner.getAppFn.isConstOf ``DFunLike.coe && ia.size == 6 do
    throwError "IdealPhiStored012 expected the actual stored inner equivalence application."
  let inverse := ia[4]!.consumeMData
  let sa := inverse.getAppArgs
  unless inverse.getAppFn.isConstOf ``LinearEquiv.symm && sa.size == 15 do
    throwError "IdealPhiStored012 expected the actual stored LinearEquiv.symm vector."
  unless sa[14]!.consumeMData.equal e.consumeMData &&
      ia[5]!.consumeMData.equal right.consumeMData do
    throwError "IdealPhiStored012 refused different stored equivalences or native values."
  logInfo "IdealPhiStored012 checked identical stored E and d without rebuilding the native telescope."
  let .const _ levels := inverse.getAppFn
    | throwError "IdealPhiStored012 expected a constant symm head with stored universe levels."
  let symmInfo ← getConstInfo ``LinearEquiv.symm
  let lawInfo ← getConstInfo ``LinearEquiv.apply_symm_apply
  unless symmInfo.levelParams == lawInfo.levelParams do
    throwError "IdealPhiStored012 refused different symm/law universe parameter vectors."
  let mut symmType := symmInfo.type
  let mut lawType := lawInfo.type
  for i in [:15] do
    let .forallE _ symmDomain symmBody symmBinder := symmType
      | throwError "IdealPhiStored012 missing symm prefix binder."
    let .forallE _ lawDomain lawBody lawBinder := lawType
      | throwError "IdealPhiStored012 missing law prefix binder."
    unless symmDomain.equal lawDomain && symmBinder == lawBinder do
      throwError "IdealPhiStored012 refused a different stored prefix binder at {i}."
    symmType := symmBody
    lawType := lawBody
  let .forallE _ _ _ _ := lawType
    | throwError "IdealPhiStored012 expected the native value after the checked prefix."
  logInfo "IdealPhiStored012 checked exact declaration prefix types and universe order."
  let proof := mkAppN (mkConst ``LinearEquiv.apply_symm_apply levels) (sa.push right)
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "IdealPhiStored012 unresolved/recovery ordinary inverse-law application."
  logInfo "IdealPhiStored012 emitted the existing ordinary law from the complete stored symm15 vector without inference."
  goal.assign proof
  replaceMainGoal []

end

/-- Ordinary opaque proof of the independently checked native inverse proposition. -/
private theorem actualOriginalIdealQuadraticPositiveTwoPhi_stored_inverse012
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    actualOriginalIdealQuadraticPositiveTwoPhi_inverse_proposition008 p hp P hP s := by
  ideal_phi_stored_proposition012

/-- The exact original public coefficient proposition, without a proof claim. -/
private def actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) : Prop :=
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let R := ChartRing (equationIdeal p hp) C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    actualCubicPositiveTwoOriginalNativePointFiberEquiv p hp
      ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization
        (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s) =
      actualResidueDifferentialDerivation (K := K) (R := R) (L := L)
        (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s)

meta section
open Lean Meta Elab Tactic

/-- Read exact endpoint vectors after only the already used named simplifications. -/
private def idealPhiEndpointVectors016 (supplied : Syntax) : Term.TermElabM (Array Expr × Expr) := do
  let original ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let original ← instantiateMVars original
  let original ← whnf original
  let mut simpTheorems ← simpTheoremsOfNames [] true
  for declName in
      [``actualOriginalIdealQuadraticPositiveTwoPhi,
        ``actualQuadraticDifferentialRestriction, ``LinearMap.comp_apply,
        ``LinearMap.restrictScalars_apply, ``LinearEquiv.coe_coe,
        ``Derivation.coeFn_coe] do
    if (← isProp (← getConstInfo declName).type) then
      simpTheorems ← simpTheorems.addConst declName
    else
      simpTheorems ← simpTheorems.addDeclToUnfold declName
  let simpContext ← Simp.mkContext
    (simpTheorems := #[simpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let (result, _) ← simp original simpContext
  let target := result.expr.consumeMData.headBeta
  let some (publicCarrier, publicLeft, publicRight) := target.eq?
    | throwError "IdealPhiEndpoints016 expected the literal original coefficient equality."
  let pa := publicLeft.consumeMData.getAppArgs
  unless publicLeft.consumeMData.getAppFn.isConstOf ``DFunLike.coe && pa.size == 6 do
    throwError "IdealPhiEndpoints016 expected the actual outer native equivalence evaluation."
  let inner := pa[5]!.consumeMData
  let ia := inner.getAppArgs
  unless inner.getAppFn.isConstOf ``DFunLike.coe && ia.size == 6 do
    throwError "IdealPhiEndpoints016 expected the actual inner native inverse evaluation."
  let inverse := ia[4]!.consumeMData
  let sa := inverse.getAppArgs
  let .const inverseName levels := inverse.getAppFn
    | throwError "IdealPhiEndpoints016 expected a stored constant inverse head."
  unless inverseName == ``LinearEquiv.symm && sa.size == 15 do
    throwError "IdealPhiEndpoints016 expected the complete stored symm15 vector."
  let symmInfo ← getConstInfo ``LinearEquiv.symm
  let lawInfo ← getConstInfo ``LinearEquiv.apply_symm_apply
  unless symmInfo.levelParams == lawInfo.levelParams do
    throwError "IdealPhiEndpoints016 refused a different law/symm universe order."
  let mut symmType := symmInfo.type
  let mut lawType := lawInfo.type
  for i in [:15] do
    let .forallE _ sd sb si := symmType
      | throwError "IdealPhiEndpoints016 missing symm prefix binder."
    let .forallE _ ld lb li := lawType
      | throwError "IdealPhiEndpoints016 missing law prefix binder."
    unless sd.equal ld && si == li do
      throwError "IdealPhiEndpoints016 refused a different law prefix at {i}."
    symmType := sb
    lawType := lb
  let .forallE _ _ _ _ := lawType
    | throwError "IdealPhiEndpoints016 expected a native value after the checked law prefix."
  let proof := mkAppN (mkConst ``LinearEquiv.apply_symm_apply levels) (sa.push ia[5]!)
  let nativeLawType ← instantiateMVars (← inferType proof)
  let some (lawCarrier, lawLeft, lawRight) := nativeLawType.consumeMData.headBeta.eq?
    | throwError "IdealPhiEndpoints016 expected the ordinary inner inverse law's equality."
  let la := lawLeft.consumeMData.getAppArgs
  unless lawLeft.consumeMData.getAppFn.isConstOf ``DFunLike.coe && la.size == 6 do
    throwError "IdealPhiEndpoints016 expected the exact law outer evaluation vector."
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "IdealPhiEndpoints016 unresolved/recovery stored law."
  -- Pairs0–3: carrier, exact E, native value, whole evaluated left endpoint.
  -- Pairs4–8: five outer coefficient vector arguments; argument5 is raw-identical.
  unless pa[5]!.consumeMData.equal la[5]!.consumeMData do
    throwError "IdealPhiEndpoints016 refused a different stored inverse application argument."
  logInfo "IdealPhiEndpoints016 extracted the exact original public and inner-law vectors; no conversion proof assumed."
  return (#[publicCarrier, lawCarrier, pa[4]!, sa[14]!, publicRight, lawRight,
    publicLeft, lawLeft, pa[0]!, la[0]!, pa[1]!, la[1]!, pa[2]!, la[2]!,
    pa[3]!, la[3]!, pa[4]!, la[4]!], proof)

elab "ideal_phi_endpoint_certificate016% " index:num supplied:term : term => do
  let (values, _) ← idealPhiEndpointVectors016 supplied
  let i := index.getNat
  unless i < 9 do throwError "IdealPhiEndpoints016 certificate index out of range."
  if i == 0 then
    return (← mkEq values[0]! values[1]!)
  else
    return (← mkHEq values[2*i]! values[2*i+1]!)

elab "ideal_phi_inner_law016% " supplied:term : term => do
  return (← idealPhiEndpointVectors016 supplied).2

/-- Use only the existing bounded structural certificate checker, from reflexivity. -/
elab "ideal_phi_endpoint_certificate016" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
  let source ← match target.eq?, target.heq? with
    | some (_, left, _), _ => mkEqRefl left
    | _, some (_, left, _, _) => mkHEqRefl left
    | _, _ => throwError "IdealPhiEndpoints016 expected a stored carrier equality or endpoint HEq."
  let supplied ← Term.exprToSyntax source
  evalTactic (← `(tactic| basis_chart_exact009 $supplied))

end

/-- The two semiring projections of the SAME explicit semifield. -/
private theorem idealPhiSemifieldSemiringProjection021
    {K : Type u} (f : Semifield K) :
    @DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K f) =
    @CommSemiring.toSemiring K (@Semifield.toCommSemiring K f) := by
  rfl

meta section
open Lean Meta Elab Tactic

private def idealPhiSemiringHead021 (e : Expr) : String :=
  match e.consumeMData.getAppFn with
  | .const n _ => toString n
  | .fvar id => s!"fvar:{id.name}"
  | _ => "nonconstant"

/-- Read only the actual failed native-value argument path, without normalizing it. -/
private def idealPhiStoredSemiringPair021 (supplied : Syntax) : Term.TermElabM (Expr × Expr) := do
  let (values, _) ← idealPhiEndpointVectors016 supplied
  let mut left := values[4]!.consumeMData
  let mut right := values[5]!.consumeMData
  for (i, arity, headName) in
      #[(5, 6, ``DFunLike.coe), (0, 6, ``DFunLike.coe), (3, 11, ``LinearMap)] do
    let la := left.getAppArgs
    let ra := right.getAppArgs
    unless left.getAppFn.isConstOf headName && right.getAppFn.isConstOf headName &&
        la.size == arity && ra.size == arity do
      throwError "IdealPhiSemiring021 unexpected stored path head/arity at argument {i}."
    left := la[i]!.consumeMData
    right := ra[i]!.consumeMData
  return (left, right)

/-- Emit an ordinary law only after checking the exact stored projection vectors. -/
private def idealPhiStoredSemiringProof021 (left right : Expr) : MetaM Expr := do
  let left := left.consumeMData
  let right := right.consumeMData
  let la := left.getAppArgs
  let ra := right.getAppArgs
  let .const ln ll := left.getAppFn
    | throwError "IdealPhiSemiring021 expected a constant left projection."
  let .const rn rl := right.getAppFn
    | throwError "IdealPhiSemiring021 expected a constant right projection."
  logInfo m!"IdealPhiSemiring021 stored outer heads={ln}/{rn}; arities={la.size}/{ra.size}."
  unless ln == ``DivisionSemiring.toSemiring && rn == ``CommSemiring.toSemiring &&
      la.size == 2 && ra.size == 2 && ll == rl do
    throwError "IdealPhiSemiring021 refused different outer projection vectors."
  let ls := la[1]!.consumeMData
  let rs := ra[1]!.consumeMData
  let lsa := ls.getAppArgs
  let rsa := rs.getAppArgs
  logInfo m!"IdealPhiSemiring021 stored parent heads={idealPhiSemiringHead021 ls}/{idealPhiSemiringHead021 rs}; arities={lsa.size}/{rsa.size}."
  unless ls.getAppFn.isConstOf ``Semifield.toDivisionSemiring &&
      rs.getAppFn.isConstOf ``Semifield.toCommSemiring &&
      lsa.size == 2 && rsa.size == 2 do
    throwError "IdealPhiSemiring021 refused different semifield projection parents."
  logInfo m!"IdealPhiSemiring021 raw K match={la[0]!.equal ra[0]!}; parent K matches={lsa[0]!.equal la[0]!}/{rsa[0]!.equal ra[0]!}; same semifield={lsa[1]!.equal rsa[1]!}; semifield head={idealPhiSemiringHead021 lsa[1]!}; arguments={lsa[1]!.getAppArgs.size}."
  unless la[0]!.equal ra[0]! && lsa[0]!.equal la[0]! &&
      rsa[0]!.equal ra[0]! && lsa[1]!.equal rsa[1]! do
    throwError "IdealPhiSemiring021 refused different stored carriers or semifield values."
  let proof := mkAppN (mkConst ``idealPhiSemifieldSemiringProjection021 ll)
    #[la[0]!, lsa[1]!]
  let some (_, pl, pr) := (← inferType proof).consumeMData.headBeta.eq?
    | throwError "IdealPhiSemiring021 ordinary law did not infer equality."
  logInfo m!"IdealPhiSemiring021 ordinary proof endpoints raw-match={pl.equal left}/{pr.equal right}."
  unless pl.equal left && pr.equal right do
    throwError "IdealPhiSemiring021 refused a law with different stored endpoints."
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "IdealPhiSemiring021 unresolved/recovery ordinary law."
  return proof

elab "ideal_phi_stored_semiring021% " supplied:term : term => do
  let (left, right) ← idealPhiStoredSemiringPair021 supplied
  discard <| idealPhiStoredSemiringProof021 left right
  return (← mkEq left right)

elab "ideal_phi_stored_semiring021" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, left, right) := (← instantiateMVars (← goal.getType)).consumeMData.headBeta.eq?
    | throwError "IdealPhiSemiring021 expected the exact stored semiring equality."
  let proof ← idealPhiStoredSemiringProof021 left right
  logInfo "IdealPhiSemiring021 emitted ordinary exact stored projection certificate."
  goal.assign proof
  replaceMainGoal []

end

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_stored_semiring021
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_stored_semiring021%
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  ideal_phi_stored_semiring021


noncomputable section
/-- SAME stalk residue field, retaining the actual local-ring proof explicitly. -/
private theorem idealPhiRawNativeCommRingHEq026
    (S : Scheme.{u}) (x : S) (h : IsLocalRing (S.presheaf.stalk x)) :
    HEq
      (@Field.toCommRing
        (@IsLocalRing.ResidueField (CommRingCat.carrier (S.presheaf.stalk x))
          (@CommRingCat.instCommRingObjForgetRingHomCarrier (S.presheaf.stalk x)) h)
        (@IsLocalRing.ResidueField.field (CommRingCat.carrier (S.presheaf.stalk x))
          (@CommRingCat.instCommRingObjForgetRingHomCarrier (S.presheaf.stalk x)) h))
      (@CommRingCat.instCommRingObjForgetRingHomCarrier (S.residueField x)) := by
  rfl

meta section
open Lean Meta Elab Tactic

/-- Only the diagnosed raw-stalk field projection and SAME bundled residue ring. -/
private def idealPhiStoredRawRingProof026 (left right : Expr) : MetaM Expr := do
  let left := left.consumeMData
  let right := right.consumeMData
  let la := left.getAppArgs
  let ra := right.getAppArgs
  let .const ln ll := left.getAppFn
    | throwError "IdealPhiRawRing026 expected a constant raw field projection."
  let .const rn rl := right.getAppFn
    | throwError "IdealPhiRawRing026 expected a constant bundled ring instance."
  unless ln == ``Field.toCommRing && rn == ``CommRingCat.instCommRingObjForgetRingHomCarrier &&
      la.size == 2 && ra.size == 1 && ll == rl && ll.length == 1 do
    throwError "IdealPhiRawRing026 refused different outer heads/arity/universes."
  let carrier := la[0]!.consumeMData
  let field := la[1]!.consumeMData
  let bundle := ra[0]!.consumeMData
  let ca := carrier.getAppArgs
  let fa := field.getAppArgs
  let ba := bundle.getAppArgs
  unless carrier.getAppFn == mkConst ``IsLocalRing.ResidueField ll && ca.size == 3 &&
      field.getAppFn == mkConst ``IsLocalRing.ResidueField.field ll && fa.size == 3 &&
      bundle.getAppFn == mkConst ``Scheme.residueField ll && ba.size == 2 do
    throwError "IdealPhiRawRing026 refused different residue-field stored parents."
  for i in [:3] do
    unless ca[i]!.equal fa[i]! do
      throwError "IdealPhiRawRing026 raw residue carrier/field argument {i} differs."
  let proof := mkAppN (mkConst ``idealPhiRawNativeCommRingHEq026 ll)
    #[ba[0]!, ba[1]!, ca[2]!]
  let some (_, pl, _, pr) := (← inferType proof).consumeMData.headBeta.heq?
    | throwError "IdealPhiRawRing026 ordinary law did not infer an HEq."
  logInfo m!"IdealPhiRawRing026 SAME stored R/ring/h=true; ordinary endpoints raw-match={pl.equal left}/{pr.equal right}."
  unless pl.equal left && pr.equal right do
    throwError "IdealPhiRawRing026 refused different ordinary-law endpoints."
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "IdealPhiRawRing026 unresolved/recovery ordinary law."
  return proof

/-- Extract the raw ring seed from the actual stored inner equivalence and q. -/
private def idealPhiStoredRawRingPair026 (supplied : Syntax) : Term.TermElabM (Expr × Expr) := do
  let (values, _) ← idealPhiEndpointVectors016 supplied
  let e := values[3]!.consumeMData
  let ea := e.getAppArgs
  unless e.getAppFn.isConstOf ``actualCubicPositiveTwoOriginalNativePointFiberEquiv &&
      ea.size == 10 do
    throwError "IdealPhiRawRing026 expected the exact actual native equivalence vector."
  let q := ea[6]!.consumeMData
  let qa := q.getAppArgs
  let .const qn ql := q.getAppFn
    | throwError "IdealPhiRawRing026 expected the stored original native point map."
  unless qn == ``Scheme.fromSpecResidueField && qa.size == 2 && ql.length == 1 do
    throwError "IdealPhiRawRing026 refused a different native point-map vector."
  let left := mkAppN (mkConst ``Field.toCommRing ql) #[ea[1]!, ea[3]!]
  let bundle := mkAppN (mkConst ``Scheme.residueField ql) qa
  let right := mkApp (mkConst ``CommRingCat.instCommRingObjForgetRingHomCarrier ql) bundle
  discard <| idealPhiStoredRawRingProof026 left right
  return (left, right)

elab "ideal_phi_stored_raw_ring026% " supplied:term : term => do
  let (left, right) ← idealPhiStoredRawRingPair026 supplied
  return (← mkHEq left right)

elab "ideal_phi_stored_raw_ring026" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, left, _, right) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.heq?
    | throwError "IdealPhiRawRing026 expected the exact stored residue-ring HEq."
  let proof ← idealPhiStoredRawRingProof026 left right
  logInfo "IdealPhiRawRing026 emitted ordinary exact stored residue-ring certificate."
  goal.assign proof
  replaceMainGoal []

end

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_stored_rawRing026
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_stored_raw_ring026%
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  ideal_phi_stored_raw_ring026

namespace IdealPhiChartResidue023
open AlgebraicGeometry

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

end IdealPhiChartResidue023
end

namespace IdealPhiChartStructural023

universe v

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

end IdealPhiChartStructural023

meta section
namespace IdealPhiChartStructural023
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
  let proof := mkAppN (mkConst ``IdealPhiChartResidue023.native_commRing_eq levels) fieldArgs
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
  let proof := mkAppN (mkConst ``IdealPhiChartResidue023.native_bundle_eq levels) ra
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
  let proof := mkAppN (mkConst ``IdealPhiChartResidue023.native_carrier_eq levels) nativeArgs
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
  let proof := mkAppN (mkConst ``IdealPhiChartResidue023.native_field_heq levels) la
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
  let proof := mkAppN (mkConst ``IdealPhiChartResidue023.native_standard_bundle_eq levels) ra
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

end IdealPhiChartStructural023
end

meta section
open Lean Meta Elab Tactic

elab "ideal_phi_chart_exact023 " supplied:term " using " suppliedSeed:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← Term.elabTerm supplied none (catchExPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    let source ← instantiateMVars source
    let sourceType ← instantiateMVars (← inferType source)
    let target ← instantiateMVars (← goal.getType)
    if source.hasMVar || source.hasLevelMVar || source.hasLooseBVars || source.hasSorry then
      throwError "IdealPhiChart023 source flags: expression metavariables={source.hasMVar}, level metavariables={source.hasLevelMVar}, loose variables={source.hasLooseBVars}, recovery={source.hasSorry}."
    let seed ← Term.elabTerm suppliedSeed none (catchExPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    let seed ← instantiateMVars seed
    if seed.hasMVar || seed.hasLevelMVar || seed.hasLooseBVars || seed.hasSorry then
      throwError "IdealPhiChart023 unresolved/recovery seed."
    let seedType := (← instantiateMVars (← inferType seed)).consumeMData.headBeta
    let (seedLeft, seedRight, seedHEq) ← match seedType.eq?, seedType.heq? with
      | some (_, left, right), _ => do
          -- Frozen021 SAME-semifield projection law.
          discard <| idealPhiStoredSemiringProof021 left right
          pure (left, right, ← mkHEqOfEq seed)
      | _, some (_, left, _, right) => do
          -- New026 EXACT raw-stalk/bundled native residue ring law.
          discard <| idealPhiStoredRawRingProof026 left right
          pure (left, right, seed)
      | _, _ => throwError "IdealPhiChart023 expected an exact stored projection Eq or residue-ring HEq."
    let reverseSeed ← mkHEqSymm seedHEq
    logInfo "IdealPhiChart023 inserted the passed exact projection law and its ordinary reverse into the existing proof cache."
    let (heq, state) ←
      (IdealPhiChartStructural023.structuralHEq sourceType target
        96 #[] "chart009").run
          { pairs := #[(seedLeft, seedRight, seedHEq), (seedRight, seedLeft, reverseSeed)] }
    let typeProof ← mkEqOfHEq heq
    let proof := mkAppN (mkConst ``Eq.mp [Level.zero])
      #[sourceType, target, typeProof, source]
    -- Builders can assign fresh expression/universe metavariables after the
    -- input expressions were instantiated. Resolve assigned values once more,
    -- then reject anything still unresolved or a recovery expression.
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "IdealPhiChart023 emitted flags: expression metavariables={proof.hasMVar}, level metavariables={proof.hasLevelMVar}, loose variables={proof.hasLooseBVars}, recovery={proof.hasSorry}."
    logInfo m!"IdealPhiChart023 ordinary exact compatibility emitted: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruence steps={state.congrSteps}, binders={state.binderSteps}, unused traversal budget={state.remaining}."
    goal.assign proof
    replaceMainGoal []

end


meta section
open Lean Meta Elab Tactic

/-- Original reflexivity source with ONLY the passed projection equality cached. -/
elab "ideal_phi_endpoint_seeded023 " suppliedSeed:term : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
  let source ← match target.eq?, target.heq? with
    | some (_, left, _), _ => mkEqRefl left
    | _, some (_, left, _, _) => mkHEqRefl left
    | _, _ => throwError "IdealPhiChart023 expected the original endpoint Eq/HEq."
  let supplied ← Term.exprToSyntax source
  evalTactic (← `(tactic| ideal_phi_chart_exact023 $supplied using $suppliedSeed))

end

universe v w x

/-- The DFinsupp alias uses the SAME fourteen semilinear instance arguments. -/
private theorem idealPhiSameEquivLikeInstances029
    {R : Type u} {S : Type v} [Semiring R] [Semiring S]
    (σ : R →+* S) {σ' : S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type w) (M₂ : Type x) [AddCommMonoid M] [AddCommMonoid M₂]
    [Module R M] [Module S M₂] :
    @DFinsupp.instEquivLikeLinearEquiv R S _ _ σ σ' _ _ M M₂ _ _ _ _ =
    @LinearEquiv.instEquivLike R S M M₂ _ _ _ _ _ _ σ σ' _ _ := by
  rfl

meta section
open Lean Meta Elab Tactic

private def idealPhiEquivLikePair028 (supplied : Syntax) : Term.TermElabM (Expr × Expr × Expr) := do
  let (values, _) ← idealPhiEndpointVectors016 supplied
  let left := values[14]!.consumeMData
  let right := values[15]!.consumeMData
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless left.getAppFn.isConstOf ``EquivLike.toFunLike && la.size == 4 &&
      right.getAppFn.isConstOf ``EquivLike.toFunLike && ra.size == 4 do
    throwError "IdealPhiEquivLike028 expected the exact outer argument3 FunLike vector."
  let leftInst := la[3]!.consumeMData
  let rightInst := ra[3]!.consumeMData
  let lia := leftInst.getAppArgs
  let ria := rightInst.getAppArgs
  let .const ln ll := leftInst.getAppFn
    | throwError "IdealPhiEquivLike028 expected a constant left instance."
  let .const rn rl := rightInst.getAppFn
    | throwError "IdealPhiEquivLike028 expected a constant right instance."
  unless ln == ``DFinsupp.instEquivLikeLinearEquiv && rn == ``LinearEquiv.instEquivLike &&
      lia.size == 14 && ria.size == 14 && ll == rl && ll.length == 4 do
    throwError "IdealPhiEquivLike028 refused different stored instance heads/arity/universes."
  let permuted := #[lia[0]!, lia[1]!, lia[8]!, lia[9]!, lia[2]!, lia[3]!,
    lia[10]!, lia[11]!, lia[12]!, lia[13]!, lia[4]!, lia[5]!, lia[6]!, lia[7]!]
  let middle := mkAppN (mkConst ``LinearEquiv.instEquivLike ll) permuted
  logInfo "IdealPhiEquivLike028 extracted actual left/right14 and explicitly permuted SAME-left14 middle; no native endpoint conversion assumed."
  return (leftInst, middle, rightInst)

private def idealPhiEquivLikeSourceProof028 (left middle : Expr) : MetaM Expr := do
  let left := left.consumeMData
  let middle := middle.consumeMData
  let .const ln ll := left.getAppFn
    | throwError "IdealPhiEquivLike028 expected a stored alias instance."
  let la := left.getAppArgs
  unless ln == ``DFinsupp.instEquivLikeLinearEquiv && la.size == 14 && ll.length == 4 &&
      middle.equal (mkAppN (mkConst ``LinearEquiv.instEquivLike ll)
        #[la[0]!, la[1]!, la[8]!, la[9]!, la[2]!, la[3]!, la[10]!, la[11]!,
          la[12]!, la[13]!, la[4]!, la[5]!, la[6]!, la[7]!]) do
    throwError "IdealPhiEquivLike028 refused different explicitly permuted SAME-left14 middle."
  let proof := mkAppN (mkConst ``idealPhiSameEquivLikeInstances029 ll) la
  let some (_, pl, pr) := (← inferType proof).consumeMData.headBeta.eq?
    | throwError "IdealPhiEquivLike028 ordinary SAME14 law did not infer equality."
  logInfo m!"IdealPhiEquivLike028 ordinary permuted SAME14 law raw endpoints={pl.equal left}/{pr.equal middle}."
  unless pl.equal left && pr.equal middle do
    throwError "IdealPhiEquivLike028 refused different ordinary SAME14 law endpoints."
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "IdealPhiEquivLike028 unresolved/recovery ordinary SAME14 law."
  return proof

elab "ideal_phi_equivlike_source028% " supplied:term : term => do
  let (left, middle, _) ← idealPhiEquivLikePair028 supplied
  discard <| idealPhiEquivLikeSourceProof028 left middle
  return (← mkEq left middle)

elab "ideal_phi_equivlike_source028" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, left, middle) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.eq?
    | throwError "IdealPhiEquivLike028 expected SAME-left14 instance equality."
  goal.assign (← idealPhiEquivLikeSourceProof028 left middle)
  replaceMainGoal []

elab "ideal_phi_equivlike_vector028% " supplied:term : term => do
  let (_, middle, right) ← idealPhiEquivLikePair028 supplied
  return (← mkHEq middle right)

elab "ideal_phi_equivlike_instance028% " supplied:term : term => do
  let (left, _, right) ← idealPhiEquivLikePair028 supplied
  return (← mkHEq left right)

/-- Own stored vectors: first ordinary alias law, then checked native vector HEq. -/
elab "ideal_phi_equivlike_join028% " suppliedSource:term ", " suppliedVector:term : term => do
  let source ← Term.elabTerm suppliedSource none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let source ← instantiateMVars source
  let vector ← Term.elabTerm suppliedVector none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let vector ← instantiateMVars vector
  let some (_, left, middle) := (← inferType source).consumeMData.headBeta.eq?
    | throwError "IdealPhiEquivLike028 expected an ordinary SAME14 source equality."
  discard <| idealPhiEquivLikeSourceProof028 left middle
  let some (_, storedMiddle, _, right) := (← inferType vector).consumeMData.headBeta.heq?
    | throwError "IdealPhiEquivLike028 expected the checked native vector HEq."
  unless middle.equal storedMiddle && right.getAppFn.isConstOf ``LinearEquiv.instEquivLike &&
      right.getAppArgs.size == 14 do
    throwError "IdealPhiEquivLike028 refused a different ordinary join middle/right."
  let proof ← mkHEqTrans (← mkHEqOfEq source) vector
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "IdealPhiEquivLike028 unresolved/recovery ordinary instance join."
  return proof

end

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_stored_equivLikeSource028
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_equivlike_source028%
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  ideal_phi_equivlike_source028

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_stored_equivLikeVector028
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_equivlike_vector028%
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  have hResidueRing := actualOriginalIdealQuadraticPositiveTwoPhi_stored_rawRing026 p hp P hP s
  ideal_phi_endpoint_seeded023 hResidueRing

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_equivLikeInferredJoin028
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (ideal_phi_equivlike_join028%
      (actualOriginalIdealQuadraticPositiveTwoPhi_stored_equivLikeSource028 p hp P hP s),
      (actualOriginalIdealQuadraticPositiveTwoPhi_stored_equivLikeVector028 p hp P hP s)) :=
  ideal_phi_equivlike_join028%
      (actualOriginalIdealQuadraticPositiveTwoPhi_stored_equivLikeSource028 p hp P hP s),
      (actualOriginalIdealQuadraticPositiveTwoPhi_stored_equivLikeVector028 p hp P hP s)

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_stored_equivLikeInstance028
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_equivlike_instance028%
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  exact actualOriginalIdealQuadraticPositiveTwoPhi_equivLikeInferredJoin028 p hp P hP s

meta section
open Lean Meta Elab Tactic

/-- Exact passed ring HEq plus exact checked stored instance HEq, ordinary cache leaves. -/
elab "ideal_phi_endpoint_two_seeds028 " suppliedRing:term ", " suppliedInstance:term : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
  let source ← match target.eq?, target.heq? with
    | some (_, left, _), _ => mkEqRefl left
    | _, some (_, left, _, _) => mkHEqRefl left
    | _, _ => throwError "IdealPhiTwoSeeds028 expected original endpoint Eq/HEq."
  let ring ← Term.elabTerm suppliedRing none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let ring ← instantiateMVars ring
  let instanceProof ← Term.elabTerm suppliedInstance none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let instanceProof ← instantiateMVars instanceProof
  let ringType := (← instantiateMVars (← inferType ring)).consumeMData.headBeta
  logInfo m!"IdealPhiTwoSeeds030 ring type head={idealPhiSemiringHead021 ringType}; arity={ringType.getAppArgs.size}; expression metavariables={ringType.hasMVar}; level metavariables={ringType.hasLevelMVar}."
  let some (_, ringLeft, _, ringRight) := ringType.heq?
    | throwError "IdealPhiTwoSeeds028 expected exact stored ring HEq."
  discard <| idealPhiStoredRawRingProof026 ringLeft ringRight
  let instanceType := (← instantiateMVars (← inferType instanceProof)).consumeMData.headBeta
  logInfo m!"IdealPhiTwoSeeds030 instance type head={idealPhiSemiringHead021 instanceType}; arity={instanceType.getAppArgs.size}; expression metavariables={instanceType.hasMVar}; level metavariables={instanceType.hasLevelMVar}."
  let some (_, instanceLeft, _, instanceRight) := instanceType.heq?
    | throwError "IdealPhiTwoSeeds028 expected exact stored instance HEq."
  unless instanceLeft.getAppFn.isConstOf ``DFinsupp.instEquivLikeLinearEquiv &&
      instanceRight.getAppFn.isConstOf ``LinearEquiv.instEquivLike &&
      instanceLeft.getAppArgs.size == 14 && instanceRight.getAppArgs.size == 14 do
    throwError "IdealPhiTwoSeeds028 refused different instance seed heads/arity."
  if ring.hasMVar || ring.hasLevelMVar || ring.hasLooseBVars || ring.hasSorry ||
      instanceProof.hasMVar || instanceProof.hasLevelMVar || instanceProof.hasLooseBVars || instanceProof.hasSorry then
    throwError "IdealPhiTwoSeeds028 unresolved/recovery ordinary cache seeds."
  let sourceType ← inferType source
  let reverseRing ← mkHEqSymm ring
  let reverseInstance ← mkHEqSymm instanceProof
  let (heq, state) ←
    (IdealPhiChartStructural023.structuralHEq sourceType target
      96 #[] "chart009").run
        { pairs := #[(ringLeft, ringRight, ring), (ringRight, ringLeft, reverseRing),
          (instanceLeft, instanceRight, instanceProof), (instanceRight, instanceLeft, reverseInstance)] }
  let typeProof ← mkEqOfHEq heq
  let proof := mkAppN (mkConst ``Eq.mp [Level.zero]) #[sourceType, target, typeProof, source]
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "IdealPhiTwoSeeds028 unresolved/recovery emitted ordinary certificate."
  logInfo m!"IdealPhiTwoSeeds028 ordinary exact compatibility emitted: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruence steps={state.congrSteps}, binders={state.binderSteps}, unused traversal budget={state.remaining}."
  goal.assign proof
  replaceMainGoal []

end

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_OuterArgument0HEq016
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_endpoint_certificate016% 4
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  have hResidueRing := actualOriginalIdealQuadraticPositiveTwoPhi_stored_rawRing026 p hp P hP s
  ideal_phi_endpoint_seeded023 hResidueRing

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_OuterArgument1HEq016
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_endpoint_certificate016% 5
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  have hResidueRing := actualOriginalIdealQuadraticPositiveTwoPhi_stored_rawRing026 p hp P hP s
  ideal_phi_endpoint_seeded023 hResidueRing

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_OuterArgument2HEq016
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_endpoint_certificate016% 6
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  have hResidueRing := actualOriginalIdealQuadraticPositiveTwoPhi_stored_rawRing026 p hp P hP s
  ideal_phi_endpoint_seeded023 hResidueRing

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_OuterArgument3HEq016
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_endpoint_certificate016% 7
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  have hResidueRing := actualOriginalIdealQuadraticPositiveTwoPhi_stored_rawRing026 p hp P hP s
  have hInstance := actualOriginalIdealQuadraticPositiveTwoPhi_stored_equivLikeInstance028 p hp P hP s
  ideal_phi_endpoint_two_seeds028 hResidueRing, hInstance

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_OuterArgument4HEq016
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_endpoint_certificate016% 8
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  ideal_phi_endpoint_certificate016

meta section
open Lean Meta Elab Tactic

/-- The same stored inverse application argument occurs on both outer sides. -/
elab "ideal_phi_outer_argument5_refl025% " supplied:term : term => do
  let (values, _) ← idealPhiEndpointVectors016 supplied
  let left := values[6]!.consumeMData
  let right := values[7]!.consumeMData
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless left.getAppFn.isConstOf ``DFunLike.coe && right.getAppFn.isConstOf ``DFunLike.coe &&
      la.size == 6 && ra.size == 6 && la[5]!.equal ra[5]! do
    throwError "IdealPhiOuter025 refused different stored inverse application arguments."
  return (← mkHEqRefl la[5]!)

/-- Infer coe6 congruence only from independently checked certificates' own vectors. -/
syntax "ideal_phi_outer_source025% " "[" term,* "]" : term
elab_rules : term
  | `(ideal_phi_outer_source025% [$certificates,*]) => do
    unless certificates.getElems.size == 6 do
      throwError "IdealPhiOuter025 expected six exact outer component certificates."
    let mut hs := #[]
    let mut la := #[]
    let mut ra := #[]
    for supplied in certificates.getElems do
      let h ← Term.elabTerm supplied none (catchExPostpone := false)
      Term.synthesizeSyntheticMVarsNoPostponing
      let h ← instantiateMVars h
      let proposition := (← whnf (← inferType h)).consumeMData.headBeta
      let some (_, left, _, right) := proposition.heq?
        | throwError "IdealPhiOuter025 expected the stored component HEq."
      hs := hs.push h
      la := la.push left
      ra := ra.push right
    let source ← mkAppOptM ``DFunLike.coe (la.map fun a => some a)
    Term.synthesizeSyntheticMVarsNoPostponing
    let source ← instantiateMVars source
    let head := source.getAppFn
    unless head.isConstOf ``DFunLike.coe && source.getAppArgs.size == 6 do
      throwError "IdealPhiOuter025 expected exact DFunLike.coe head/arity6."
    let thm ← mkHCongrWithArity head 6
    let mut arguments := #[]
    for i in [:6] do
      let h ← match thm.argKinds[i]! with
        | .eq => mkEqOfHEq hs[i]!
        | .heq => pure hs[i]!
        | _ => throwError "IdealPhiOuter025 unexpected congruence argument kind."
      arguments := arguments ++ #[la[i]!, ra[i]!, h]
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars (mkAppN thm.proof arguments)
    if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "IdealPhiOuter025 unresolved/recovery inferred ordinary coe6 proof."
    logInfo "IdealPhiOuter025 ordinary coe6 proof inferred from own exact component vectors; no native expected type or intro substitutions."
    return proof

end

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_outerInferredApplication025
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (ideal_phi_outer_source025% [
      actualOriginalIdealQuadraticPositiveTwoPhi_OuterArgument0HEq016 p hp P hP s,
      actualOriginalIdealQuadraticPositiveTwoPhi_OuterArgument1HEq016 p hp P hP s,
      actualOriginalIdealQuadraticPositiveTwoPhi_OuterArgument2HEq016 p hp P hP s,
      actualOriginalIdealQuadraticPositiveTwoPhi_OuterArgument3HEq016 p hp P hP s,
      actualOriginalIdealQuadraticPositiveTwoPhi_OuterArgument4HEq016 p hp P hP s,
      ideal_phi_outer_argument5_refl025%
        (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s)]) :=
  ideal_phi_outer_source025% [
      actualOriginalIdealQuadraticPositiveTwoPhi_OuterArgument0HEq016 p hp P hP s,
      actualOriginalIdealQuadraticPositiveTwoPhi_OuterArgument1HEq016 p hp P hP s,
      actualOriginalIdealQuadraticPositiveTwoPhi_OuterArgument2HEq016 p hp P hP s,
      actualOriginalIdealQuadraticPositiveTwoPhi_OuterArgument3HEq016 p hp P hP s,
      actualOriginalIdealQuadraticPositiveTwoPhi_OuterArgument4HEq016 p hp P hP s,
      ideal_phi_outer_argument5_refl025%
        (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s)]

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_LeftEvaluationHEq016
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_endpoint_certificate016% 3
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  exact actualOriginalIdealQuadraticPositiveTwoPhi_outerInferredApplication025 p hp P hP s
private theorem actualOriginalIdealQuadraticPositiveTwoPhi_exactInnerLaw016
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (ideal_phi_inner_law016%
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s)) :=
  ideal_phi_inner_law016%
    (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s)

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_CarrierEq016
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_endpoint_certificate016% 0
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  ideal_phi_endpoint_certificate016

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_NativeEHEq016
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_endpoint_certificate016% 1
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  ideal_phi_endpoint_certificate016

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_NativeValueHEq016
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_endpoint_certificate016% 2
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  have hSemiring := actualOriginalIdealQuadraticPositiveTwoPhi_stored_semiring021 p hp P hP s
  ideal_phi_endpoint_seeded023 hSemiring

meta section
open Lean Meta Elab Tactic

/-- The exact normalized public proposition, from the already checked endpoint factory. -/
elab "ideal_phi_normalized_public031% " supplied:term : term => do
  let (values, _) ← idealPhiEndpointVectors016 supplied
  let level ← getLevel values[0]!
  return mkAppN (mkConst ``Eq [level]) #[values[0]!, values[6]!, values[4]!]

/-- Equality-of-propositions assembled only from the certificates' own stored vectors. -/
elab "ideal_phi_public_proof031% " suppliedCarrier:term ", " suppliedLeft:term ", " suppliedRight:term ", " suppliedLaw:term : term => do
  let carrier ← Term.elabTerm suppliedCarrier none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let carrier ← instantiateMVars carrier
  let left ← Term.elabTerm suppliedLeft none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let left ← instantiateMVars left
  let right ← Term.elabTerm suppliedRight none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let right ← instantiateMVars right
  let law ← Term.elabTerm suppliedLaw none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let law ← instantiateMVars law
  let some (_, publicCarrier, lawCarrier) :=
      (← instantiateMVars (← inferType carrier)).consumeMData.headBeta.eq?
    | throwError "IdealPhiPublic031 expected the checked native carrier equality."
  let some (_, publicLeft, _, lawLeft) :=
      (← instantiateMVars (← inferType left)).consumeMData.headBeta.heq?
    | throwError "IdealPhiPublic031 expected the checked whole-left evaluation HEq."
  let some (_, publicRight, _, lawRight) :=
      (← instantiateMVars (← inferType right)).consumeMData.headBeta.heq?
    | throwError "IdealPhiPublic031 expected the checked native-value HEq."
  let lawType := (← instantiateMVars (← inferType law)).consumeMData.headBeta
  let some (storedCarrier, storedLeft, storedRight) := lawType.eq?
    | throwError "IdealPhiPublic031 expected the exact checked inner inverse law."
  logInfo m!"IdealPhiPublic031 exact law vector raw matches={storedCarrier.equal lawCarrier}/{storedLeft.equal lawLeft}/{storedRight.equal lawRight}."
  unless storedCarrier.equal lawCarrier && storedLeft.equal lawLeft && storedRight.equal lawRight do
    throwError "IdealPhiPublic031 refused different exact ordinary law vectors."
  let level ← getLevel publicCarrier
  let head := mkConst ``Eq [level]
  let thm ← mkHCongrWithArity head 3
  let la := #[publicCarrier, publicLeft, publicRight]
  let ra := #[lawCarrier, lawLeft, lawRight]
  let hs := #[(← mkHEqOfEq carrier), left, right]
  let mut arguments := #[]
  for i in [:3] do
    let h ← match thm.argKinds[i]! with
      | .eq => mkEqOfHEq hs[i]!
      | .heq => pure hs[i]!
      | _ => throwError "IdealPhiPublic031 unexpected Eq3 congruence argument kind."
    arguments := arguments ++ #[la[i]!, ra[i]!, h]
  let propositionHEq := mkAppN thm.proof arguments
  let propositionEq ← mkEqOfHEq propositionHEq
  let publicType := mkAppN head la
  let proof := mkAppN (mkConst ``Eq.mpr [Level.zero]) #[publicType, lawType, propositionEq, law]
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "IdealPhiPublic031 unresolved/recovery own-vector ordinary transport."
  logInfo "IdealPhiPublic031 emitted ordinary Eq3 proposition transport from own checked vectors; no original header conversion assumed."
  return proof

end

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_publicInferredTransport031
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (ideal_phi_public_proof031%
      (actualOriginalIdealQuadraticPositiveTwoPhi_CarrierEq016 p hp P hP s),
      (actualOriginalIdealQuadraticPositiveTwoPhi_LeftEvaluationHEq016 p hp P hP s),
      (actualOriginalIdealQuadraticPositiveTwoPhi_NativeValueHEq016 p hp P hP s),
      (actualOriginalIdealQuadraticPositiveTwoPhi_exactInnerLaw016 p hp P hP s)) :=
  ideal_phi_public_proof031%
      (actualOriginalIdealQuadraticPositiveTwoPhi_CarrierEq016 p hp P hP s),
      (actualOriginalIdealQuadraticPositiveTwoPhi_LeftEvaluationHEq016 p hp P hP s),
      (actualOriginalIdealQuadraticPositiveTwoPhi_NativeValueHEq016 p hp P hP s),
      (actualOriginalIdealQuadraticPositiveTwoPhi_exactInnerLaw016 p hp P hP s)

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_publicNormalized031
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_normalized_public031%
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  exact actualOriginalIdealQuadraticPositiveTwoPhi_publicInferredTransport031 p hp P hP s

meta section
open Lean Meta Elab Tactic

/-- Original opaque Phi map/application versus its ONE guarded defining delta. -/
private def idealPhiMapEvaluationVectors033 (supplied : Syntax) : Term.TermElabM (Array Expr) := do
  let original ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let original ← instantiateMVars original
  let original ← whnf original
  let some (originalCarrier, originalLeft, originalRight) := original.consumeMData.headBeta.eq?
    | throwError "IdealPhiMap033 expected the actual original public coefficient Eq."
  let outer := originalLeft.consumeMData
  let oa := outer.getAppArgs
  unless outer.getAppFn.isConstOf ``DFunLike.coe && oa.size == 6 do
    throwError "IdealPhiMap033 expected the actual original outer evaluation6."
  let value := oa[5]!.consumeMData
  let va := value.getAppArgs
  unless value.getAppFn.isConstOf ``DFunLike.coe && va.size == 6 do
    throwError "IdealPhiMap033 expected the opaque Phi application6."
  let phiMap := va[4]!.consumeMData
  logInfo m!"IdealPhiMap034 stored opaque Phi head={idealPhiSemiringHead021 phiMap}; arity={phiMap.getAppArgs.size}."
  unless phiMap.getAppFn.isConstOf ``actualOriginalIdealQuadraticPositiveTwoPhi &&
      phiMap.getAppArgs.size == 7 do
    throwError "IdealPhiMap033 refused a different opaque Phi map head/arity."
  let some expanded ← delta? phiMap (fun n => n == ``actualOriginalIdealQuadraticPositiveTwoPhi)
    | throwError "IdealPhiMap033 could not unfold the ONE original Phi declaration."
  let expandedValue := mkAppN value.getAppFn (va.set! 4 expanded)
  let (normalized, _) ← idealPhiEndpointVectors016 supplied
  let normalizedLeft := normalized[6]!.consumeMData
  let na := normalizedLeft.getAppArgs
  unless normalizedLeft.getAppFn.isConstOf ``DFunLike.coe && na.size == 6 do
    throwError "IdealPhiMap033 expected the existing normalized outer evaluation6."
  let normalizedValue := na[5]!
  logInfo m!"IdealPhiMap033 original/normalized proposition carrier raw-match={originalCarrier.equal normalized[0]!}; right raw-match={originalRight.equal normalized[4]!}; exact opaquePhi7 extracted, ONE delta only."
  logInfo m!"IdealPhiMap033 map/body heads={idealPhiSemiringHead021 phiMap}/{idealPhiSemiringHead021 expanded}; application/body-value/normalized-inner heads={idealPhiSemiringHead021 value}/{idealPhiSemiringHead021 expandedValue}/{idealPhiSemiringHead021 normalizedValue}."
  return #[phiMap, expanded, value, expandedValue, normalizedValue]

elab "ideal_phi_map_cut033% " index:num supplied:term : term => do
  let values ← idealPhiMapEvaluationVectors033 supplied
  match index.getNat with
  | 0 => mkEq values[0]! values[1]!
  | 1 => mkEq values[2]! values[3]!
  | 2 => mkHEq values[3]! values[4]!
  | _ => throwError "IdealPhiMap033 cut index out of range."

/-- Only ONE stored Phi-defining delta is justified by this ordinary rfl cut. -/
elab "ideal_phi_map_definition033" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, left, right) := (← instantiateMVars (← goal.getType)).consumeMData.headBeta.eq?
    | throwError "IdealPhiMap033 expected the defining-map equality."
  logInfo m!"IdealPhiMap034 defining-law opaque Phi head={idealPhiSemiringHead021 left}; arity={left.getAppArgs.size}."
  unless left.getAppFn.isConstOf ``actualOriginalIdealQuadraticPositiveTwoPhi &&
      left.getAppArgs.size == 7 do
    throwError "IdealPhiMap033 refused a different stored Phi map."
  let some expanded ← delta? left (fun n => n == ``actualOriginalIdealQuadraticPositiveTwoPhi)
    | throwError "IdealPhiMap033 missing guarded Phi delta."
  unless right.equal expanded do
    throwError "IdealPhiMap033 refused a different exact defining body."
  logInfo "IdealPhiMap033 assigned ordinary rfl for exactly ONE defining Phi delta; kernel must check it."
  goal.assign (← mkEqRefl left)
  replaceMainGoal []

/-- Lift the checked defining-map equality through its SAME original application vector. -/
elab "ideal_phi_map_application033% " suppliedProposition:term ", " suppliedDefinition:term : term => do
  let values ← idealPhiMapEvaluationVectors033 suppliedProposition
  let definition ← Term.elabTerm suppliedDefinition none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let definition ← instantiateMVars definition
  let some (_, leftMap, rightMap) :=
      (← instantiateMVars (← inferType definition)).consumeMData.headBeta.eq?
    | throwError "IdealPhiMap033 expected the checked defining-map equality."
  unless leftMap.equal values[0]! && rightMap.equal values[1]! do
    throwError "IdealPhiMap033 refused different exact defining-map endpoints."
  let value := values[2]!.consumeMData
  let va := value.getAppArgs
  let function ← withLocalDeclD `phiMap (← inferType leftMap) fun m => do
    mkLambdaFVars #[m] (mkAppN value.getAppFn (va.set! 4 m))
  let proof ← mkCongrArg function definition
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "IdealPhiMap033 unresolved/recovery own-vector ordinary application proof."
  logInfo "IdealPhiMap033 ordinary application congruence inferred from SAME original coe6 vector and checked map delta."
  return proof

/-- Separate bounded ordinary reflexivity check for the remaining value computation. -/
elab "ideal_phi_map_computation033" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, left, _, _) :=
      (← instantiateMVars (← goal.getType)).consumeMData.headBeta.heq?
    | throwError "IdealPhiMap033 expected the exact applied-body/normalized-inner HEq."
  logInfo "IdealPhiMap033 assigned ordinary HEq.rfl for the remaining applied-body/normalized-inner conversion; kernel must check it."
  goal.assign (← mkHEqRefl left)
  replaceMainGoal []

end

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_definingMapEq033
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_map_cut033% 0
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  ideal_phi_map_definition033

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_appliedMapInferred033
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (ideal_phi_map_application033%
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s),
      (actualOriginalIdealQuadraticPositiveTwoPhi_definingMapEq033 p hp P hP s)) :=
  ideal_phi_map_application033%
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s),
      (actualOriginalIdealQuadraticPositiveTwoPhi_definingMapEq033 p hp P hP s)

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_appliedMapEq033
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_map_cut033% 1
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  exact actualOriginalIdealQuadraticPositiveTwoPhi_appliedMapInferred033 p hp P hP s

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_bodyValueHEq033
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_map_cut033% 2
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  ideal_phi_map_computation033

meta section
open Lean Meta Elab Tactic

/-- Exact original public vectors and frozen031 normalized vectors. -/
private def idealPhiOriginalVectors035 (supplied : Syntax) : Term.TermElabM (Array Expr) := do
  let original ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let original ← instantiateMVars original
  let original ← whnf original
  let some (originalCarrier, originalLeft, originalRight) := original.consumeMData.headBeta.eq?
    | throwError "IdealPhiOriginal035 expected the exact original public Eq."
  let (normalized, _) ← idealPhiEndpointVectors016 supplied
  let left := originalLeft.consumeMData
  let right := normalized[6]!.consumeMData
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless left.getAppFn.isConstOf ``DFunLike.coe && right.getAppFn.isConstOf ``DFunLike.coe &&
      la.size == 6 && ra.size == 6 && left.getAppFn.equal right.getAppFn do
    throwError "IdealPhiOriginal035 refused different original/normalized outer evaluation6 heads."
  logInfo m!"IdealPhiOriginal035 carrier/right raw matches={originalCarrier.equal normalized[0]!}/{originalRight.equal normalized[4]!}."
  for i in [:5] do
    logInfo m!"IdealPhiOriginal035 original/normalized outer prefix[{i}] raw-match={la[i]!.equal ra[i]!}; heads={idealPhiSemiringHead021 la[i]!}/{idealPhiSemiringHead021 ra[i]!}."
  return #[originalCarrier, normalized[0]!, originalRight, normalized[4]!,
    originalLeft, normalized[6]!, la[5]!, ra[5]!, la[0]!, ra[0]!,
    la[1]!, ra[1]!, la[2]!, ra[2]!, la[3]!, ra[3]!, la[4]!, ra[4]!]

elab "ideal_phi_original_cut035% " index:num supplied:term : term => do
  let values ← idealPhiOriginalVectors035 supplied
  let i := index.getNat
  unless i < 9 do throwError "IdealPhiOriginal035 certificate index out of range."
  if i == 0 then mkEq values[0]! values[1]!
  else mkHEq values[2*i]! values[2*i+1]!

/-- A candidate definitional cut, certified ONLY if ordinary declaration checking passes. -/
elab "ideal_phi_original_rfl035" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
  let proof ← match target.eq?, target.heq? with
    | some (_, left, _), _ => mkEqRefl left
    | _, some (_, left, _, _) => mkHEqRefl left
    | _, _ => throwError "IdealPhiOriginal035 expected exact original/normalized Eq or HEq."
  logInfo "IdealPhiOriginal035 assigned ordinary reflexivity for one exact original/normalized cut; no acceptance assumed."
  goal.assign proof
  replaceMainGoal []

/-- Own-vector ordinary join of checked map application and checked body-value conversion. -/
elab "ideal_phi_original_value035% " suppliedApplication:term ", " suppliedBody:term : term => do
  let application ← Term.elabTerm suppliedApplication none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let application ← instantiateMVars application
  let body ← Term.elabTerm suppliedBody none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let body ← instantiateMVars body
  let some (_, originalValue, expandedValue) :=
      (← instantiateMVars (← inferType application)).consumeMData.headBeta.eq?
    | throwError "IdealPhiOriginal035 expected checked exact map-application equality."
  let some (_, bodyValue, _, _) :=
      (← instantiateMVars (← inferType body)).consumeMData.headBeta.heq?
    | throwError "IdealPhiOriginal035 expected checked exact body-value HEq."
  logInfo m!"IdealPhiOriginal035 map/body join middle raw-match={expandedValue.equal bodyValue}."
  unless expandedValue.equal bodyValue do
    throwError "IdealPhiOriginal035 refused a different checked original/body join middle."
  let proof ← mkHEqTrans (← mkHEqOfEq application) body
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "IdealPhiOriginal035 unresolved/recovery checked original-value join."
  return proof

end

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_originalCarrierEq035
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_original_cut035% 0
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  ideal_phi_original_rfl035

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_originalRightHEq035
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_original_cut035% 1
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  ideal_phi_original_rfl035

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_originalValueInferred035
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (ideal_phi_original_value035%
      (actualOriginalIdealQuadraticPositiveTwoPhi_appliedMapEq033 p hp P hP s),
      (actualOriginalIdealQuadraticPositiveTwoPhi_bodyValueHEq033 p hp P hP s)) :=
  ideal_phi_original_value035%
      (actualOriginalIdealQuadraticPositiveTwoPhi_appliedMapEq033 p hp P hP s),
      (actualOriginalIdealQuadraticPositiveTwoPhi_bodyValueHEq033 p hp P hP s)

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_originalValueHEq035
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_original_cut035% 3
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  exact actualOriginalIdealQuadraticPositiveTwoPhi_originalValueInferred035 p hp P hP s

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_originalOuterArgument0HEq035
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_original_cut035% 4
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  ideal_phi_original_rfl035

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_originalOuterArgument1HEq035
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_original_cut035% 5
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  ideal_phi_original_rfl035

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_originalOuterArgument2HEq035
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_original_cut035% 6
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  ideal_phi_original_rfl035

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_originalOuterArgument3HEq035
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_original_cut035% 7
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  ideal_phi_original_rfl035

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_originalOuterArgument4HEq035
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_original_cut035% 8
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  ideal_phi_original_rfl035

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_originalLeftInferred035
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (ideal_phi_outer_source025% [
      actualOriginalIdealQuadraticPositiveTwoPhi_originalOuterArgument0HEq035 p hp P hP s,
      actualOriginalIdealQuadraticPositiveTwoPhi_originalOuterArgument1HEq035 p hp P hP s,
      actualOriginalIdealQuadraticPositiveTwoPhi_originalOuterArgument2HEq035 p hp P hP s,
      actualOriginalIdealQuadraticPositiveTwoPhi_originalOuterArgument3HEq035 p hp P hP s,
      actualOriginalIdealQuadraticPositiveTwoPhi_originalOuterArgument4HEq035 p hp P hP s,
      actualOriginalIdealQuadraticPositiveTwoPhi_originalValueHEq035 p hp P hP s]) :=
  ideal_phi_outer_source025% [
      actualOriginalIdealQuadraticPositiveTwoPhi_originalOuterArgument0HEq035 p hp P hP s,
      actualOriginalIdealQuadraticPositiveTwoPhi_originalOuterArgument1HEq035 p hp P hP s,
      actualOriginalIdealQuadraticPositiveTwoPhi_originalOuterArgument2HEq035 p hp P hP s,
      actualOriginalIdealQuadraticPositiveTwoPhi_originalOuterArgument3HEq035 p hp P hP s,
      actualOriginalIdealQuadraticPositiveTwoPhi_originalOuterArgument4HEq035 p hp P hP s,
      actualOriginalIdealQuadraticPositiveTwoPhi_originalValueHEq035 p hp P hP s]

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_originalLeftHEq035
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_original_cut035% 2
      (actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s) := by
  exact actualOriginalIdealQuadraticPositiveTwoPhi_originalLeftInferred035 p hp P hP s

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_originalCoefficientInferred035
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (ideal_phi_public_proof031%
      (actualOriginalIdealQuadraticPositiveTwoPhi_originalCarrierEq035 p hp P hP s),
      (actualOriginalIdealQuadraticPositiveTwoPhi_originalLeftHEq035 p hp P hP s),
      (actualOriginalIdealQuadraticPositiveTwoPhi_originalRightHEq035 p hp P hP s),
      (actualOriginalIdealQuadraticPositiveTwoPhi_publicNormalized031 p hp P hP s)) :=
  ideal_phi_public_proof031%
      (actualOriginalIdealQuadraticPositiveTwoPhi_originalCarrierEq035 p hp P hP s),
      (actualOriginalIdealQuadraticPositiveTwoPhi_originalLeftHEq035 p hp P hP s),
      (actualOriginalIdealQuadraticPositiveTwoPhi_originalRightHEq035 p hp P hP s),
      (actualOriginalIdealQuadraticPositiveTwoPhi_publicNormalized031 p hp P hP s)

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_originalCoefficient035
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 p hp P hP s := by
  exact actualOriginalIdealQuadraticPositiveTwoPhi_originalCoefficientInferred035 p hp P hP s

meta section
open Lean Meta Elab Tactic

private def idealPhiSourceType041 (suppliedProof : Syntax) : Term.TermElabM Expr := do
  let source ← Term.elabTerm suppliedProof none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let source ← instantiateMVars source
  let sourceType ← instantiateMVars (← inferType source)
  if source.hasMVar || source.hasLevelMVar || source.hasLooseBVars || source.hasSorry ||
      sourceType.hasMVar || sourceType.hasLevelMVar || sourceType.hasLooseBVars || sourceType.hasSorry then
    throwError "IdealPhiSource041 unresolved/recovery ordinary source proof/type."
  return sourceType

private def idealPhiOriginalSourceType041 (suppliedProof : Syntax) : Term.TermElabM Expr := do
  let sourceType ← idealPhiSourceType041 suppliedProof
  let ty := sourceType.consumeMData.headBeta
  unless ty.getAppFn.isConstOf ``actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016 &&
      ty.getAppArgs.size == 8 do
    throwError "IdealPhiSource041 expected exact folded original coefficient Prop8."
  return sourceType

/-- Preserve original sharing: ONE producer delta, no recursive dsimp/projector traversal. -/
elab "ideal_phi_source_delta041% " suppliedProof:term : term => do
  let sourceType ← idealPhiOriginalSourceType041 suppliedProof
  let some expanded ← delta? sourceType
      (fun n => n == ``actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016)
    | throwError "IdealPhiSource041 missing the exact original producer delta."
  logInfo m!"IdealPhiSource041 ONE producer delta: folded/expanded heads={idealPhiSemiringHead021 sourceType}/{idealPhiSemiringHead021 expanded}; no recursive dsimp."
  return expanded

/-- Isolate ONLY the first/default producer dsimp step from040. -/
elab "ideal_phi_source_producer_dsimp041% " suppliedProof:term : term => do
  let sourceType ← idealPhiOriginalSourceType041 suppliedProof
  let mut theorems ← simpTheoremsOfNames [] true
  theorems ← theorems.addDeclToUnfold
    ``actualOriginalIdealQuadraticPositiveTwoPhi_coefficient_proposition016
  let config : Simp.Config := { ({} : DSimp.Config) with }
  let context ← Simp.mkContext
    (config := config) (simpTheorems := #[theorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let (normalized, _) ← dsimp sourceType context
  let normalized ← instantiateMVars normalized
  if normalized.hasMVar || normalized.hasLevelMVar || normalized.hasLooseBVars || normalized.hasSorry then
    throwError "IdealPhiSource041 unresolved/recovery producer-only dsimp type."
  logInfo m!"IdealPhiSource041 producer-only default dsimp head={idealPhiSemiringHead021 normalized}; arity={normalized.getAppArgs.size}."
  return normalized

/-- Isolate ONLY carrier-of normalization, taking the named checked first-stage proof. -/
elab "ideal_phi_source_coe_dsimp041% " suppliedProof:term : term => do
  let sourceType ← idealPhiSourceType041 suppliedProof
  let theorems ← simpTheoremsOfNames [``CommRingCat.coe_of] true
  let config : Simp.Config :=
    { ({ zeta := false, instances := true } : DSimp.Config) with }
  let context ← Simp.mkContext
    (config := config) (simpTheorems := #[theorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let (normalized, _) ← dsimp sourceType context
  let normalized ← instantiateMVars normalized
  if normalized.hasMVar || normalized.hasLevelMVar || normalized.hasLooseBVars || normalized.hasSorry then
    throwError "IdealPhiSource041 unresolved/recovery carrier-of-only type."
  logInfo m!"IdealPhiSource041 ONLY carrier-of stage changed={!(sourceType.equal normalized)}; head={idealPhiSemiringHead021 normalized}; arity={normalized.getAppArgs.size}."
  return normalized

end

private theorem actualOriginalIdealQuadraticPositiveTwoPhi_sourceSingleDelta041
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    ideal_phi_source_delta041%
      (actualOriginalIdealQuadraticPositiveTwoPhi_originalCoefficient035 p hp P hP s) := by
  exact actualOriginalIdealQuadraticPositiveTwoPhi_originalCoefficient035 p hp P hP s

theorem actualOriginalIdealQuadraticPositiveTwoPhi_native_coefficient
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
    actualCubicPositiveTwoOriginalNativePointFiberEquiv p hp
      ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization
        (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s) =
      actualResidueDifferentialDerivation (K := K) (R := R) (L := L)
        (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s) := by
  intro C R L
  have hCoefficient := actualOriginalIdealQuadraticPositiveTwoPhi_sourceSingleDelta041 p hp P hP s
  have hResidueRing := actualOriginalIdealQuadraticPositiveTwoPhi_stored_rawRing026 p hp P hP s
  ideal_phi_chart_exact023 hCoefficient using hResidueRing


end PfaffianDescent
