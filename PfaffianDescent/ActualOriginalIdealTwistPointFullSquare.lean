import PfaffianDescent.ActualOriginalIdealTwistPointBasisSquare
import PfaffianDescent.ActualPointLocalNativeOpenChartAction
import PfaffianDescent.ActualAffineConormalNativeSectionClass

import Mathlib.LinearAlgebra.TensorProduct.Tower

namespace CasselsFullTensor143
open scoped TensorProduct

/-- The unit pure tensors generate the scalar extension as an L-module,
so their preimages under an actual linear equivalence determine a map. -/
private theorem linearMap_eq_of_tensorUnitGenerators
    {R L M V W : Type*} [CommSemiring R] [Semiring L] [Algebra R L]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid V] [Module L V] [AddCommMonoid W] [Module L W]
    (E : V ≃ₗ[L] L ⊗[R] M) (A B : V →ₗ[L] W)
    (h : ∀ x : M, A (E.symm ((1 : L) ⊗ₜ[R] x)) =
      B (E.symm ((1 : L) ⊗ₜ[R] x))) : A = B := by
  have hall : ∀ t : L ⊗[R] M, A (E.symm t) = B (E.symm t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x =>
      have ht : a ⊗ₜ[R] x = a • ((1 : L) ⊗ₜ[R] x) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht, E.symm.map_smul, A.map_smul, B.map_smul, h]
    | add t s ht hs => simp only [map_add, ht, hs]
  apply LinearMap.ext
  intro v
  simpa only [E.symm_apply_apply] using hall (E v)

end CasselsFullTensor143

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

meta section
open Lean Meta Elab Tactic

elab "basis_full_exact142 " supplied:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← Term.elabTerm supplied none (catchExPostpone := false)
    Term.synthesizeSyntheticMVarsNoPostponing
    let source ← instantiateMVars source
    let sourceType ← instantiateMVars (← inferType source)
    let target ← instantiateMVars (← goal.getType)
    if source.hasMVar || source.hasLevelMVar || source.hasLooseBVars || source.hasSorry then
      throwError "Full142 source flags: expression metavariables={source.hasMVar}, level metavariables={source.hasLevelMVar}, loose variables={source.hasLooseBVars}, recovery={source.hasSorry}."
    let (heq, state) ←
      (CasselsFullStructural142.structuralHEq sourceType target
        96 #[] "full142").run {}
    let typeProof ← mkEqOfHEq heq
    let proof := mkAppN (mkConst ``Eq.mp [Level.zero])
      #[sourceType, target, typeProof, source]
    -- Builders can assign fresh expression/universe metavariables after the
    -- input expressions were instantiated. Resolve assigned values once more,
    -- then reject anything still unresolved or a recovery expression.
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "Full142 emitted flags: expression metavariables={proof.hasMVar}, level metavariables={proof.hasLevelMVar}, loose variables={proof.hasLooseBVars}, recovery={proof.hasSorry}."
    logInfo m!"Full142 ordinary exact compatibility emitted: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruence steps={state.congrSteps}, binders={state.binderSteps}, unused traversal budget={state.remaining}."
    goal.assign proof
    replaceMainGoal []

end

meta section
namespace CasselsFullTensor144
open Lean Meta Elab Term

private def diagnosticHead144 (e : Expr) : String :=
  let e := e.consumeMData
  let head := match e.getAppFn with
    | .const name _ => s!"constant {name}"
    | .fvar id => s!"local {id.name}"
    | .proj name index _ => s!"projection {name}[{index}]"
    | .forallE .. => "forall"
    | .lam .. => "lambda"
    | _ => "other"
  s!"{head}; arguments={e.getAppArgs.size}"

private def clean144 (e : Expr) (label : String) : MetaM Expr := do
  let e ← instantiateMVars e
  if e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
    throwError "Tensor144 {label} contains unresolved or recovery expressions."
  return e

private def storedType144 (e : Expr) (name : Name) (arity : Nat) : MetaM Expr := do
  let ty ← CasselsFullStructural142.normalizeHead (← inferType e) 8
  unless ty.getAppFn.isConstOf name && ty.getAppArgs.size == arity do
    throwError "Tensor144 expected stored {name}/{arity}, got {diagnosticHead144 ty}."
  clean144 ty "stored type"

/- Recover a stronger class from the already stored subclass projection spine.
No geometric value is unfolded. This only selects an existing expression; the
ordinary enclosing declaration checks every parameter and class argument. -/
private partial def ancestorClass144 (seed : Expr) (className : Name)
    (fuel : Nat) : MetaM Expr := do
  let seed ← clean144 seed "stored class"
  let ty ← CasselsFullStructural142.normalizeHead (← inferType seed) 8
  if ty.getAppFn.isConstOf className then return seed
  if fuel == 0 then
    throwError "Tensor144 could not recover stored {className} parent; type={diagnosticHead144 ty}."
  match seed.consumeMData with
  | .proj _ _ major => ancestorClass144 major className (fuel - 1)
  | .fvar id =>
    if let some value := (← id.getDecl).value? then
      ancestorClass144 value className (fuel - 1)
    else
      throwError "Tensor144 stored class has no {className} parent value."
  | .letE _ _ value body _ =>
    ancestorClass144 (body.instantiate1 value) className (fuel - 1)
  | e =>
    let args := e.getAppArgs
    if args.isEmpty then
      throwError "Tensor144 stored class has no {className} parent argument."
    ancestorClass144 args[args.size - 1]! className (fuel - 1)

private def typeUniverse144 (typeExpr : Expr) : MetaM Level := do
  let sort ← clean144 (← whnfD (← inferType typeExpr)) "carrier sort"
  let .sort level := sort
    | throwError "Tensor144 carrier does not have a stored sort."
  let some level := level.dec
    | throwError "Tensor144 helper carrier is not a Type."
  return level

/- Match the five Type* universe parameters by their actual declaration
binders, rather than assuming the order of autogenerated universe names. -/
private def helperConstant144 (carriers : Array Expr) : MetaM Expr := do
  let info ← getConstInfo ``CasselsFullTensor143.linearMap_eq_of_tensorUnitGenerators
  let mut formalType := info.type
  let mut universePairs : Array (Name × Level) := #[]
  for carrier in carriers do
    let .forallE _ (.sort (.succ (.param name))) body _ := formalType
      | throwError "Tensor144 generic helper's Type* telescope changed."
    universePairs := universePairs.push (name, ← typeUniverse144 carrier)
    formalType := body
  let mut levels : List Level := []
  for name in info.levelParams do
    let some pair := universePairs.find? (fun pair => pair.1 == name)
      | throwError "Tensor144 generic helper has an unexpected universe parameter."
    levels := levels ++ [pair.2]
  return mkConst info.name levels

elab "basisFullTensor144% " "(" suppliedEquiv:term ")"
    "(" suppliedA:term ")" "(" suppliedB:term ")"
    "(" suppliedGenerators:term ")" : term => do
  let equivalence ← Term.elabTerm suppliedEquiv none (catchExPostpone := false)
  let leftMap ← Term.elabTerm suppliedA none (catchExPostpone := false)
  let rightMap ← Term.elabTerm suppliedB none (catchExPostpone := false)
  let generators ← Term.elabTerm suppliedGenerators none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let equivalence ← clean144 equivalence "equivalence"
  let leftMap ← clean144 leftMap "left map"
  let rightMap ← clean144 rightMap "right map"
  let generators ← clean144 generators "generators"
  let equivalenceType ← storedType144 equivalence ``LinearEquiv 14
  let leftType ← storedType144 leftMap ``LinearMap 11
  let rightType ← storedType144 rightMap ``LinearMap 11
  let ea := equivalenceType.getAppArgs
  let la := leftType.getAppArgs
  let ra := rightType.getAppArgs
  let tensorType ← CasselsFullStructural142.normalizeHead ea[9]! 8
  unless tensorType.getAppFn.isConstOf ``TensorProduct && tensorType.getAppArgs.size == 8 do
    throwError "Tensor144 equivalence target is not the stored tensor product: {diagnosticHead144 tensorType}."
  let ta := tensorType.getAppArgs
  let generatorType ← CasselsFullStructural142.normalizeHead (← inferType generators) 8
  let .forallE _ generatorCarrier _ _ := generatorType
    | throwError "Tensor144 generator proof has no stored domain binder."
  let baseRing := ta[0]!
  let scalarRing := la[0]!
  let tensorGeneratorCarrier := ta[3]!
  let sourceCarrier := la[5]!
  let targetCarrier := la[6]!
  -- Use the actual minimum class vectors. No CommRing/AddCommGroup recovery
  -- or generator-group synthesis is needed by the private abstract proof.
  let baseCommSemiring := ta[1]!
  let scalarSemiring := la[2]!
  let generatorMonoid := ta[5]!
  let sourceMonoid := la[7]!
  let targetMonoid := la[8]!
  let algebra ← ancestorClass144 ta[6]! ``Algebra 8
  let helper ← helperConstant144
    #[baseRing, scalarRing, tensorGeneratorCarrier, sourceCarrier, targetCarrier]
  let helperPrefix := mkAppN helper
    #[baseRing, scalarRing, tensorGeneratorCarrier, sourceCarrier, targetCarrier,
      baseCommSemiring, scalarSemiring, algebra, generatorMonoid, ta[7]!,
      sourceMonoid, la[9]!, targetMonoid, la[10]!, equivalence, leftMap, rightMap]
  let prefixType ← CasselsFullStructural142.normalizeHead (← inferType helperPrefix) 8
  let .forallE _ expectedGenerators _ _ := prefixType
    | throwError "Tensor144 generic helper did not leave its generator-proof binder."
  logInfo m!"Tensor151 minimum stored vectors: E scalar={ea[0]!.equal scalarRing}, E source={ea[8]!.equal sourceCarrier}, tensor scalar={ta[2]!.equal scalarRing}, source generator domain={generatorCarrier.equal tensorGeneratorCarrier}, B scalar={ra[0]!.equal scalarRing}, B source={ra[5]!.equal sourceCarrier}, B target={ra[6]!.equal targetCarrier}, source E monoid/module={ea[10]!.equal sourceMonoid && ea[12]!.equal la[9]!}, generator proposition={generatorType.equal expectedGenerators}."
  let (heq, state) ←
    (CasselsFullStructural142.structuralHEq generatorType expectedGenerators
      96 #[] "tensorGenerators144").run {}
  let typeProof ← mkEqOfHEq heq
  let transportedGenerators := mkAppN (mkConst ``Eq.mp [Level.zero])
    #[generatorType, expectedGenerators, typeProof, generators]
  let proof := mkApp helperPrefix transportedGenerators
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← clean144 proof "ordinary helper application"
  logInfo m!"Tensor144 generator compatibility emitted: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruence steps={state.congrSteps}, binders={state.binderSteps}, unused traversal budget={state.remaining}."
  return proof

end CasselsFullTensor144
end


noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/- Ordinary Eq.trans with actual argument vectors supplied explicitly. -/
private theorem actualUntwistTrans138 {A : Sort u} {a b c : A}
    (h : a = b) (h' : b = c) : a = c := h.trans h'

meta section
open Lean Meta Elab Term

private def stripSpine138 : Expr → Expr
  | .mdata _ e => stripSpine138 e
  | .app f a => .app (stripSpine138 f) a
  | e => e

private partial def equationHead138 (e : Expr) (fuel : Nat) : MetaM Expr := do
  let e ← instantiateMVars e
  let e := stripSpine138 ((stripSpine138 e).headBeta)
  if fuel == 0 then return e
  match e with
  | .letE _ _ value body _ => equationHead138 (body.instantiate1 value) (fuel - 1)
  | _ =>
    if let .fvar id := e.getAppFn then
      if let some value := (← id.getDecl).value? then
        return ← equationHead138 (mkAppN value e.getAppArgs) (fuel - 1)
    if e.getAppFn.isConstOf ``id && e.getAppArgs.size == 2 then
      equationHead138 e.getAppArgs[1]! (fuel - 1)
    else return e

private def suppliedProof138 (stx : Syntax) : TermElabM Expr := do
  let proof ← Term.elabTerm stx none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "MappedUntwist138 refuses unresolved or recovery proof terms."
  return proof

private def ownEquation138 (proof : Expr) : MetaM (Expr × Expr × Expr) := do
  let ty ← equationHead138 (← inferType proof) 8
  let some (carrier,left,right) := ty.eq?
    | throwError "MappedUntwist138 expects an actual ordinary Eq proof."
  if ty.hasMVar || ty.hasLevelMVar then
    throwError "MappedUntwist138 unresolved equality vector."
  return (carrier,left,right)

elab "basisUntwistTrans138% " "(" first:term ")" "(" second:term ")" : term =>
    Term.withoutErrToSorry do
  let first ← suppliedProof138 first
  let second ← suppliedProof138 second
  let (carrier,left,middle) ← ownEquation138 first
  let (otherCarrier,otherMiddle,right) ← ownEquation138 second
  let level ← getLevel carrier
  let helper ← getConstInfo ``actualUntwistTrans138
  unless helper.levelParams.length == 1 do
    throwError "MappedUntwist138 abstract trans universe vector differs."
  let proof := mkAppN (mkConst helper.name [level])
    #[carrier,left,middle,right,first,second]
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "MappedUntwist138 unresolved/recovery trans term."
  logInfo m!"MappedUntwist138 ordinary own-vector trans: raw carrier={carrier.equal otherCarrier}, raw middle={middle.equal otherMiddle}."
  return proof

end

private theorem actualOriginalIdealTwistPointMappedAssociation139
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

private theorem actualOriginalIdealTwistPointLiteralClass138
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
      ((G.map ((actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
          (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
            ((Scheme.Modules.pullback q).obj T)
            (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom)) ≫
        G.map (actualOriginalUntwistedIdealPointChartIso p hp P hP).hom)
        (actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
          (actualModuleLocalTensorSection J T U m
            (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))) =
      G.map (actualOriginalUntwistedIdealPointChartIso p hp P hP).hom
        (
      G.map ((actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
        (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
          ((Scheme.Modules.pullback q).obj T)
          (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom)
        (actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
          (actualModuleLocalTensorSection J T U m
            (actualOriginalPositiveTwoLocalBasisSection p hp P hP U)))
        ) := by
  intro C I q J T f j U hU G m
  basis_structural_exact124
    (basisCompositionLaw115%
      (
      ((G.map ((actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
          (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
            ((Scheme.Modules.pullback q).obj T)
            (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom)) ≫
        G.map (actualOriginalUntwistedIdealPointChartIso p hp P hP).hom)
        (actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
          (actualModuleLocalTensorSection J T U m
            (actualOriginalPositiveTwoLocalBasisSection p hp P hP U)))
      ))

private theorem actualOriginalIdealTwistPointLiteralOuter138
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
      G.map (actualOriginalUntwistedIdealPointChartIso p hp P hP).hom
        (
      G.map ((actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
        (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
          ((Scheme.Modules.pullback q).obj T)
          (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom)
        (actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
          (actualModuleLocalTensorSection J T U m
            (actualOriginalPositiveTwoLocalBasisSection p hp P hP U)))
        ) =
      G.map (actualOriginalUntwistedIdealPointChartIso p hp P hP).hom
        (
      actualPointLocalSectionClass q J U hU m
        ) := by
  intro C I q J T f j U hU G m
  basis_structural_exact124
    (basisOuterContraction115%
      (
      G.map (actualOriginalUntwistedIdealPointChartIso p hp P hP).hom
        (
      G.map ((actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
        (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
          ((Scheme.Modules.pullback q).obj T)
          (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom)
        (actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
          (actualModuleLocalTensorSection J T U m
            (actualOriginalPositiveTwoLocalBasisSection p hp P hP U)))
        )
      )
      (actualOriginalIdealTwistPointUntwistContraction p hp P hP m))

private theorem actualOriginalIdealTwistPointAssociatedUntwist138
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
      ((G.map ((actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
          (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
            ((Scheme.Modules.pullback q).obj T)
            (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom)) ≫
        G.map (actualOriginalUntwistedIdealPointChartIso p hp P hP).hom)
        (actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
          (actualModuleLocalTensorSection J T U m
            (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))) =
      G.map (actualOriginalUntwistedIdealPointChartIso p hp P hP).hom
        (
      actualPointLocalSectionClass q J U hU m
        ) := by
  intro C I q J T f j U hU G m
  basis_structural_exact124
    (basisUntwistTrans138%
      (actualOriginalIdealTwistPointLiteralClass138 p hp P hP m)
      (actualOriginalIdealTwistPointLiteralOuter138 p hp P hP m))

lemma actualOriginalIdealTwistPointMappedUntwistContraction
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
      G.map (actualOriginalUntwistedIdealPointChartIso p hp P hP).hom
        (
      actualPointLocalSectionClass q J U hU m
        ) := by
  intro C I q J T f j U hU G m
  basis_structural_exact124
    (basisUntwistTrans138%
      (actualOriginalIdealTwistPointMappedAssociation139 p hp P hP m)
      (actualOriginalIdealTwistPointAssociatedUntwist138 p hp P hP m))

end PfaffianDescent
end

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false

/-- Transporting a top section back through the actual two chart isomorphisms
and then to the point recovers its original point section class. -/
private lemma actualPointLocalChartSourceFactorization_inverse_unitHom
    {L : Type u} [Field L] {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (j : Spec (.of L) ⟶ Y)
    (q : Spec (.of L) ⟶ X) (hfac : j ≫ f = q)
    (M : X.Modules) (N : Y.Modules)
    (e : (Scheme.Modules.restrictFunctor f).obj M ≅ N)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ N) :
    (moduleSpecΓFunctor (R := .of L)).map
      (actualModulePointChartSourceFactorizationIso f j q hfac M N e).hom
      (actualPointLocalSectionClass q M (f ''ᵁ ⊤)
        (actualFieldPointFactor_preimage_image_top f j q hfac)
        ((M.restrictAppIso f ⊤).hom
          (e.inv.val.app (op ⊤) (s.val.app (op ⊤) (1 : Γ(Y, ⊤)))))) =
      actualModulePointSectionClass j N s := by
  rw [actualPointLocalChartSourceFactorization_image_top]
  have hrestrict : (M.restrictAppIso f ⊤).inv
      ((M.restrictAppIso f ⊤).hom
        (e.inv.val.app (op ⊤) (s.val.app (op ⊤) (1 : Γ(Y, ⊤))))) =
      e.inv.val.app (op ⊤) (s.val.app (op ⊤) (1 : Γ(Y, ⊤))) :=
    ConcreteCategory.congr_hom (M.restrictAppIso f ⊤).hom_inv_id _
  have he : e.hom.val.app (op ⊤)
      (e.inv.val.app (op ⊤) (s.val.app (op ⊤) (1 : Γ(Y, ⊤)))) =
      s.val.app (op ⊤) (1 : Γ(Y, ⊤)) :=
    ConcreteCategory.congr_hom
      (congrArg (fun a => a.val.app (op (⊤ : Y.Opens))) e.inv_hom_id) _
  rw [hrestrict, he]
  exact actualPointLocalSectionClass_top_of_unitHom j N s


open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency.types false

private lemma actualOriginalUntwistedIdealPointNativeSection_root007
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let j := Spec.map (CommRingCat.ofHom C.residue)
    let f := chartι I C.index
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let J : (hypersurface p hp).Modules := closedImmersionModule q
    let Ji := closedImmersionModule j
    let U := f ''ᵁ (⊤ : (Spec (.of (ChartRing I C.index))).Opens)
    let hU := actualFieldPointFactor_preimage_image_top f j q C.factorization
    let e := actualOriginalNativeUntwistedIdealChartIso p hp P hP
    ∀ x : RingHom.ker C.residue,
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let zx := sx.val.app (op ⊤) (1 : Γ(Spec (.of (ChartRing I C.index)), ⊤))
    let m := (J.restrictAppIso f ⊤).hom (e.inv.val.app (op ⊤) zx)
    (moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))).map
      (actualOriginalUntwistedIdealPointChartIso p hp P hP).hom
      (actualPointLocalSectionClass q J U hU m) = actualModulePointSectionClass j Ji sx := by
  intro C I q j f J Ji U hU e x sx zx m
  unfold actualOriginalUntwistedIdealPointChartIso
  basis_structural_exact124
    (actualPointLocalChartSourceFactorization_inverse_unitHom f j q C.factorization J Ji e sx)

end PfaffianDescent
end

/- SOURCE ONLY / UNVERIFIED. FULL original ideal-twist point square,
derived from true local basis generators and actual affine ideal tensor
fiber generation. No original projective global-generation assumption or
desired tensor/ideal/source square certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma actualOriginalIdealTwistPointGeneratorSource159
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    let R := ChartRing I C.index
    letI : Algebra R L := C.residue.toAlgebra
    let Et := actualOriginalQuadraticConormalPointChartIso p hp P hP
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    let c := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom ≫ Ej.hom
    let E := (G.mapIso Et).toLinearEquiv.trans
      (actualAffineConormalTensorEquiv C.residue C.residue_surjective)
    let A := (G.map Et.hom).hom
    let B := (G.map c).hom
    ∀ x : RingHom.ker C.residue,
    let j := Spec.map (CommRingCat.ofHom C.residue)
    let f := chartι I C.index
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Ji := closedImmersionModule j
    let U := f ''ᵁ (⊤ : (Spec (.of R)).Opens)
    let hU := actualFieldPointFactor_preimage_image_top f j q C.factorization
    let e := actualOriginalNativeUntwistedIdealChartIso p hp P hP
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let zx := sx.val.app (op ⊤) (1 : Γ(Spec (.of R), ⊤))
    let m := ((show (hypersurface p hp).Modules from J).restrictAppIso f ⊤).hom
      (e.inv.val.app (op ⊤) zx)
    let w := actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
      (actualModuleLocalTensorSection J T U m
        (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))
    let u := actualPointLocalSectionClass q J U hU m
    G.map Ej.hom u = actualModulePointSectionClass j Ji sx := by
  intro I q J T G C L R Et Ej c E A B x j f Ji U hU e sx zx m w u
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  basis_full_exact142
    (actualOriginalUntwistedIdealPointNativeSection_root007 p hp P hP x)

private lemma actualOriginalIdealTwistPointGeneratorBasis159
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    let R := ChartRing I C.index
    letI : Algebra R L := C.residue.toAlgebra
    let Et := actualOriginalQuadraticConormalPointChartIso p hp P hP
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    let c := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom ≫ Ej.hom
    let E := (G.mapIso Et).toLinearEquiv.trans
      (actualAffineConormalTensorEquiv C.residue C.residue_surjective)
    let A := (G.map Et.hom).hom
    let B := (G.map c).hom
    ∀ x : RingHom.ker C.residue,
    let j := Spec.map (CommRingCat.ofHom C.residue)
    let f := chartι I C.index
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Ji := closedImmersionModule j
    let U := f ''ᵁ (⊤ : (Spec (.of R)).Opens)
    let hU := actualFieldPointFactor_preimage_image_top f j q C.factorization
    let e := actualOriginalNativeUntwistedIdealChartIso p hp P hP
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let zx := sx.val.app (op ⊤) (1 : Γ(Spec (.of R), ⊤))
    let m := ((show (hypersurface p hp).Modules from J).restrictAppIso f ⊤).hom
      (e.inv.val.app (op ⊤) zx)
    let w := actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
      (actualModuleLocalTensorSection J T U m
        (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))
    let u := actualPointLocalSectionClass q J U hU m
    A w = B w := by
  intro I q J T G C L R Et Ej c E A B x j f Ji U hU e sx zx m w u
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  basis_full_exact142
    (actualOriginalIdealTwistPointBasisSquare p hp P hP m)

private lemma actualOriginalIdealTwistPointGeneratorUntwist159
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    let R := ChartRing I C.index
    letI : Algebra R L := C.residue.toAlgebra
    let Et := actualOriginalQuadraticConormalPointChartIso p hp P hP
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    let c := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom ≫ Ej.hom
    let E := (G.mapIso Et).toLinearEquiv.trans
      (actualAffineConormalTensorEquiv C.residue C.residue_surjective)
    let A := (G.map Et.hom).hom
    let B := (G.map c).hom
    ∀ x : RingHom.ker C.residue,
    let j := Spec.map (CommRingCat.ofHom C.residue)
    let f := chartι I C.index
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Ji := closedImmersionModule j
    let U := f ''ᵁ (⊤ : (Spec (.of R)).Opens)
    let hU := actualFieldPointFactor_preimage_image_top f j q C.factorization
    let e := actualOriginalNativeUntwistedIdealChartIso p hp P hP
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let zx := sx.val.app (op ⊤) (1 : Γ(Spec (.of R), ⊤))
    let m := ((show (hypersurface p hp).Modules from J).restrictAppIso f ⊤).hom
      (e.inv.val.app (op ⊤) zx)
    let w := actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
      (actualModuleLocalTensorSection J T U m
        (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))
    let u := actualPointLocalSectionClass q J U hU m
    G.map c w = G.map Ej.hom u := by
  intro I q J T G C L R Et Ej c E A B x j f Ji U hU e sx zx m w u
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  basis_full_exact142
    (actualOriginalIdealTwistPointMappedUntwistContraction p hp P hP m)

/- Remove only the exact eleven local-let nodes retained in the checked
sibling result types. This is syntactic zeta substitution: no factory,
class vector, native wrapper or theorem body is unfolded. The cast below
is an ordinary Eq.mp whose equality is checked by the kernel. -/
meta section
open Lean Meta Elab Term

elab "basisGeneratorLetSpine160% " "(" supplied:term ")" : term => do
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let source ← instantiateMVars source
  if source.hasMVar || source.hasLevelMVar || source.hasLooseBVars || source.hasSorry then
    throwError "Generator160 source has unresolved or recovery expressions."
  let sourceType ← instantiateMVars (← inferType source)
  if sourceType.hasMVar || sourceType.hasLevelMVar || sourceType.hasLooseBVars then
    throwError "Generator160 source type has unresolved expressions."
  let mut resultType := sourceType.consumeMData
  for expectedName in #[`j, `f, `Ji, `U, `hU, `e, `sx, `zx, `m, `w, `u] do
    let .letE actualName _ value body _ := resultType
      | throwError "Generator160 expected the stored local let {expectedName}."
    unless actualName == expectedName do
      throwError "Generator160 expected local let {expectedName}, got {actualName}."
    resultType := (body.instantiate1 value).consumeMData
  if let .letE .. := resultType then
    throwError "Generator160 sibling result has an unexpected residual local let."
  let reflexivity ← mkEqRefl resultType
  let proof := mkAppN (mkConst ``Eq.mp [Level.zero])
    #[sourceType, resultType, reflexivity, source]
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "Generator160 emitted unresolved or recovery expressions."
  logInfo "Generator160 exact sibling local-let spine substituted; ordinary Eq.mp cast emitted."
  return proof

end

private lemma actualOriginalIdealTwistPointGeneratorUntwistedTensorImage161
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    let R := ChartRing I C.index
    letI : Algebra R L := C.residue.toAlgebra
    let Et := actualOriginalQuadraticConormalPointChartIso p hp P hP
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    let c := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom ≫ Ej.hom
    let E := (G.mapIso Et).toLinearEquiv.trans
      (actualAffineConormalTensorEquiv C.residue C.residue_surjective)
    let A := (G.map Et.hom).hom
    let B := (G.map c).hom
    ∀ x : RingHom.ker C.residue,
    let j := Spec.map (CommRingCat.ofHom C.residue)
    let f := chartι I C.index
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Ji := closedImmersionModule j
    let U := f ''ᵁ (⊤ : (Spec (.of R)).Opens)
    let hU := actualFieldPointFactor_preimage_image_top f j q C.factorization
    let e := actualOriginalNativeUntwistedIdealChartIso p hp P hP
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let zx := sx.val.app (op ⊤) (1 : Γ(Spec (.of R), ⊤))
    let m := ((show (hypersurface p hp).Modules from J).restrictAppIso f ⊤).hom
      (e.inv.val.app (op ⊤) zx)
    let w := actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
      (actualModuleLocalTensorSection J T U m
        (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))
    let u := actualPointLocalSectionClass q J U hU m
    actualAffineConormalTensorEquiv C.residue C.residue_surjective (G.map Ej.hom u) = (1 : L) ⊗ₜ[R] x := by
  intro I q J T G C L R Et Ej c E A B x j f Ji U hU e sx zx m w u
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  have hSource : G.map Ej.hom u = actualModulePointSectionClass j Ji sx := by
    basis_full_exact142
      (basisGeneratorLetSpine160%
        (actualOriginalIdealTwistPointGeneratorSource159 p hp P hP x))
  rw [hSource, actualAffineConormalTensorEquiv_nativeSection]

private lemma actualOriginalIdealTwistPointGeneratorMappedTensorImage161
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    let R := ChartRing I C.index
    letI : Algebra R L := C.residue.toAlgebra
    let Et := actualOriginalQuadraticConormalPointChartIso p hp P hP
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    let c := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom ≫ Ej.hom
    let E := (G.mapIso Et).toLinearEquiv.trans
      (actualAffineConormalTensorEquiv C.residue C.residue_surjective)
    let A := (G.map Et.hom).hom
    let B := (G.map c).hom
    ∀ x : RingHom.ker C.residue,
    let j := Spec.map (CommRingCat.ofHom C.residue)
    let f := chartι I C.index
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Ji := closedImmersionModule j
    let U := f ''ᵁ (⊤ : (Spec (.of R)).Opens)
    let hU := actualFieldPointFactor_preimage_image_top f j q C.factorization
    let e := actualOriginalNativeUntwistedIdealChartIso p hp P hP
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let zx := sx.val.app (op ⊤) (1 : Γ(Spec (.of R), ⊤))
    let m := ((show (hypersurface p hp).Modules from J).restrictAppIso f ⊤).hom
      (e.inv.val.app (op ⊤) zx)
    let w := actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
      (actualModuleLocalTensorSection J T U m
        (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))
    let u := actualPointLocalSectionClass q J U hU m
    actualAffineConormalTensorEquiv C.residue C.residue_surjective (G.map c w) = (1 : L) ⊗ₜ[R] x := by
  intro I q J T G C L R Et Ej c E A B x j f Ji U hU e sx zx m w u
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  have hUntwist : G.map c w = G.map Ej.hom u := by
    basis_full_exact142
      (basisGeneratorLetSpine160%
        (actualOriginalIdealTwistPointGeneratorUntwist159 p hp P hP x))
  rw [hUntwist]
  basis_full_exact142
    (basisGeneratorLetSpine160%
      (actualOriginalIdealTwistPointGeneratorUntwistedTensorImage161 p hp P hP x))

/-- Equality at a vector and its image transports through a linear equivalence.
This proof is checked over abstract module vectors, with no geometric objects. -/
private theorem actualGeneratorPreimageTransport162
    {L V W Z : Type*} [Semiring L]
    [AddCommMonoid V] [Module L V]
    [AddCommMonoid W] [Module L W]
    [AddCommMonoid Z] [Module L Z]
    (E : V ≃ₗ[L] Z) (A B : V →ₗ[L] W) (w : V) (t : Z)
    (hBasis : A w = B w) (hImage : E w = t) :
    A (E.symm t) = B (E.symm t) := by
  rw [← hImage, E.symm_apply_apply]
  exact hBasis

private lemma actualOriginalIdealTwistPointGeneratorEquivImage162
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    let R := ChartRing I C.index
    letI : Algebra R L := C.residue.toAlgebra
    let Et := actualOriginalQuadraticConormalPointChartIso p hp P hP
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    let c := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom ≫ Ej.hom
    let E := (G.mapIso Et).toLinearEquiv.trans
      (actualAffineConormalTensorEquiv C.residue C.residue_surjective)
    let A := (G.map Et.hom).hom
    let B := (G.map c).hom
    ∀ x : RingHom.ker C.residue,
    let j := Spec.map (CommRingCat.ofHom C.residue)
    let f := chartι I C.index
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Ji := closedImmersionModule j
    let U := f ''ᵁ (⊤ : (Spec (.of R)).Opens)
    let hU := actualFieldPointFactor_preimage_image_top f j q C.factorization
    let e := actualOriginalNativeUntwistedIdealChartIso p hp P hP
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let zx := sx.val.app (op ⊤) (1 : Γ(Spec (.of R), ⊤))
    let m := ((show (hypersurface p hp).Modules from J).restrictAppIso f ⊤).hom
      (e.inv.val.app (op ⊤) zx)
    let w := actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
      (actualModuleLocalTensorSection J T U m
        (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))
    let u := actualPointLocalSectionClass q J U hU m
    E w = (1 : L) ⊗ₜ[R] x := by
  intro I q J T G C L R Et Ej c E A B x j f Ji U hU e sx zx m w u
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  have hBasis : A w = B w := by
    basis_full_exact142
      (basisGeneratorLetSpine160%
        (actualOriginalIdealTwistPointGeneratorBasis159 p hp P hP x))
  change actualAffineConormalTensorEquiv C.residue C.residue_surjective (A w) = _
  rw [hBasis]
  change actualAffineConormalTensorEquiv C.residue C.residue_surjective
    (G.map c w) = _
  basis_full_exact142
    (basisGeneratorLetSpine160%
      (actualOriginalIdealTwistPointGeneratorMappedTensorImage161 p hp P hP x))

/- Apply the small abstract transport theorem using the class vectors
already stored in the actual equivalence and maps. No native class synthesis
or geometric factory unfolding is needed to construct this application. -/
meta section
namespace CasselsFullPreimage162
open Lean Meta Elab Term

private def clean162 (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
    throwError "Preimage162 found unresolved or recovery expressions."
  return e

private def stored162 (e : Expr) (name : Name) (arity : Nat) : MetaM Expr := do
  let ty ← CasselsFullStructural142.normalizeHead (← inferType e) 8
  unless ty.getAppFn.isConstOf name && ty.getAppArgs.size == arity do
    throwError "Preimage162 expected the stored {name}/{arity} type."
  clean162 ty

private def universe162 (carrier : Expr) : MetaM Level := do
  let sort ← clean162 (← whnfD (← inferType carrier))
  let .sort level := sort
    | throwError "Preimage162 carrier has no stored sort."
  let some level := level.dec
    | throwError "Preimage162 carrier is not a Type."
  return level

private def helper162 (carriers : Array Expr) : MetaM Expr := do
  let info ← getConstInfo ``PfaffianDescent.actualGeneratorPreimageTransport162
  let mut formal := info.type
  let mut pairs : Array (Name × Level) := #[]
  for carrier in carriers do
    let .forallE _ (.sort (.succ (.param name))) body _ := formal
      | throwError "Preimage162 abstract Type telescope changed."
    pairs := pairs.push (name, ← universe162 carrier)
    formal := body
  let mut levels : List Level := []
  for name in info.levelParams do
    let some pair := pairs.find? (fun pair => pair.1 == name)
      | throwError "Preimage162 unexpected abstract universe."
    levels := levels ++ [pair.2]
  return mkConst info.name levels

private def transport162 (proof expected : Expr) (label : String) : MetaM Expr := do
  let actual ← clean162 (← inferType proof)
  let (heq, state) ←
    (CasselsFullStructural142.structuralHEq actual expected
      96 #[] ("preimage162." ++ label)).run {}
  let equality ← mkEqOfHEq heq
  logInfo m!"Preimage162 {label} compatibility: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, congruence steps={state.congrSteps}, binders={state.binderSteps}."
  clean162 (mkAppN (mkConst ``Eq.mp [Level.zero]) #[actual, expected, equality, proof])

elab "basisPreimageTransport162% " "(" suppliedE:term ")"
    "(" suppliedA:term ")" "(" suppliedB:term ")"
    "(" suppliedW:term ")" "(" suppliedT:term ")"
    "(" suppliedBasis:term ")" "(" suppliedImage:term ")" : term => do
  let equivalence ← Term.elabTerm suppliedE none (catchExPostpone := false)
  let left ← Term.elabTerm suppliedA none (catchExPostpone := false)
  let right ← Term.elabTerm suppliedB none (catchExPostpone := false)
  let w ← Term.elabTerm suppliedW none (catchExPostpone := false)
  let t ← Term.elabTerm suppliedT none (catchExPostpone := false)
  let basis ← Term.elabTerm suppliedBasis none (catchExPostpone := false)
  let image ← Term.elabTerm suppliedImage none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let equivalence ← clean162 equivalence
  let left ← clean162 left
  let right ← clean162 right
  let w ← clean162 w
  let t ← clean162 t
  let basis ← clean162 basis
  let image ← clean162 image
  let et ← stored162 equivalence ``LinearEquiv 14
  let leftType162 ← stored162 left ``LinearMap 11
  let bt ← stored162 right ``LinearMap 11
  let ea := et.getAppArgs
  let aa := leftType162.getAppArgs
  let ba := bt.getAppArgs
  let helper ← helper162 #[aa[0]!, aa[5]!, aa[6]!, ea[9]!]
  let transportApplication162 := mkAppN helper
    #[aa[0]!, aa[5]!, aa[6]!, ea[9]!, aa[2]!,
      aa[7]!, aa[9]!, aa[8]!, aa[10]!, ea[11]!, ea[13]!,
      equivalence, left, right, w, t]
  let basisBinder ← CasselsFullStructural142.normalizeHead (← inferType transportApplication162) 8
  let .forallE _ expectedBasis _ _ := basisBinder
    | throwError "Preimage162 missing abstract basis equality binder."
  let basis ← transport162 basis expectedBasis "basis"
  let withBasis := mkApp transportApplication162 basis
  let imageBinder ← CasselsFullStructural142.normalizeHead (← inferType withBasis) 8
  let .forallE _ expectedImage _ _ := imageBinder
    | throwError "Preimage162 missing abstract image equality binder."
  let image ← transport162 image expectedImage "image"
  logInfo m!"Preimage162 stored vectors: E scalar={ea[0]!.equal aa[0]!}, E semiring={ea[2]!.equal aa[2]!}, E source monoid/module={ea[10]!.equal aa[7]! && ea[12]!.equal aa[9]!}, B scalar/source/target={ba[0]!.equal aa[0]! && ba[5]!.equal aa[5]! && ba[6]!.equal aa[6]!}."
  Term.synthesizeSyntheticMVarsNoPostponing
  clean162 (mkApp withBasis image)

end CasselsFullPreimage162
end

private lemma actualOriginalIdealTwistPointUnitGenerators156
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let L := (hypersurface p hp).residueField P.1
    let R := ChartRing I C.index
    letI : Algebra R L := C.residue.toAlgebra
    let Et := actualOriginalQuadraticConormalPointChartIso p hp P hP
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    let c := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom ≫ Ej.hom
    let E := (G.mapIso Et).toLinearEquiv.trans
      (actualAffineConormalTensorEquiv C.residue C.residue_surjective)
    let A := (G.map Et.hom).hom
    let B := (G.map c).hom
    ∀ x : RingHom.ker C.residue,
      A (E.symm ((1 : L) ⊗ₜ[R] x)) = B (E.symm ((1 : L) ⊗ₜ[R] x)) := by
  intro I q J T G C L R Et Ej c E A B x
  letI : Algebra R L := C.residue.toAlgebra
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  let Ji := closedImmersionModule j
  let U := f ''ᵁ (⊤ : (Spec (.of R)).Opens)
  let hU := actualFieldPointFactor_preimage_image_top f j q C.factorization
  let e := actualOriginalNativeUntwistedIdealChartIso p hp P hP
  let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
  let zx := sx.val.app (op ⊤) (1 : Γ(Spec (.of R), ⊤))
  let m := ((show (hypersurface p hp).Modules from J).restrictAppIso f ⊤).hom
    (e.inv.val.app (op ⊤) zx)
  let w := actualPointLocalSectionClass q (schemeModuleTensor J T) U hU
    (actualModuleLocalTensorSection J T U m
      (actualOriginalPositiveTwoLocalBasisSection p hp P hP U))
  let u := actualPointLocalSectionClass q J U hU m
  have hBasis : A w = B w := by
    basis_full_exact142
      (basisGeneratorLetSpine160%
        (actualOriginalIdealTwistPointGeneratorBasis159 p hp P hP x))
  have hE : E w = (1 : L) ⊗ₜ[R] x := by
    basis_full_exact142
      (basisGeneratorLetSpine160%
        (actualOriginalIdealTwistPointGeneratorEquivImage162 p hp P hP x))
  basis_full_exact142
    (basisPreimageTransport162% (E) (A) (B) (w) ((1 : L) ⊗ₜ[R] x)
      (hBasis) (hE))

lemma actualOriginalIdealTwistPointFullSquare
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))
    (G.map (actualOriginalQuadraticConormalPointChartIso p hp P hP).hom).hom =
    (G.map ((actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom ≫
      (actualOriginalUntwistedIdealPointChartIso p hp P hP).hom)).hom := by
  intro I q J T G
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  let L := (hypersurface p hp).residueField P.1
  let R := ChartRing I C.index
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  let Ji := closedImmersionModule j
  let U := f ''ᵁ (⊤ : (Spec (.of R)).Opens)
  let hU := actualFieldPointFactor_preimage_image_top f j q C.factorization
  let Et := actualOriginalQuadraticConormalPointChartIso p hp P hP
  let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
  let e := actualOriginalNativeUntwistedIdealChartIso p hp P hP
  let c := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
    (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
      ((Scheme.Modules.pullback q).obj T)
      (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom ≫ Ej.hom
  let E := (G.mapIso Et).toLinearEquiv.trans
    (actualAffineConormalTensorEquiv C.residue C.residue_surjective)
  let A := (G.map Et.hom).hom
  let B := (G.map c).hom
  have hGenerators : ∀ x : RingHom.ker C.residue,
      A (E.symm ((1 : L) ⊗ₜ[R] x)) = B (E.symm ((1 : L) ⊗ₜ[R] x)) := by
    basis_full_exact142
      (fun x : RingHom.ker C.residue =>
        actualOriginalIdealTwistPointUnitGenerators156 p hp P hP x)
  basis_full_exact142
    (basisFullTensor144% (E) (A) (B) (hGenerators))

end PfaffianDescent
end
