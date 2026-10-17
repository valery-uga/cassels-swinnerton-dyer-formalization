import PfaffianDescent.ActualOriginalIdealTwistPointFullSquare
import PfaffianDescent.ActualOriginalIdealChartTransportEquality
import PfaffianDescent.ActualOriginalPositiveTwoContractedNativeDifferentialMap
import PfaffianDescent.ActualOriginalGlobalCanonicalQuadraticPhiContraction
import PfaffianDescent.ActualOriginalGlobalConormalKaehlerComparison
import PfaffianDescent.ActualResidueDifferentialLeibnizBalance
import PfaffianDescent.ActualOriginalIdealQuadraticNativeRestriction

/- SOURCE ONLY / UNVERIFIED. The genuinely GLOBAL, chart-free Phi has
its literal native quadratic differential coefficient under the actual
original O2 contraction/open-chart/Kaehler chain. All source/ideal/map
comparisons are derived internally; no desired Phi equality premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

private lemma actualOriginalGlobalPhiNativeSectionHeader004
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let Etw := actualOriginalQuadraticConormalPointChartIso p hp P hP
    let x : RingHom.ker C.residue :=
      ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    G.map Etw.hom z = actualModulePointSectionClass j (closedImmersionModule j) sx := by
  exact actualOriginalQuadraticConormalPointChartIso_section p hp P hP s

universe v w

/-- Evaluate a mapped composite before specializing any native module/category vector. -/
private theorem actualGlobalPhiMappedCompositeSection007
    {R : Type u} [Ring R] {A : Type v} [Category.{w} A]
    (G : A ⥤ ModuleCat.{u} R) {X Y Z : A}
    (f : X ⟶ Y) (g : Y ⟶ Z) (z : G.obj X) (t : G.obj Z)
    (h : G.map (f ≫ g) z = t) :
    G.map g (G.map f z) = t := by
  simpa only [Functor.map_comp, ModuleCat.comp_apply] using h

meta section
open Lean Meta Elab Term

/-- Infer the proof on its own stored vector, without a native expected proposition. -/
elab "phi_native_infer010% " supplied:term : term => do
  let proof ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "PhiNative010 unresolved or recovery proof."
  return proof

end

private lemma actualOriginalGlobalPhiNativeFullSquareInferred010
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_infer010% (let I := equationIdeal p hp
      let q := (hypersurface p hp).fromSpecResidueField P.1
      letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let T := positiveSheafOfModules (grading I) 2
      let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
        (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
      congrArg (fun F => F z) (actualOriginalIdealTwistPointFullSquare p hp P hP))) :=
  phi_native_infer010% (let I := equationIdeal p hp
      let q := (hypersurface p hp).fromSpecResidueField P.1
      letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let T := positiveSheafOfModules (grading I) 2
      let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
        (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
      congrArg (fun F => F z) (actualOriginalIdealTwistPointFullSquare p hp P hP))

/-- The SAME canonical bundled-ring structure roundtrip, without a field projection. -/
private theorem phiNativeCanonicalBundle013 (R : CommRingCat.{u}) :
    @CommRingCat.of (CommRingCat.carrier R)
      (@CommRingCat.instCommRingObjForgetRingHomCarrier R) = R := by
  rfl

private theorem actualOriginalPhiNativeResidueBundle013
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp)) :
    @CommRingCat.of
      (CommRingCat.carrier ((hypersurface p hp).residueField P.1))
      (@CommRingCat.instCommRingObjForgetRingHomCarrier
        ((hypersurface p hp).residueField P.1)) =
      (hypersurface p hp).residueField P.1 := by
  exact phiNativeCanonicalBundle013 ((hypersurface p hp).residueField P.1)

/-- Equality of the SAME module-hom accessor, on its original stored vector. -/
private theorem phiNativeHomProjection015.{vAccessor015, uAccessor015}
    {R : Type uAccessor015} [Ring R] {M N : ModuleCat.{vAccessor015} R}
    (f : ModuleCat.Hom M N) :
    f.hom = ConcreteCategory.hom (C := ModuleCat.{vAccessor015} R) f := by
  rfl

meta section
open Lean Meta Elab Term

/-- Apply the ordinary accessor law using exactly the passed source's hom5
vector and universe order, never infer replacement native instances. -/
elab "phi_native_accessor015% " side:num supplied:term : term => do
  unless side.getNat < 2 do
    throwError "NativeAccessor015 expected side0 or1."
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let source ← instantiateMVars source
  let proposition := (← whnf (← inferType source)).consumeMData.headBeta
  let some (_, sourceLeft, sourceRight) := proposition.eq?
    | throwError "NativeAccessor015 expected passed source's exact Eq proposition."
  let endpoint := (if side.getNat == 0 then sourceLeft else sourceRight).consumeMData.headBeta
  let endpointArgs := endpoint.getAppArgs
  unless endpoint.getAppFn.isConstOf ``DFunLike.coe && endpointArgs.size == 6 do
    throwError "NativeAccessor015 expected actual stored function application6."
  let accessor := endpointArgs[4]!.consumeMData.headBeta
  let args := accessor.getAppArgs
  unless accessor.getAppFn.isConstOf ``ModuleCat.Hom.hom && args.size == 5 do
    throwError "NativeAccessor015 expected actual stored ModuleCat.Hom.hom5."
  let .const _ levels := accessor.getAppFn
    | throwError "NativeAccessor015 expected exact stored accessor universe vector."
  let accessorInfo ← getConstInfo ``ModuleCat.Hom.hom
  let lawInfo ← getConstInfo ``phiNativeHomProjection015
  unless accessorInfo.levelParams.length == 2 && lawInfo.levelParams.length == 2 &&
      levels.length == 2 do
    throwError "NativeAccessor015 expected exactly the two stored accessor/law universes."
  -- Alpha-renamed universes are compared by their SAME ordered canonical vector.
  let canonicalLevels := [Level.param `phiNativeAccessorObjectCanonical015,
    Level.param `phiNativeAccessorRingCanonical015]
  let mut accessorType := accessorInfo.type.instantiateLevelParams
    accessorInfo.levelParams canonicalLevels
  let mut lawType := lawInfo.type.instantiateLevelParams
    lawInfo.levelParams canonicalLevels
  for i in [:5] do
    let .forallE _ accessorDomain accessorBody accessorBinder := accessorType
      | throwError "NativeAccessor015 missing accessor prefix binder."
    let .forallE _ lawDomain lawBody lawBinder := lawType
      | throwError "NativeAccessor015 missing law prefix binder."
    unless accessorDomain.equal lawDomain && accessorBinder == lawBinder do
      throwError "NativeAccessor015 refused different exact prefix binder at {i}."
    accessorType := accessorBody
    lawType := lawBody
  let proof ← instantiateMVars (mkAppN (mkConst ``phiNativeHomProjection015 levels) args)
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeAccessor015 unresolved/recovery ordinary stored-vector law."
  logInfo m!"NativeAccessor015 side{side.getNat}: exact hom5 law emitted with stored universes and declaration-prefix guard."
  return proof

end

private lemma actualOriginalGlobalPhiNativeLeftAccessor015
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_accessor015% 0 (actualOriginalGlobalPhiNativeFullSquareInferred010 p hp P hP s)) :=
  phi_native_accessor015% 0 (actualOriginalGlobalPhiNativeFullSquareInferred010 p hp P hP s)

private lemma actualOriginalGlobalPhiNativeRightAccessor015
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_accessor015% 1 (actualOriginalGlobalPhiNativeFullSquareInferred010 p hp P hP s)) :=
  phi_native_accessor015% 1 (actualOriginalGlobalPhiNativeFullSquareInferred010 p hp P hP s)

/-- The literal native010 header expression, with its original maps/actions;
no desired proof premise or alternate scalar structure. -/
private def actualOriginalGlobalPhiNativeHeaderProposition016
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) : Prop :=
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let Etw := actualOriginalQuadraticConormalPointChartIso p hp P hP
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    G.map Etw.hom z = G.map (cJ ≫ Ej.hom) z

meta section
open Lean Meta Elab Term

/-- Read only the actual Eq carrier from a proof TYPE or proposition expression. -/
elab "phi_native_eq_carrier016% " mode:num supplied:term : term => do
  unless mode.getNat < 2 do
    throwError "NativeCarrier016 expected proof-type0 or proposition1."
  let supplied ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let supplied ← instantiateMVars supplied
  if supplied.hasMVar || supplied.hasLevelMVar || supplied.hasLooseBVars || supplied.hasSorry then
    throwError "NativeCarrier016 unresolved/recovery source."
  let proposition ← if mode.getNat == 0 then inferType supplied else pure supplied
  let proposition := (← whnf proposition).consumeMData.headBeta
  let some (carrier, _, _) := proposition.eq?
    | throwError "NativeCarrier016 expected the exact stored outer Eq."
  return carrier

end

private theorem actualOriginalGlobalPhiNativeCarrierHEq016
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    HEq (phi_native_eq_carrier016% 0
      (actualOriginalGlobalPhiNativeFullSquareInferred010 p hp P hP s))
      (phi_native_eq_carrier016% 1
        (actualOriginalGlobalPhiNativeHeaderProposition016 p hp P hP s)) := by
  rfl


meta section
open Lean Meta Elab Term

/-- Read an actual stored Eq endpoint from the own proof TYPE or literal
native proposition; no expected native endpoint or map reconstruction. -/
elab "phi_native_eq_endpoint017% " mode:num side:num supplied:term : term => do
  unless mode.getNat < 2 && side.getNat < 2 do
    throwError "NativeEndpoint017 expected mode0/1 and side0/1."
  let supplied ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let supplied ← instantiateMVars supplied
  if supplied.hasMVar || supplied.hasLevelMVar || supplied.hasLooseBVars || supplied.hasSorry then
    throwError "NativeEndpoint017 unresolved/recovery source."
  let proposition ← if mode.getNat == 0 then inferType supplied else pure supplied
  let proposition := (← whnf proposition).consumeMData.headBeta
  let some (_, left, right) := proposition.eq?
    | throwError "NativeEndpoint017 expected the exact stored outer Eq."
  return if side.getNat == 0 then left else right

end

/-- Associativity under the SAME mapped section, before native specialization. -/
private theorem phiNativeMappedTripleAssociation018.{uAssoc018, vAssoc018, wAssoc018}
    {R : Type uAssoc018} [Ring R] {A : Type vAssoc018} [Category.{wAssoc018} A]
    (G : A ⥤ ModuleCat.{uAssoc018} R) {W X Y Z : A}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (z : G.obj W) :
    G.map ((f ≫ g) ≫ h) z = G.map (f ≫ (g ≫ h)) z := by
  rw [Category.assoc]

meta section
open Lean Meta Elab Term

private def phiNativeStoredEq018 (input : Expr) : Term.TermElabM (Expr × Expr × Expr) := do
  let proposition := (← whnf (← inferType input)).consumeMData.headBeta
  let some parts := proposition.eq?
    | throwError "Native018 expected exact stored Eq proof type."
  return parts

/-- Apply PASSED accessor015 to the SAME stored DFunLike.coe6 section vector.
The evaluation lambda and congrArg's complete vector are constructed explicitly. -/
elab "phi_native_accessor_point018% " side:num supplied:term " using " law:term : term => do
  unless side.getNat < 2 do
    throwError "NativeAccessorPoint018 expected side0/1."
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  let law ← Term.elabTerm law none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let source ← instantiateMVars source
  let law ← instantiateMVars law
  let (_, sourceLeft, sourceRight) ← phiNativeStoredEq018 source
  let endpoint := (if side.getNat == 0 then sourceLeft else sourceRight).consumeMData.headBeta
  let args := endpoint.getAppArgs
  unless endpoint.getAppFn.isConstOf ``DFunLike.coe && args.size == 6 do
    throwError "NativeAccessorPoint018 expected original endpoint application6."
  let (accessorType, accessorLeft, accessorRight) ← phiNativeStoredEq018 law
  unless accessorType.consumeMData.equal args[0]!.consumeMData &&
      accessorLeft.consumeMData.equal args[4]!.consumeMData do
    throwError "NativeAccessorPoint018 refused different stored accessor type or value."
  let resultType ← inferType endpoint
  let evaluator ← withLocalDeclD `accessor accessorType fun accessor => do
    mkLambdaFVars #[accessor] (mkAppN endpoint.getAppFn (args.set! 4 accessor))
  let sourceLevel ← getLevel accessorType
  let resultLevel ← getLevel resultType
  let proof := mkAppN (mkConst ``congrArg [sourceLevel, resultLevel])
    #[accessorType, resultType, accessorLeft, accessorRight, evaluator, law]
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeAccessorPoint018 unresolved/recovery exact stored evaluation."
  logInfo m!"NativeAccessorPoint018 side{side.getNat}: ordinary congrArg from exact stored coe6/equality vector."
  return proof

/-- Read native Prop016's actual RHS functor/accessor/comp vectors and apply
ordinary mapped associativity with every argument supplied explicitly. -/
elab "phi_native_stored_association018% " supplied:term : term => do
  let proposition ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let proposition ← instantiateMVars proposition
  let proposition := (← whnf proposition).consumeMData.headBeta
  let some (_, _, endpoint) := proposition.eq?
    | throwError "NativeAssociation018 expected literal native Eq proposition."
  let endpoint := endpoint.consumeMData.headBeta
  let ea := endpoint.getAppArgs
  unless endpoint.getAppFn.isConstOf ``DFunLike.coe && ea.size == 6 do
    throwError "NativeAssociation018 expected native coe6 endpoint."
  let accessor := ea[4]!.consumeMData.headBeta
  let ha := accessor.getAppArgs
  unless accessor.getAppFn.isConstOf ``CategoryTheory.ConcreteCategory.hom && ha.size == 9 do
    throwError "NativeAssociation018 expected exact native concrete accessor9."
  let moduleType := ha[0]!.consumeMData.headBeta
  let ringArgs := moduleType.getAppArgs
  unless moduleType.getAppFn.isConstOf ``ModuleCat && ringArgs.size == 2 do
    throwError "NativeAssociation018 expected stored ModuleCat ring/instance2."
  let mapped := ha[8]!.consumeMData.headBeta
  let ma := mapped.getAppArgs
  unless mapped.getAppFn.isConstOf ``CategoryTheory.Functor.map && ma.size == 8 do
    throwError "NativeAssociation018 expected exact stored functor map8."
  unless ma[2]!.consumeMData.equal moduleType.consumeMData do
    throwError "NativeAssociation018 refused different functor/module target vector."
  let outer := ma[7]!.consumeMData.headBeta
  let oa := outer.getAppArgs
  unless outer.getAppFn.isConstOf ``CategoryTheory.CategoryStruct.comp && oa.size == 7 do
    throwError "NativeAssociation018 expected native outer comp7."
  let inner := oa[5]!.consumeMData.headBeta
  let ia := inner.getAppArgs
  unless inner.getAppFn.isConstOf ``CategoryTheory.CategoryStruct.comp && ia.size == 7 do
    throwError "NativeAssociation018 expected native left-associated inner comp7."
  unless ia[0]!.consumeMData.equal oa[0]!.consumeMData &&
      ia[1]!.consumeMData.equal oa[1]!.consumeMData &&
      ia[2]!.consumeMData.equal oa[2]!.consumeMData &&
      ia[4]!.consumeMData.equal oa[3]!.consumeMData &&
      ma[0]!.consumeMData.equal oa[0]!.consumeMData &&
      ma[5]!.consumeMData.equal oa[2]!.consumeMData &&
      ma[6]!.consumeMData.equal oa[4]!.consumeMData do
    throwError "NativeAssociation018 refused incompatible stored category/object prefixes."
  let arguments := #[ringArgs[0]!, ringArgs[1]!, ma[0]!, ma[1]!, ma[4]!,
    ia[2]!, ia[3]!, ia[4]!, oa[4]!, ia[5]!, ia[6]!, oa[6]!, ea[5]!]
  -- All thirteen class/object/value arguments are stored. This resolves only
  -- universe levels, then mkAppN emits the SAME complete stored argument vector.
  let resolved ← mkAppOptM ``phiNativeMappedTripleAssociation018
    (arguments.map fun argument => some argument)
  Term.synthesizeSyntheticMVarsNoPostponing
  let resolved ← instantiateMVars resolved
  let proof ← instantiateMVars (mkAppN resolved.getAppFn arguments)
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeAssociation018 unresolved/recovery stored native association."
  let (_, nativeLeft, _) ← phiNativeStoredEq018 proof
  unless nativeLeft.consumeMData.equal endpoint.consumeMData do
    throwError "NativeAssociation018 refused reconstructed endpoint unequal to literal native RHS."
  logInfo "NativeAssociation018 ordinary mapped Category.assoc from exact stored ring/category/comp/object/section vectors."
  return proof

end

private theorem actualOriginalGlobalPhiNativeLeftAccessorPoint018
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_accessor_point018% 0
      (actualOriginalGlobalPhiNativeFullSquareInferred010 p hp P hP s)
      using
      (actualOriginalGlobalPhiNativeLeftAccessor015 p hp P hP s)) :=
  phi_native_accessor_point018% 0
      (actualOriginalGlobalPhiNativeFullSquareInferred010 p hp P hP s)
      using
      (actualOriginalGlobalPhiNativeLeftAccessor015 p hp P hP s)


meta section
open Lean Meta Elab Term

/-- Exact law-type/coe-type selectors; the already matching accessor VALUE
must remain raw identical. No comparison is accepted as a proof here. -/
elab "phi_native_right_type022% " mode:num supplied:term " using " law:term : term => do
  unless mode.getNat < 2 do
    throwError "NativeRightType022 expected mode0/1."
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  let law ← Term.elabTerm law none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let source ← instantiateMVars source
  let law ← instantiateMVars law
  if source.hasMVar || source.hasLevelMVar || source.hasLooseBVars || source.hasSorry ||
      law.hasMVar || law.hasLevelMVar || law.hasLooseBVars || law.hasSorry then
    throwError "NativeRightType022 unresolved/recovery vector."
  let (_, _, endpoint) ← phiNativeStoredEq018 source
  let endpoint := endpoint.consumeMData.headBeta
  let a := endpoint.getAppArgs
  unless endpoint.getAppFn.isConstOf ``DFunLike.coe && a.size == 6 do
    throwError "NativeRightType022 expected exact source coe6."
  let (lawType, lawLeft, _) ← phiNativeStoredEq018 law
  unless lawLeft.consumeMData.equal a[4]!.consumeMData do
    throwError "NativeRightType022 refused different original accessor VALUE."
  return if mode.getNat == 0 then lawType else a[0]!

/-- Exact outer/inner category selectors from literal native Prop016.
No reconstructed object, category or dictionary is silently substituted. -/
elab "phi_native_association_category022% " side:num supplied:term : term => do
  unless side.getNat < 2 do
    throwError "NativeAssociationCategory022 expected outer0/inner1."
  let proposition ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let proposition ← instantiateMVars proposition
  if proposition.hasMVar || proposition.hasLevelMVar || proposition.hasLooseBVars || proposition.hasSorry then
    throwError "NativeAssociationCategory022 unresolved/recovery proposition."
  let proposition := (← whnf proposition).consumeMData.headBeta
  let some (_, _, endpoint) := proposition.eq?
    | throwError "NativeAssociationCategory022 expected literal Eq."
  let endpoint := endpoint.consumeMData.headBeta
  let a := endpoint.getAppArgs
  unless endpoint.getAppFn.isConstOf ``DFunLike.coe && a.size == 6 do
    throwError "NativeAssociationCategory022 expected literal coe6."
  let accessor := a[4]!.consumeMData.headBeta
  let ha := accessor.getAppArgs
  unless accessor.getAppFn.isConstOf ``CategoryTheory.ConcreteCategory.hom && ha.size == 9 do
    throwError "NativeAssociationCategory022 expected literal accessor9."
  let mapped := ha[8]!.consumeMData.headBeta
  let ma := mapped.getAppArgs
  unless mapped.getAppFn.isConstOf ``CategoryTheory.Functor.map && ma.size == 8 do
    throwError "NativeAssociationCategory022 expected literal map8."
  let outer := ma[7]!.consumeMData.headBeta
  let oa := outer.getAppArgs
  unless outer.getAppFn.isConstOf ``CategoryTheory.CategoryStruct.comp && oa.size == 7 do
    throwError "NativeAssociationCategory022 expected literal outer comp7."
  let inner := oa[5]!.consumeMData.headBeta
  let ia := inner.getAppArgs
  unless inner.getAppFn.isConstOf ``CategoryTheory.CategoryStruct.comp && ia.size == 7 do
    throwError "NativeAssociationCategory022 expected literal inner comp7."
  return if side.getNat == 0 then oa[0]! else ia[0]!

end

private theorem actualOriginalGlobalPhiNativeRightAccessorTypeEq022
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    (phi_native_right_type022% 0
      (actualOriginalGlobalPhiNativeFullSquareInferred010 p hp P hP s)
      using (actualOriginalGlobalPhiNativeRightAccessor015 p hp P hP s)) =
    (phi_native_right_type022% 1
      (actualOriginalGlobalPhiNativeFullSquareInferred010 p hp P hP s)
      using (actualOriginalGlobalPhiNativeRightAccessor015 p hp P hP s)) := by
  basis_full_exact142 (rfl : (phi_native_right_type022% 0
      (actualOriginalGlobalPhiNativeFullSquareInferred010 p hp P hP s)
      using (actualOriginalGlobalPhiNativeRightAccessor015 p hp P hP s)) =
    (phi_native_right_type022% 0
      (actualOriginalGlobalPhiNativeFullSquareInferred010 p hp P hP s)
      using (actualOriginalGlobalPhiNativeRightAccessor015 p hp P hP s)))

private theorem actualOriginalGlobalPhiNativeAssociationCategoryEq022
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    (phi_native_association_category022% 0
      (actualOriginalGlobalPhiNativeHeaderProposition016 p hp P hP s)) =
    (phi_native_association_category022% 1
      (actualOriginalGlobalPhiNativeHeaderProposition016 p hp P hP s)) := by
  basis_full_exact142
    (congrArg (fun R : CommRingCat.{u} => (Spec R).Modules)
      (actualOriginalPhiNativeResidueBundle013 p hp P))


/-- Project an actual equality through a dependent family without replacing
its types or instances definitionally. -/
private theorem phiNativeDependentCongr023.{uDep023, vDep023}
    {A : Sort uDep023} {B : A → Sort vDep023} {x y : A}
    (h : x = y) (f : ∀ a, B a) : HEq (f x) (f y) := by
  cases h
  rfl

meta section
open Lean Meta Elab Term

/-- Evaluate the original F-typed accessor after its PROVED F=G transport,
using the exact stored native G-typed coe6 vector. No raw TYPE guard bypass. -/
elab "phi_native_right_cast_point023% " supplied:term " using " law:term
    " along " compatibility:term : term => do
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  let law ← Term.elabTerm law none (catchExPostpone := false)
  let compatibility ← Term.elabTerm compatibility none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let source ← instantiateMVars source
  let law ← instantiateMVars law
  let compatibility ← instantiateMVars compatibility
  if source.hasMVar || source.hasLevelMVar || source.hasLooseBVars || source.hasSorry ||
      law.hasMVar || law.hasLevelMVar || law.hasLooseBVars || law.hasSorry ||
      compatibility.hasMVar || compatibility.hasLevelMVar || compatibility.hasLooseBVars || compatibility.hasSorry then
    throwError "NativeCastPoint023 unresolved/recovery stored input."
  let (_, _, endpoint) ← phiNativeStoredEq018 source
  let endpoint := endpoint.consumeMData.headBeta
  let a := endpoint.getAppArgs
  unless endpoint.getAppFn.isConstOf ``DFunLike.coe && a.size == 6 do
    throwError "NativeCastPoint023 expected exact original coe6 endpoint."
  let (lawType, lawLeft, lawRight) ← phiNativeStoredEq018 law
  let (_, compatLeft, compatRight) ← phiNativeStoredEq018 compatibility
  unless compatLeft.consumeMData.equal lawType.consumeMData &&
      compatRight.consumeMData.equal a[0]!.consumeMData &&
      lawLeft.consumeMData.equal a[4]!.consumeMData do
    throwError "NativeCastPoint023 refused a different proven TYPE bridge or accessor VALUE."
  let resultType ← inferType endpoint
  let sourceLevel ← getLevel lawType
  let resultLevel ← getLevel resultType
  let evaluator ← withLocalDeclD `accessor lawType fun accessor => do
    let transported := mkAppN (mkConst ``Eq.mp [sourceLevel])
      #[lawType, a[0]!, compatibility, accessor]
    mkLambdaFVars #[accessor] (mkAppN endpoint.getAppFn (a.set! 4 transported))
  let proof := mkAppN (mkConst ``congrArg [sourceLevel, resultLevel])
    #[lawType, resultType, lawLeft, lawRight, evaluator, law]
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "NativeCastPoint023 unresolved/recovery emitted ordinary proof."
  logInfo "NativeCastPoint023 original accessor law evaluated with explicit checked TypeEq022 cast and stored coe6 vector."
  return proof

/-- Literal outer/inner CategoryStruct values, independent of object/value
conversion. Uses the SAME native map/proposition selectors, not reconstruction. -/
elab "phi_native_association_struct023% " side:num supplied:term : term => do
  unless side.getNat < 2 do
    throwError "NativeAssociationStruct023 expected outer0/inner1."
  let proposition ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let proposition ← instantiateMVars proposition
  if proposition.hasMVar || proposition.hasLevelMVar || proposition.hasLooseBVars || proposition.hasSorry then
    throwError "NativeAssociationStruct023 unresolved/recovery proposition."
  let proposition := (← whnf proposition).consumeMData.headBeta
  let some (_, _, endpoint) := proposition.eq?
    | throwError "NativeAssociationStruct023 expected literal native Eq."
  let endpoint := endpoint.consumeMData.headBeta
  let a := endpoint.getAppArgs
  unless endpoint.getAppFn.isConstOf ``DFunLike.coe && a.size == 6 do
    throwError "NativeAssociationStruct023 expected literal coe6."
  let accessor := a[4]!.consumeMData.headBeta
  let ha := accessor.getAppArgs
  unless accessor.getAppFn.isConstOf ``CategoryTheory.ConcreteCategory.hom && ha.size == 9 do
    throwError "NativeAssociationStruct023 expected literal concrete accessor9."
  let mapped := ha[8]!.consumeMData.headBeta
  let ma := mapped.getAppArgs
  unless mapped.getAppFn.isConstOf ``CategoryTheory.Functor.map && ma.size == 8 do
    throwError "NativeAssociationStruct023 expected literal map8."
  let outer := ma[7]!.consumeMData.headBeta
  let oa := outer.getAppArgs
  unless outer.getAppFn.isConstOf ``CategoryTheory.CategoryStruct.comp && oa.size == 7 do
    throwError "NativeAssociationStruct023 expected literal outer comp7."
  let inner := oa[5]!.consumeMData.headBeta
  let ia := inner.getAppArgs
  unless inner.getAppFn.isConstOf ``CategoryTheory.CategoryStruct.comp && ia.size == 7 do
    throwError "NativeAssociationStruct023 expected literal inner comp7."
  return if side.getNat == 0 then oa[1]! else ia[1]!

end

private theorem actualOriginalGlobalPhiNativeRightAccessorCastPoint023
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_right_cast_point023%
      (actualOriginalGlobalPhiNativeFullSquareInferred010 p hp P hP s)
      using (actualOriginalGlobalPhiNativeRightAccessor015 p hp P hP s)
      along (actualOriginalGlobalPhiNativeRightAccessorTypeEq022 p hp P hP s)) :=
  phi_native_right_cast_point023%
    (actualOriginalGlobalPhiNativeFullSquareInferred010 p hp P hP s)
    using (actualOriginalGlobalPhiNativeRightAccessor015 p hp P hP s)
    along (actualOriginalGlobalPhiNativeRightAccessorTypeEq022 p hp P hP s)

private theorem actualOriginalGlobalPhiNativeAssociationStructHEq023
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    HEq (phi_native_association_struct023% 0
      (actualOriginalGlobalPhiNativeHeaderProposition016 p hp P hP s))
      (phi_native_association_struct023% 1
        (actualOriginalGlobalPhiNativeHeaderProposition016 p hp P hP s)) := by
  basis_full_exact142
    (phiNativeDependentCongr023 (actualOriginalPhiNativeResidueBundle013 p hp P)
      (fun R : CommRingCat.{u} =>
        @Category.toCategoryStruct (Spec R).Modules (@Scheme.Modules.instCategory (Spec R))))


meta section
open Lean Meta Elab Term

private structure PhiNativeAssociationVectors025 where
  endpoint : Expr
  coeArgs : Array Expr
  accessor : Expr
  accessorArgs : Array Expr
  mapped : Expr
  mapArgs : Array Expr
  outer : Expr
  outerArgs : Array Expr
  inner : Expr
  innerArgs : Array Expr

private def phiNativeAssociationVectors025 (proposition : Expr) :
    Term.TermElabM PhiNativeAssociationVectors025 := do
  let proposition := (← whnf proposition).consumeMData.headBeta
  let some (_, _, endpoint) := proposition.eq?
    | throwError "Native025 expected literal native Eq proposition."
  let endpoint := endpoint.consumeMData.headBeta
  let ea := endpoint.getAppArgs
  unless endpoint.getAppFn.isConstOf ``DFunLike.coe && ea.size == 6 do
    throwError "Native025 expected literal coe6."
  let accessor := ea[4]!.consumeMData.headBeta
  let ha := accessor.getAppArgs
  unless accessor.getAppFn.isConstOf ``CategoryTheory.ConcreteCategory.hom && ha.size == 9 do
    throwError "Native025 expected literal concrete accessor9."
  let mapped := ha[8]!.consumeMData.headBeta
  let ma := mapped.getAppArgs
  unless mapped.getAppFn.isConstOf ``CategoryTheory.Functor.map && ma.size == 8 do
    throwError "Native025 expected literal map8."
  let outer := ma[7]!.consumeMData.headBeta
  let oa := outer.getAppArgs
  unless outer.getAppFn.isConstOf ``CategoryTheory.CategoryStruct.comp && oa.size == 7 do
    throwError "Native025 expected literal outer comp7."
  let inner := oa[5]!.consumeMData.headBeta
  let ia := inner.getAppArgs
  unless inner.getAppFn.isConstOf ``CategoryTheory.CategoryStruct.comp && ia.size == 7 &&
      inner.getAppFn.equal outer.getAppFn do
    throwError "Native025 expected same original inner/outer comp7 head and universes."
  unless ia[2]!.consumeMData.equal oa[2]!.consumeMData &&
      ia[4]!.consumeMData.equal oa[3]!.consumeMData &&
      ma[0]!.consumeMData.equal oa[0]!.consumeMData &&
      ma[5]!.consumeMData.equal oa[2]!.consumeMData &&
      ma[6]!.consumeMData.equal oa[4]!.consumeMData do
    throwError "Native025 refused changed literal object/functor vectors."
  return ⟨endpoint, ea, accessor, ha, mapped, ma, outer, oa, inner, ia⟩

private def phiNativeNoRecovery025 (proof : Expr) : Term.TermElabM Expr := do
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "Native025 unresolved/recovery proof/vector."
  return proof

/-- Compare literal inner composition with the SAME f/g/W/X/Y using outer
prefix, by one ordinary hcongr whose first two inputs are checked022/024. -/
elab "phi_native_inner_comp025% " supplied:term " using " categoryProof:term
    " and " dictionaryProof:term : term => do
  let proposition ← Term.elabTerm supplied none (catchExPostpone := false)
  let categoryProof ← Term.elabTerm categoryProof none (catchExPostpone := false)
  let dictionaryProof ← Term.elabTerm dictionaryProof none (catchExPostpone := false)
  let proposition ← phiNativeNoRecovery025 proposition
  let categoryProof ← phiNativeNoRecovery025 categoryProof
  let dictionaryProof ← phiNativeNoRecovery025 dictionaryProof
  let v ← phiNativeAssociationVectors025 proposition
  let (_, categoryLeft, categoryRight) ← phiNativeStoredEq018 categoryProof
  let some (_, dictionaryLeft, _, dictionaryRight) :=
      (← whnf (← inferType dictionaryProof)).consumeMData.headBeta.heq?
    | throwError "Native025 expected checked dictionaryProof HEq."
  unless categoryLeft.consumeMData.equal v.outerArgs[0]!.consumeMData &&
      categoryRight.consumeMData.equal v.innerArgs[0]!.consumeMData &&
      dictionaryLeft.consumeMData.equal v.outerArgs[1]!.consumeMData &&
      dictionaryRight.consumeMData.equal v.innerArgs[1]!.consumeMData do
    throwError "Native025 refused different checked categoryProof/dictionaryProof endpoints."
  let la := (v.innerArgs.set! 0 v.outerArgs[0]!).set! 1 v.outerArgs[1]!
  let congruence ← mkHCongrWithArity v.inner.getAppFn 7
  let mut arguments := #[]
  for i in [:7] do
    let heq ← if i == 0 then mkHEqOfEq categoryProof
      else if i == 1 then pure dictionaryProof
      else mkHEqRefl v.innerArgs[i]!
    let compatibility ← match congruence.argKinds[i]! with
      | .eq => mkEqOfHEq heq
      | .heq => pure heq
      | _ => throwError "Native025 unsupported generated congruence argument kind."
    arguments := arguments ++ #[la[i]!, v.innerArgs[i]!, compatibility]
  let proof ← phiNativeNoRecovery025 (mkAppN congruence.proof arguments)
  let some (_, left, _, right) := (← whnf (← inferType proof)).consumeMData.headBeta.heq?
    | throwError "Native025 expected emitted inner-comp HEq."
  unless left.consumeMData.equal (mkAppN v.inner.getAppFn la).consumeMData &&
      right.consumeMData.equal v.inner.consumeMData do
    throwError "Native025 refused drift from original inner composition values."
  logInfo "Native025 inner-comp hcongr uses actual categoryEq022/dictionaryHEq024 and SAME remaining five original arguments."
  return proof

/-- Ordinary own-vector mapped associativity on explicitly outer-aligned
composition. It is not yet the literal native left endpoint. -/
elab "phi_native_mapped_assoc_own025% " supplied:term : term => do
  let proposition ← Term.elabTerm supplied none (catchExPostpone := false)
  let proposition ← phiNativeNoRecovery025 proposition
  let v ← phiNativeAssociationVectors025 proposition
  let moduleType := v.accessorArgs[0]!.consumeMData.headBeta
  let ra := moduleType.getAppArgs
  unless moduleType.getAppFn.isConstOf ``ModuleCat && ra.size == 2 &&
      v.mapArgs[2]!.consumeMData.equal moduleType.consumeMData do
    throwError "Native025 refused different native module/ring vector."
  let arguments := #[ra[0]!, ra[1]!, v.mapArgs[0]!, v.mapArgs[1]!, v.mapArgs[4]!,
    v.innerArgs[2]!, v.innerArgs[3]!, v.innerArgs[4]!, v.outerArgs[4]!,
    v.innerArgs[5]!, v.innerArgs[6]!, v.outerArgs[6]!, v.coeArgs[5]!]
  let resolved ← mkAppOptM ``phiNativeMappedTripleAssociation018
    (arguments.map fun argument => some argument)
  let resolved ← phiNativeNoRecovery025 resolved
  let proof ← phiNativeNoRecovery025 (mkAppN resolved.getAppFn arguments)
  let (_, left, _) ← phiNativeStoredEq018 proof
  let aligned := mkAppN v.inner.getAppFn
    ((v.innerArgs.set! 0 v.outerArgs[0]!).set! 1 v.outerArgs[1]!)
  let outer := mkAppN v.outer.getAppFn (v.outerArgs.set! 5 aligned)
  let mapped := mkAppN v.mapped.getAppFn (v.mapArgs.set! 7 outer)
  let accessor := mkAppN v.accessor.getAppFn (v.accessorArgs.set! 8 mapped)
  let expected := mkAppN v.endpoint.getAppFn (v.coeArgs.set! 4 accessor)
  unless left.consumeMData.equal expected.consumeMData do
    throwError "Native025 refused own left endpoint drifting from explicit outer-aligned same-value vector."
  logInfo "Native025 ordinary generic018 mapped association instantiated with full original ring/categoryProof/f/g/h/object/section vector, aligned prefix explicit."
  return proof

/-- Lift the CHECKED inner composition equality through literal original
outer comp/map/accessor/section and combine with ordinary own mapped assoc. -/
elab "phi_native_mapped_assoc_literal025% " supplied:term " using " innerEquality:term
    " and " association:term : term => do
  let proposition ← Term.elabTerm supplied none (catchExPostpone := false)
  let innerEquality ← Term.elabTerm innerEquality none (catchExPostpone := false)
  let association ← Term.elabTerm association none (catchExPostpone := false)
  let proposition ← phiNativeNoRecovery025 proposition
  let innerEquality ← phiNativeNoRecovery025 innerEquality
  let association ← phiNativeNoRecovery025 association
  let v ← phiNativeAssociationVectors025 proposition
  let (innerType, aligned, literal) ← phiNativeStoredEq018 innerEquality
  let (resultType, assocLeft, assocRight) ← phiNativeStoredEq018 association
  let expectedAligned := mkAppN v.inner.getAppFn
    ((v.innerArgs.set! 0 v.outerArgs[0]!).set! 1 v.outerArgs[1]!)
  unless aligned.consumeMData.equal expectedAligned.consumeMData &&
      literal.consumeMData.equal v.inner.consumeMData do
    throwError "Native025 refused different actual inner-comp equality endpoints."
  let evaluator ← withLocalDeclD `innerMorphism innerType fun innerMorphism => do
    let outer := mkAppN v.outer.getAppFn (v.outerArgs.set! 5 innerMorphism)
    let mapped := mkAppN v.mapped.getAppFn (v.mapArgs.set! 7 outer)
    let accessor := mkAppN v.accessor.getAppFn (v.accessorArgs.set! 8 mapped)
    mkLambdaFVars #[innerMorphism] (mkAppN v.endpoint.getAppFn (v.coeArgs.set! 4 accessor))
  let innerLevel ← getLevel innerType
  let resultLevel ← getLevel resultType
  let pointLift := mkAppN (mkConst ``congrArg [innerLevel, resultLevel])
    #[innerType, resultType, aligned, literal, evaluator, innerEquality]
  let pointLift ← phiNativeNoRecovery025 pointLift
  let (liftType, liftLeft, liftRight) ← phiNativeStoredEq018 pointLift
  unless liftType.consumeMData.equal resultType.consumeMData &&
      liftLeft.consumeMData.headBeta.equal assocLeft.consumeMData.headBeta &&
      liftRight.consumeMData.headBeta.equal v.endpoint.consumeMData.headBeta do
    throwError "Native025 refused changed mapped/section endpoints in inner-composition pointLift."
  let reverseProof := mkAppN (mkConst ``Eq.symm [resultLevel])
    #[resultType, liftLeft, liftRight, pointLift]
  let proof := mkAppN (mkConst ``Eq.trans [resultLevel])
    #[resultType, v.endpoint, assocLeft, assocRight, reverseProof, association]
  let proof ← phiNativeNoRecovery025 proof
  logInfo "Native025 literal native mapped associativity follows actual inner equality under original context plus own generic018 association; no deep defeq association."
  return proof

end

private theorem actualOriginalGlobalPhiNativeInnerCompositionHEq025
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_inner_comp025%
      (actualOriginalGlobalPhiNativeHeaderProposition016 p hp P hP s)
      using (actualOriginalGlobalPhiNativeAssociationCategoryEq022 p hp P hP s)
      and (actualOriginalGlobalPhiNativeAssociationStructHEq023 p hp P hP s)) :=
  phi_native_inner_comp025%
    (actualOriginalGlobalPhiNativeHeaderProposition016 p hp P hP s)
    using (actualOriginalGlobalPhiNativeAssociationCategoryEq022 p hp P hP s)
    and (actualOriginalGlobalPhiNativeAssociationStructHEq023 p hp P hP s)


/-- Eq.mp changes the type, preserving the SAME accessor value heterogeneously. -/
private theorem phiNativeEqMpHEq026.{uEqMp026}
    {F G : Sort uEqMp026} (h : F = G) (x : F) :
    HEq (@Eq.mp F G h x) x := by
  cases h
  rfl

meta section
open Lean Meta Elab Term

private def phiNativeCastEndpoint026 (side : Nat) (pointProof : Expr) :
    Term.TermElabM (Expr × Array Expr × Array Expr) := do
  unless side < 2 do throwError "Native026 expected side0/1."
  let (_, pointLeft, pointRight) ← phiNativeStoredEq018 pointProof
  let endpoint := (if side == 0 then pointLeft else pointRight).consumeMData.headBeta
  let ea := endpoint.getAppArgs
  unless endpoint.getAppFn.isConstOf ``DFunLike.coe && ea.size == 6 do
    throwError "Native026 expected original casted point coe6."
  let casted := ea[4]!.consumeMData.headBeta
  let ca := casted.getAppArgs
  unless casted.getAppFn.isConstOf ``Eq.mp && ca.size == 4 &&
      ea[0]!.consumeMData.equal ca[1]!.consumeMData do
    throwError "Native026 expected exact casted accessor Eq.mp4/typeG."
  return (endpoint, ea, ca)

/-- Use the exact Eq.mp universe/four-argument vector, guarded by the checked
TYPE equality proof VALUE, and ordinary generic law prefix identity. -/
elab "phi_native_accessor_cast_heq026% " side:num supplied:term
    " along " compatibility:term : term => do
  let supplied ← Term.elabTerm supplied none (catchExPostpone := false)
  let compatibility ← Term.elabTerm compatibility none (catchExPostpone := false)
  let supplied ← phiNativeNoRecovery025 supplied
  let compatibility ← phiNativeNoRecovery025 compatibility
  let (_, ea, ca) ← phiNativeCastEndpoint026 side.getNat supplied
  let (_, typeLeft, typeRight) ← phiNativeStoredEq018 compatibility
  unless typeLeft.consumeMData.equal ca[0]!.consumeMData &&
      typeRight.consumeMData.equal ca[1]!.consumeMData &&
      compatibility.consumeMData.equal ca[2]!.consumeMData do
    throwError "Native026 refused different checked TypeEq022 proof/vector."
  let casted := ea[4]!.consumeMData.headBeta
  let .const _ levels := casted.getAppFn
    | throwError "Native026 expected exact Eq.mp stored universe."
  let castInfo ← getConstInfo ``Eq.mp
  let lawInfo ← getConstInfo ``phiNativeEqMpHEq026
  unless levels.length == 1 && castInfo.levelParams.length == 1 &&
      lawInfo.levelParams.length == 1 do
    throwError "Native026 expected exactly one Eq.mp/law universe."
  let canonical := [Level.param `phiNativeEqMpCanonical026]
  let mut castType := castInfo.type.instantiateLevelParams castInfo.levelParams canonical
  let mut lawType := lawInfo.type.instantiateLevelParams lawInfo.levelParams canonical
  for i in [:4] do
    let .forallE _ castDomain castBody castBinder := castType
      | throwError "Native026 missing Eq.mp prefix binder."
    let .forallE _ lawDomain lawBody lawBinder := lawType
      | throwError "Native026 missing generic Eq.mp law binder."
    unless castDomain.equal lawDomain && castBinder == lawBinder do
      throwError "Native026 refused unequal exact Eq.mp/law prefix at {i}."
    castType := castBody
    lawType := lawBody
  let proof ← phiNativeNoRecovery025 (mkAppN (mkConst ``phiNativeEqMpHEq026 levels) ca)
  let some (_, left, _, right) := (← whnf (← inferType proof)).consumeMData.headBeta.heq?
    | throwError "Native026 expected emitted accessor HEq."
  unless left.consumeMData.equal casted.consumeMData &&
      right.consumeMData.equal ca[3]!.consumeMData do
    throwError "Native026 refused changed Eq.mp/accessor result endpoints."
  logInfo m!"Native026 side{side.getNat}: own Eq.mp4 HEq emitted, actual TypeEq022 value retained."
  return proof

/-- Lift a checked homogeneous accessor equality through the EXACT original
point evaluator; side0's uncast endpoint must be original own010 RHS raw-identical. -/
elab "phi_native_cast_point_lift026% " side:num supplied:term
    " using " accessorEquality:term " from " originalSource:term : term => do
  let supplied ← Term.elabTerm supplied none (catchExPostpone := false)
  let accessorEquality ← Term.elabTerm accessorEquality none (catchExPostpone := false)
  let originalSource ← Term.elabTerm originalSource none (catchExPostpone := false)
  let supplied ← phiNativeNoRecovery025 supplied
  let accessorEquality ← phiNativeNoRecovery025 accessorEquality
  let originalSource ← phiNativeNoRecovery025 originalSource
  let (endpoint, ea, ca) ← phiNativeCastEndpoint026 side.getNat supplied
  let (accessorType, casted, original) ← phiNativeStoredEq018 accessorEquality
  unless accessorType.consumeMData.equal ea[0]!.consumeMData &&
      casted.consumeMData.equal ea[4]!.consumeMData &&
      original.consumeMData.equal ca[3]!.consumeMData do
    throwError "Native026 refused different actual accessor equality/type endpoints."
  let originalPoint := mkAppN endpoint.getAppFn (ea.set! 4 original)
  let (_, _, sourceRight) ← phiNativeStoredEq018 originalSource
  if side.getNat == 0 then
    unless originalPoint.consumeMData.equal sourceRight.consumeMData do
      throwError "Native026 refused changed original own010 RHS/coercion/value."
  let resultType ← inferType endpoint
  let evaluator ← withLocalDeclD `accessor accessorType fun accessor => do
    mkLambdaFVars #[accessor] (mkAppN endpoint.getAppFn (ea.set! 4 accessor))
  let accessorLevel ← getLevel accessorType
  let resultLevel ← getLevel resultType
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``congrArg [accessorLevel, resultLevel])
      #[accessorType, resultType, casted, original, evaluator, accessorEquality])
  let (_, left, right) ← phiNativeStoredEq018 proof
  unless left.consumeMData.headBeta.equal endpoint.consumeMData.headBeta &&
      right.consumeMData.headBeta.equal originalPoint.consumeMData.headBeta do
    throwError "Native026 refused changed original coe6 evaluator/section."
  logInfo m!"Native026 side{side.getNat}: ordinary accessor equality lifted through exact stored original coe6 vector."
  return proof

/-- Join actual point lifts with passed023 casted point equality. All native
values/coercions are the exact stored endpoints, no new action or scalar map. -/
elab "phi_native_uncast_point026% " supplied:term " using " leftLift:term
    " and " rightLift:term : term => do
  let supplied ← Term.elabTerm supplied none (catchExPostpone := false)
  let leftLift ← Term.elabTerm leftLift none (catchExPostpone := false)
  let rightLift ← Term.elabTerm rightLift none (catchExPostpone := false)
  let supplied ← phiNativeNoRecovery025 supplied
  let leftLift ← phiNativeNoRecovery025 leftLift
  let rightLift ← phiNativeNoRecovery025 rightLift
  let (pointType, castLeft, castRight) ← phiNativeStoredEq018 supplied
  let (leftType, liftedLeft, originalLeft) ← phiNativeStoredEq018 leftLift
  let (rightType, liftedRight, originalRight) ← phiNativeStoredEq018 rightLift
  unless pointType.consumeMData.equal leftType.consumeMData &&
      pointType.consumeMData.equal rightType.consumeMData &&
      castLeft.consumeMData.headBeta.equal liftedLeft.consumeMData.headBeta &&
      castRight.consumeMData.headBeta.equal liftedRight.consumeMData.headBeta do
    throwError "Native026 refused different cast/point lift endpoints or type."
  let level ← getLevel pointType
  let reverseLeft := mkAppN (mkConst ``Eq.symm [level])
    #[pointType, liftedLeft, originalLeft, leftLift]
  let firstComposite := mkAppN (mkConst ``Eq.trans [level])
    #[pointType, originalLeft, castLeft, castRight, reverseLeft, supplied]
  let proof := mkAppN (mkConst ``Eq.trans [level])
    #[pointType, originalLeft, castRight, originalRight, firstComposite, rightLift]
  let proof ← phiNativeNoRecovery025 proof
  logInfo "Native026 uncast own-point equality follows actual two lifted accessor equalities and passed023 point equality, exact vectors."
  return proof

end

private theorem actualOriginalGlobalPhiNativeLeftAccessorCastHEq026
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_accessor_cast_heq026% 0
      (actualOriginalGlobalPhiNativeRightAccessorCastPoint023 p hp P hP s)
      along (actualOriginalGlobalPhiNativeRightAccessorTypeEq022 p hp P hP s)) :=
  phi_native_accessor_cast_heq026% 0
    (actualOriginalGlobalPhiNativeRightAccessorCastPoint023 p hp P hP s)
    along (actualOriginalGlobalPhiNativeRightAccessorTypeEq022 p hp P hP s)

private theorem actualOriginalGlobalPhiNativeLeftAccessorCastEq026
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_infer010%
      (eq_of_heq (actualOriginalGlobalPhiNativeLeftAccessorCastHEq026 p hp P hP s))) :=
  phi_native_infer010%
    (eq_of_heq (actualOriginalGlobalPhiNativeLeftAccessorCastHEq026 p hp P hP s))

private theorem actualOriginalGlobalPhiNativeLeftCastPointLift026
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_cast_point_lift026% 0
      (actualOriginalGlobalPhiNativeRightAccessorCastPoint023 p hp P hP s)
      using (actualOriginalGlobalPhiNativeLeftAccessorCastEq026 p hp P hP s)
      from (actualOriginalGlobalPhiNativeFullSquareInferred010 p hp P hP s)) :=
  phi_native_cast_point_lift026% 0
    (actualOriginalGlobalPhiNativeRightAccessorCastPoint023 p hp P hP s)
    using (actualOriginalGlobalPhiNativeLeftAccessorCastEq026 p hp P hP s)
    from (actualOriginalGlobalPhiNativeFullSquareInferred010 p hp P hP s)

private theorem actualOriginalGlobalPhiNativeRightAccessorCastHEq026
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_accessor_cast_heq026% 1
      (actualOriginalGlobalPhiNativeRightAccessorCastPoint023 p hp P hP s)
      along (actualOriginalGlobalPhiNativeRightAccessorTypeEq022 p hp P hP s)) :=
  phi_native_accessor_cast_heq026% 1
    (actualOriginalGlobalPhiNativeRightAccessorCastPoint023 p hp P hP s)
    along (actualOriginalGlobalPhiNativeRightAccessorTypeEq022 p hp P hP s)

private theorem actualOriginalGlobalPhiNativeRightAccessorCastEq026
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_infer010%
      (eq_of_heq (actualOriginalGlobalPhiNativeRightAccessorCastHEq026 p hp P hP s))) :=
  phi_native_infer010%
    (eq_of_heq (actualOriginalGlobalPhiNativeRightAccessorCastHEq026 p hp P hP s))

private theorem actualOriginalGlobalPhiNativeRightCastPointLift026
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_cast_point_lift026% 1
      (actualOriginalGlobalPhiNativeRightAccessorCastPoint023 p hp P hP s)
      using (actualOriginalGlobalPhiNativeRightAccessorCastEq026 p hp P hP s)
      from (actualOriginalGlobalPhiNativeFullSquareInferred010 p hp P hP s)) :=
  phi_native_cast_point_lift026% 1
    (actualOriginalGlobalPhiNativeRightAccessorCastPoint023 p hp P hP s)
    using (actualOriginalGlobalPhiNativeRightAccessorCastEq026 p hp P hP s)
    from (actualOriginalGlobalPhiNativeFullSquareInferred010 p hp P hP s)

private theorem actualOriginalGlobalPhiNativeRightUncastPoint026
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_uncast_point026%
      (actualOriginalGlobalPhiNativeRightAccessorCastPoint023 p hp P hP s)
      using (actualOriginalGlobalPhiNativeLeftCastPointLift026 p hp P hP s)
      and (actualOriginalGlobalPhiNativeRightCastPointLift026 p hp P hP s)) :=
  phi_native_uncast_point026%
    (actualOriginalGlobalPhiNativeRightAccessorCastPoint023 p hp P hP s)
    using (actualOriginalGlobalPhiNativeLeftCastPointLift026 p hp P hP s)
    and (actualOriginalGlobalPhiNativeRightCastPointLift026 p hp P hP s)


private theorem actualOriginalGlobalPhiNativeInnerCompositionEq025
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_infer010%
      (eq_of_heq (actualOriginalGlobalPhiNativeInnerCompositionHEq025 p hp P hP s))) :=
  phi_native_infer010%
    (eq_of_heq (actualOriginalGlobalPhiNativeInnerCompositionHEq025 p hp P hP s))

private theorem actualOriginalGlobalPhiNativeMappedAssociationOwn025
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_mapped_assoc_own025%
      (actualOriginalGlobalPhiNativeHeaderProposition016 p hp P hP s)) :=
  phi_native_mapped_assoc_own025%
    (actualOriginalGlobalPhiNativeHeaderProposition016 p hp P hP s)

private theorem actualOriginalGlobalPhiNativeMappedAssociationLiteral025
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_mapped_assoc_literal025%
      (actualOriginalGlobalPhiNativeHeaderProposition016 p hp P hP s)
      using (actualOriginalGlobalPhiNativeInnerCompositionEq025 p hp P hP s)
      and (actualOriginalGlobalPhiNativeMappedAssociationOwn025 p hp P hP s)) :=
  phi_native_mapped_assoc_literal025%
    (actualOriginalGlobalPhiNativeHeaderProposition016 p hp P hP s)
    using (actualOriginalGlobalPhiNativeInnerCompositionEq025 p hp P hP s)
    and (actualOriginalGlobalPhiNativeMappedAssociationOwn025 p hp P hP s)

private theorem actualOriginalGlobalPhiNativeLeftEndpointHEq025
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    HEq (phi_native_eq_endpoint017% 0 0
      (actualOriginalGlobalPhiNativeFullSquareInferred010 p hp P hP s))
      (phi_native_eq_endpoint017% 1 0
        (actualOriginalGlobalPhiNativeHeaderProposition016 p hp P hP s)) := by
  basis_full_exact142
    (heq_of_eq (actualOriginalGlobalPhiNativeLeftAccessorPoint018 p hp P hP s))

/- SOURCE ONLY / UNVERIFIED027. Compare SAME right-associated images, after
ordinary026 cast forgetting. Associativity is supplied separately by025. -/
private theorem actualOriginalGlobalPhiNativeRightEndpointHEq027
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    HEq (phi_native_eq_endpoint017% 0 1
      (actualOriginalGlobalPhiNativeRightUncastPoint026 p hp P hP s))
      (phi_native_eq_endpoint017% 0 1
        (actualOriginalGlobalPhiNativeMappedAssociationLiteral025 p hp P hP s)) := by
  basis_full_exact142
    (HEq.refl (phi_native_eq_endpoint017% 0 1
      (actualOriginalGlobalPhiNativeRightUncastPoint026 p hp P hP s)))

/-- Ordinary endpoint transport; all five concrete certificates are derived
internally below, without a new premise on the public theorem. -/
private theorem phiNativeSquareEndpointAssembly027.{uAssembly027}
    {V W : Sort uAssembly027}
    {a b c : V} {l r t : W}
    (sourceEquality : a = b) (leftComparison : HEq a l)
    (uncastEquality : b = c) (rightComparison : HEq c t)
    (associationEquality : r = t) : l = r := by
  apply eq_of_heq
  exact HEq.trans (HEq.symm leftComparison)
    (HEq.trans (heq_of_eq sourceEquality)
      (HEq.trans (heq_of_eq uncastEquality)
        (HEq.trans rightComparison (heq_of_eq associationEquality.symm))))

meta section
open Lean Meta Elab Term

private def phiNativeStoredHEq027 (proof : Expr) :
    Term.TermElabM (Expr × Expr × Expr × Expr) := do
  let proposition := (← whnf (← inferType proof)).consumeMData.headBeta
  let some parts := proposition.heq?
    | throwError "Native027 expected exact stored HEq proof type."
  return parts

/-- Every explicit argument is read from the certificates' OWN stored vectors.
Strict raw guards protect all shared types/endpoints before applying the tiny
ordinary transport law. No target-native type is imposed while elaborating. -/
elab "phi_native_square_assembly027% " sourceProof:term
    " using " leftProof:term " then " uncastProof:term
    " along " rightProof:term " and " associationProof:term : term => do
  let sourceProof ← Term.elabTerm sourceProof none (catchExPostpone := false)
  let leftProof ← Term.elabTerm leftProof none (catchExPostpone := false)
  let uncastProof ← Term.elabTerm uncastProof none (catchExPostpone := false)
  let rightProof ← Term.elabTerm rightProof none (catchExPostpone := false)
  let associationProof ← Term.elabTerm associationProof none (catchExPostpone := false)
  let sourceProof ← phiNativeNoRecovery025 sourceProof
  let leftProof ← phiNativeNoRecovery025 leftProof
  let uncastProof ← phiNativeNoRecovery025 uncastProof
  let rightProof ← phiNativeNoRecovery025 rightProof
  let associationProof ← phiNativeNoRecovery025 associationProof
  let (sourceType, sourceLeft, sourceRight) ← phiNativeStoredEq018 sourceProof
  let (leftSourceType, comparedSourceLeft, nativeType, nativeLeft) ←
    phiNativeStoredHEq027 leftProof
  let (uncastType, uncastLeft, uncastRight) ← phiNativeStoredEq018 uncastProof
  let (rightSourceType, comparedUncastRight, rightNativeType, nativeAssociated) ←
    phiNativeStoredHEq027 rightProof
  let (associationType, nativeRight, associationRight) ←
    phiNativeStoredEq018 associationProof
  let same := fun (a b : Expr) => a.consumeMData.headBeta.equal b.consumeMData.headBeta
  unless same sourceType leftSourceType && same sourceType uncastType &&
      same sourceType rightSourceType do
    throwError "Native027 refused different stored source/left/uncast/right carrier vectors."
  unless same nativeType rightNativeType && same nativeType associationType do
    throwError "Native027 refused different stored native left/right/association carriers."
  unless same sourceLeft comparedSourceLeft && same sourceRight uncastLeft &&
      same uncastRight comparedUncastRight && same nativeAssociated associationRight do
    throwError "Native027 refused changed shared actual endpoint values."
  let args := #[sourceType, nativeType, sourceLeft, sourceRight, uncastRight,
    nativeLeft, nativeRight, nativeAssociated, sourceProof, leftProof,
    uncastProof, rightProof, associationProof]
  -- All thirteen arguments are supplied. Resolve universe parameters,
  -- then instantiate by mkAppN using precisely the same complete vector.
  let application ← mkAppOptM ``phiNativeSquareEndpointAssembly027 (args.map some)
  let proof ← phiNativeNoRecovery025 (mkAppN application.getAppFn args)
  let (resultType, resultLeft, resultRight) ← phiNativeStoredEq018 proof
  unless same resultType nativeType && same resultLeft nativeLeft &&
      same resultRight nativeRight do
    throwError "Native027 refused changed native result endpoints."
  logInfo "Native027 ordinary endpoint assembly uses all13 exact stored vectors; explicit source/left/uncast/right/association proof values."
  return proof

/-- Final original literal proposition must have exactly the assembled stored
carrier and both endpoints. This is a checked identity, not a conversion bypass. -/
elab "phi_native_literal_square027% " supplied:term " using " literal:term : term => do
  let supplied ← Term.elabTerm supplied none (catchExPostpone := false)
  let literal ← Term.elabTerm literal none (catchExPostpone := false)
  let supplied ← phiNativeNoRecovery025 supplied
  let literal ← phiNativeNoRecovery025 literal
  let (sourceType, sourceLeft, sourceRight) ← phiNativeStoredEq018 supplied
  let some (targetType, targetLeft, targetRight) :=
      (← whnf literal).consumeMData.headBeta.eq?
    | throwError "Native027 expected original literal native Eq proposition."
  let same := fun (a b : Expr) => a.consumeMData.headBeta.equal b.consumeMData.headBeta
  unless same sourceType targetType && same sourceLeft targetLeft &&
      same sourceRight targetRight do
    throwError "Native027 refused changing literal native header carrier or endpoints."
  logInfo "Native027 assembled result is exact original literal native proposition vector."
  return supplied

end

private theorem actualOriginalGlobalPhiNativeFullSquareAssemblyOwn027
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_square_assembly027%
      (actualOriginalGlobalPhiNativeFullSquareInferred010 p hp P hP s)
      using (actualOriginalGlobalPhiNativeLeftEndpointHEq025 p hp P hP s)
      then (actualOriginalGlobalPhiNativeRightUncastPoint026 p hp P hP s)
      along (actualOriginalGlobalPhiNativeRightEndpointHEq027 p hp P hP s)
      and (actualOriginalGlobalPhiNativeMappedAssociationLiteral025 p hp P hP s)) :=
  phi_native_square_assembly027%
    (actualOriginalGlobalPhiNativeFullSquareInferred010 p hp P hP s)
    using (actualOriginalGlobalPhiNativeLeftEndpointHEq025 p hp P hP s)
    then (actualOriginalGlobalPhiNativeRightUncastPoint026 p hp P hP s)
    along (actualOriginalGlobalPhiNativeRightEndpointHEq027 p hp P hP s)
    and (actualOriginalGlobalPhiNativeMappedAssociationLiteral025 p hp P hP s)


meta section
open Lean Meta Elab Term

/-- Check exact flat native Eq vectors but RETAIN literal proposition Q as the
unexpanded argument of Eq.refl. Ordinary declaration checking must verify P=Q;
this isolates header conversion from the assembled proof VALUE. -/
elab "phi_native_folded_type_eq029% " supplied:term " using " literal:term : term => do
  let supplied ← Term.elabTerm supplied none (catchExPostpone := false)
  let literal ← Term.elabTerm literal none (catchExPostpone := false)
  let supplied ← phiNativeNoRecovery025 supplied
  let literal ← phiNativeNoRecovery025 literal
  let (sourceType, sourceLeft, sourceRight) ← phiNativeStoredEq018 supplied
  let some (targetType, targetLeft, targetRight) :=
      (← whnf literal).consumeMData.headBeta.eq?
    | throwError "Native029 expected exact original literal Eq proposition."
  let same := fun (a b : Expr) => a.consumeMData.headBeta.equal b.consumeMData.headBeta
  unless same sourceType targetType && same sourceLeft targetLeft &&
      same sourceRight targetRight do
    throwError "Native029 refused changed original literal native proposition vectors."
  let literalType ← inferType literal
  unless literalType.consumeMData.equal (mkSort Level.zero) do
    throwError "Native029 expected literal proposition of Sort0."
  -- Eq on propositions has universe1; Q is left folded in the proof term.
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``Eq.refl [Level.succ Level.zero])
      #[mkSort Level.zero, literal])
  logInfo "Native029 exact native vectors match; standalone ordinary proposition equality retains folded Q on both Eq.refl endpoints."
  return proof

/-- Consume actual TypeEquality029 proof VALUE with its OWN stored P/Q vector.
Q must still be the original literal proposition application, not its whnf. -/
elab "phi_native_folded_proof029% " supplied:term
    " using " typeEquality:term " along " literal:term : term => do
  let supplied ← Term.elabTerm supplied none (catchExPostpone := false)
  let typeEquality ← Term.elabTerm typeEquality none (catchExPostpone := false)
  let literal ← Term.elabTerm literal none (catchExPostpone := false)
  let supplied ← phiNativeNoRecovery025 supplied
  let typeEquality ← phiNativeNoRecovery025 typeEquality
  let literal ← phiNativeNoRecovery025 literal
  let sourceProposition ← inferType supplied
  let (propositionType, storedSource, storedLiteral) ← phiNativeStoredEq018 typeEquality
  unless propositionType.consumeMData.equal (mkSort Level.zero) &&
      storedSource.consumeMData.equal sourceProposition.consumeMData &&
      storedLiteral.consumeMData.equal literal.consumeMData do
    throwError "Native029 refused changed stored source TYPE or folded literal proposition."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``Eq.mp [Level.zero])
      #[storedSource, storedLiteral, typeEquality, supplied])
  let proofType ← inferType proof
  unless proofType.consumeMData.equal literal.consumeMData do
    throwError "Native029 refused unfolded/replaced result proposition."
  logInfo "Native029 Eq.mp consumes exact own stored P/Q and proof values; result Q remains folded original literal proposition."
  return proof

end

private theorem actualOriginalGlobalPhiNativeHeaderTypeEquality029
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    (type_of% (actualOriginalGlobalPhiNativeFullSquareAssemblyOwn027 p hp P hP s)) =
      actualOriginalGlobalPhiNativeHeaderProposition016 p hp P hP s :=
  phi_native_folded_type_eq029%
    (actualOriginalGlobalPhiNativeFullSquareAssemblyOwn027 p hp P hP s)
    using (actualOriginalGlobalPhiNativeHeaderProposition016 p hp P hP s)

private theorem actualOriginalGlobalPhiNativeFoldedLiteralProof029
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    actualOriginalGlobalPhiNativeHeaderProposition016 p hp P hP s :=
  phi_native_folded_proof029%
    (actualOriginalGlobalPhiNativeFullSquareAssemblyOwn027 p hp P hP s)
    using (actualOriginalGlobalPhiNativeHeaderTypeEquality029 p hp P hP s)
    along (actualOriginalGlobalPhiNativeHeaderProposition016 p hp P hP s)

private lemma actualOriginalGlobalPhiNativeFullSquareSection027
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let Etw := actualOriginalQuadraticConormalPointChartIso p hp P hP
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    G.map Etw.hom z = G.map (cJ ≫ Ej.hom) z := by
  -- Actual original elaborated lets (030), retaining their local native types.
  -- Read the own source proof with no target type; comparison is on this local
  -- body, not on the stored proof-abstracted Prop016 let telescope.
  intro C I R L q f j J T G z cJ Etw Ej
  basis_full_exact142
    (actualOriginalGlobalPhiNativeFullSquareAssemblyOwn027 p hp P hP s)

private lemma actualOriginalGlobalPhiNativeJoinedFullCompatibility032
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      J (closedImmersionModule j) (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let x : RingHom.ker C.residue :=
      ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    let Etw := actualOriginalQuadraticConormalPointChartIso p hp P hP
    G.map Etw.hom z = G.map (cJ ≫ Ej.hom) z := by
  intro C I R L q f j J T G z cJ Es x sx Ej Etw
  basis_full_exact142
    (actualOriginalGlobalPhiNativeFullSquareAssemblyOwn027 p hp P hP s)

private lemma actualOriginalGlobalPhiNativeJoinedNativeCompatibility032
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      J (closedImmersionModule j) (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let x : RingHom.ker C.residue :=
      ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    let Etw := actualOriginalQuadraticConormalPointChartIso p hp P hP
    G.map Etw.hom z =
      actualModulePointSectionClass j (closedImmersionModule j) sx := by
  intro C I R L q f j J T G z cJ Es x sx Ej Etw
  basis_full_exact142
    (actualOriginalQuadraticConormalPointChartIso_section p hp P hP s)

meta section
open Lean Meta Elab Term

/-- Join two actual local compatibility proofs by SAME stored carrier/Etw-point
vectors. Complete Eq.symm/trans arguments and universes are used explicitly. -/
elab "phi_native_joined_own032% " fullProof:term " using " nativeProof:term : term => do
  let fullProof ← Term.elabTerm fullProof none (catchExPostpone := false)
  let nativeProof ← Term.elabTerm nativeProof none (catchExPostpone := false)
  let fullProof ← phiNativeNoRecovery025 fullProof
  let nativeProof ← phiNativeNoRecovery025 nativeProof
  let (fullType, wholeImage, untwistedImage) ← phiNativeStoredEq018 fullProof
  let (nativeType, nativeWholeImage, nativeSection) ← phiNativeStoredEq018 nativeProof
  unless fullType.consumeMData.equal nativeType.consumeMData &&
      wholeImage.consumeMData.equal nativeWholeImage.consumeMData do
    throwError "Native032 refused different stored original carrier/Etw-point vectors."
  let level ← getLevel fullType
  let reverseProof := mkAppN (mkConst ``Eq.symm [level])
    #[fullType, wholeImage, untwistedImage, fullProof]
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``Eq.trans [level])
      #[fullType, untwistedImage, wholeImage, nativeSection, reverseProof, nativeProof])
  let (resultType, resultLeft, resultRight) ← phiNativeStoredEq018 proof
  unless resultType.consumeMData.equal fullType.consumeMData &&
      resultLeft.consumeMData.equal untwistedImage.consumeMData &&
      resultRight.consumeMData.equal nativeSection.consumeMData do
    throwError "Native032 refused changed joined original endpoint vectors."
  logInfo "Native032 ordinary Eq.symm/trans consumes actual local Full/Native compatibility values at exact stored original carrier/Etw-point/section vectors."
  return proof

end

private theorem actualOriginalGlobalPhiNativeJoinedOwnAssembly032
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_joined_own032%
      (actualOriginalGlobalPhiNativeJoinedFullCompatibility032 p hp P hP s)
      using (actualOriginalGlobalPhiNativeJoinedNativeCompatibility032 p hp P hP s)) :=
  phi_native_joined_own032%
    (actualOriginalGlobalPhiNativeJoinedFullCompatibility032 p hp P hP s)
    using (actualOriginalGlobalPhiNativeJoinedNativeCompatibility032 p hp P hP s)

private lemma actualOriginalGlobalPhiNativeJoinedSection010
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      J (closedImmersionModule j) (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let x : RingHom.ker C.residue :=
      ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    G.map (cJ ≫ Ej.hom) z =
      actualModulePointSectionClass j (closedImmersionModule j) sx := by
  intro C I R L q f j J T G z cJ Es x sx Ej
  basis_full_exact142
    (actualOriginalGlobalPhiNativeJoinedOwnAssembly032 p hp P hP s)

private lemma actualOriginalGlobalPhiNativeFactoredIsoCompatibility033
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      J (closedImmersionModule j) (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let x : RingHom.ker C.residue :=
      ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    Ej = Es := by
  intro C I R L q f j J T G z cJ Es x sx Ej
  basis_full_exact142
    (actualOriginalUntwistedIdealPointChartIso_eq_factored p hp P hP)

meta section
open Lean Meta Elab Term

private structure PhiNativePointVectors033 where
  endpoint : Expr
  coeArgs : Array Expr
  accessor : Expr
  accessorArgs : Array Expr
  mapped : Expr
  mapArgs : Array Expr

private def phiNativePointVectors033 (endpoint : Expr) :
    Term.TermElabM PhiNativePointVectors033 := do
  let endpoint := endpoint.consumeMData.headBeta
  let ea := endpoint.getAppArgs
  unless endpoint.getAppFn.isConstOf ``DFunLike.coe && ea.size == 6 do
    throwError "Native033 expected original point coe6."
  let accessor := ea[4]!.consumeMData.headBeta
  let ha := accessor.getAppArgs
  unless (accessor.getAppFn.isConstOf ``CategoryTheory.ConcreteCategory.hom && ha.size == 9) ||
      (accessor.getAppFn.isConstOf ``ModuleCat.Hom.hom && ha.size == 5) do
    throwError "Native033 expected actual concrete9 or module5 accessor."
  let mapped := ha[ha.size - 1]!.consumeMData.headBeta
  let ma := mapped.getAppArgs
  unless mapped.getAppFn.isConstOf ``CategoryTheory.Functor.map && ma.size == 8 do
    throwError "Native033 expected original map8."
  return ⟨endpoint, ea, accessor, ha, mapped, ma⟩

/-- Instantiate existing generic007 by EXACT stored Joined scalar/category,
composite f/g, original point z and actual native section t vectors. -/
elab "phi_native_mapped_composite_own033% " supplied:term : term => do
  let supplied ← Term.elabTerm supplied none (catchExPostpone := false)
  let supplied ← phiNativeNoRecovery025 supplied
  let (_, joinedLeft, joinedRight) ← phiNativeStoredEq018 supplied
  let v ← phiNativePointVectors033 joinedLeft
  let composite := v.mapArgs[7]!.consumeMData.headBeta
  let ca := composite.getAppArgs
  unless composite.getAppFn.isConstOf ``CategoryTheory.CategoryStruct.comp && ca.size == 7 do
    throwError "Native033 expected actual original composite7."
  let destination := v.mapArgs[2]!.consumeMData.headBeta
  let da := destination.getAppArgs
  unless destination.getAppFn.isConstOf ``ModuleCat && da.size == 2 do
    throwError "Native033 expected actual ModuleCat scalar/ring vector."
  unless ca[0]!.consumeMData.equal v.mapArgs[0]!.consumeMData &&
      ca[2]!.consumeMData.equal v.mapArgs[5]!.consumeMData &&
      ca[4]!.consumeMData.equal v.mapArgs[6]!.consumeMData do
    throwError "Native033 refused changed actual composite/functor object vectors."
  let args := #[da[0]!, da[1]!, v.mapArgs[0]!, v.mapArgs[1]!, v.mapArgs[4]!,
    ca[2]!, ca[3]!, ca[4]!, ca[5]!, ca[6]!, v.coeArgs[5]!, joinedRight, supplied]
  let application ← mkAppOptM ``actualGlobalPhiMappedCompositeSection007 (args.map some)
  let proof ← phiNativeNoRecovery025 (mkAppN application.getAppFn args)
  let (_, resultLeft, resultRight) ← phiNativeStoredEq018 proof
  let outer ← phiNativePointVectors033 resultLeft
  let inner ← phiNativePointVectors033 outer.coeArgs[5]!
  unless outer.mapArgs[4]!.consumeMData.equal v.mapArgs[4]!.consumeMData &&
      outer.mapArgs[7]!.consumeMData.equal ca[6]!.consumeMData &&
      inner.mapArgs[4]!.consumeMData.equal v.mapArgs[4]!.consumeMData &&
      inner.mapArgs[7]!.consumeMData.equal ca[5]!.consumeMData &&
      inner.coeArgs[5]!.consumeMData.equal v.coeArgs[5]!.consumeMData &&
      resultRight.consumeMData.equal joinedRight.consumeMData do
    throwError "Native033 refused changed actual nested mapped values/section."
  logInfo "Native033 genericmappedComposite007 uses all13 exact Joined stored scalar/category/f/g/z/t/proof arguments."
  return proof

/-- Lift actual Ej=Es through EXACT stored Iso.hom/map/accessor/coe evaluator;
source point/section/scalars and native factory endpoints are unchanged. -/
elab "phi_native_factored_point_own033% " supplied:term
    " using " isoEquality:term : term => do
  let supplied ← Term.elabTerm supplied none (catchExPostpone := false)
  let isoEquality ← Term.elabTerm isoEquality none (catchExPostpone := false)
  let supplied ← phiNativeNoRecovery025 supplied
  let isoEquality ← phiNativeNoRecovery025 isoEquality
  let (pointType, originalPoint, _) ← phiNativeStoredEq018 supplied
  let (isoType, originalIso, factoredIso) ← phiNativeStoredEq018 isoEquality
  let v ← phiNativePointVectors033 originalPoint
  let hom := v.mapArgs[7]!.consumeMData.headBeta
  let ha := hom.getAppArgs
  unless hom.getAppFn.isConstOf ``CategoryTheory.Iso.hom && ha.size == 5 &&
      ha[4]!.consumeMData.equal originalIso.consumeMData do
    throwError "Native033 refused changed actual stored Iso.hom5/old iso vector."
  let evaluator ← withLocalDeclD `isoValue isoType fun isoValue => do
    let hom := mkAppN hom.getAppFn (ha.set! 4 isoValue)
    let mapped := mkAppN v.mapped.getAppFn (v.mapArgs.set! 7 hom)
    let accessor := mkAppN v.accessor.getAppFn
      (v.accessorArgs.set! (v.accessorArgs.size - 1) mapped)
    mkLambdaFVars #[isoValue] (mkAppN v.endpoint.getAppFn (v.coeArgs.set! 4 accessor))
  let isoLevel ← getLevel isoType
  let pointLevel ← getLevel pointType
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``congrArg [isoLevel, pointLevel])
      #[isoType, pointType, originalIso, factoredIso, evaluator, isoEquality])
  let (_, resultLeft, resultRight) ← phiNativeStoredEq018 proof
  unless resultLeft.consumeMData.headBeta.equal v.endpoint.consumeMData.headBeta do
    throwError "Native033 refused changed original point evaluator value."
  let result ← phiNativePointVectors033 resultRight
  let resultHom := result.mapArgs[7]!.consumeMData.headBeta
  unless resultHom.getAppFn.equal hom.getAppFn && resultHom.getAppArgs.size == 5 &&
      resultHom.getAppArgs[4]!.consumeMData.equal factoredIso.consumeMData &&
      result.coeArgs[5]!.consumeMData.equal v.coeArgs[5]!.consumeMData do
    throwError "Native033 refused replaced factored iso/inner point."
  logInfo "Native033 actual local Ej=Es lifted by full-vector congrArg through unchanged original Iso.hom/map/accessor/coe/inner point."
  return proof

elab "phi_native_source_own033% " supplied:term
    " using " evaluation:term : term => do
  let supplied ← Term.elabTerm supplied none (catchExPostpone := false)
  let evaluation ← Term.elabTerm evaluation none (catchExPostpone := false)
  let supplied ← phiNativeNoRecovery025 supplied
  let evaluation ← phiNativeNoRecovery025 evaluation
  let (pointType, oldPoint, nativeSection) ← phiNativeStoredEq018 supplied
  let (evaluationType, evaluationOld, factoredPoint) ← phiNativeStoredEq018 evaluation
  unless pointType.consumeMData.equal evaluationType.consumeMData &&
      oldPoint.consumeMData.headBeta.equal evaluationOld.consumeMData.headBeta do
    throwError "Native033 refused changed stored carrier/original mapped point."
  let level ← getLevel pointType
  let reverseProof := mkAppN (mkConst ``Eq.symm [level])
    #[pointType, evaluationOld, factoredPoint, evaluation]
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``Eq.trans [level])
      #[pointType, factoredPoint, oldPoint, nativeSection, reverseProof, supplied])
  logInfo "Native033 exact Eq.symm/trans consumes mapped-composite and actual factored evaluation proof values."
  return proof

end

private theorem actualOriginalGlobalPhiNativeMappedCompositeOwn033
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_mapped_composite_own033%
      (actualOriginalGlobalPhiNativeJoinedOwnAssembly032 p hp P hP s)) :=
  phi_native_mapped_composite_own033%
    (actualOriginalGlobalPhiNativeJoinedOwnAssembly032 p hp P hP s)

private theorem actualOriginalGlobalPhiNativeFactoredPointOwn033
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_factored_point_own033%
      (actualOriginalGlobalPhiNativeMappedCompositeOwn033 p hp P hP s)
      using (actualOriginalGlobalPhiNativeFactoredIsoCompatibility033 p hp P hP s)) :=
  phi_native_factored_point_own033%
    (actualOriginalGlobalPhiNativeMappedCompositeOwn033 p hp P hP s)
    using (actualOriginalGlobalPhiNativeFactoredIsoCompatibility033 p hp P hP s)

private theorem actualOriginalGlobalPhiNativeSourceOwnAssembly033
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_source_own033%
      (actualOriginalGlobalPhiNativeMappedCompositeOwn033 p hp P hP s)
      using (actualOriginalGlobalPhiNativeFactoredPointOwn033 p hp P hP s)) :=
  phi_native_source_own033%
    (actualOriginalGlobalPhiNativeMappedCompositeOwn033 p hp P hP s)
    using (actualOriginalGlobalPhiNativeFactoredPointOwn033 p hp P hP s)

private lemma actualOriginalGlobalPhiNativeSourceSection006
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      J (closedImmersionModule j) (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let x : RingHom.ker C.residue :=
      ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    G.map Es.hom (G.map cJ z) =
      actualModulePointSectionClass j (closedImmersionModule j) sx := by
  intro C I R L q f j J T G z cJ Es x sx
  basis_full_exact142
    (actualOriginalGlobalPhiNativeSourceOwnAssembly033 p hp P hP s)

meta section
open Lean Meta Elab Term

/-- Unfold ONLY the actual conormal-module definition observed in diagnostic039.
No other constant, local let, dictionary, carrier, map, or scalar is normalized.
Only raw guards use this view; ordinary emitted proof vectors are untouched. -/
private def phiNativeConormalAliasView040 (input : Expr) : Term.TermElabM Expr := do
  let info ← getConstInfo ``actualClosedImmersionConormalModule
  let .defnInfo definition := info
    | throwError "Native040 expected the existing actual conormal-module definition."
  return Expr.replace (fun node =>
    let args := node.getAppArgs
    match node.getAppFn with
    | .const name levels =>
      if name == ``actualClosedImmersionConormalModule && args.size == 3 &&
          levels.length == definition.levelParams.length then
        some ((mkAppN (definition.value.instantiateLevelParams
          definition.levelParams levels) args).headBeta)
      else none
    | _ => none) input

/-- Read only the actual stored comp_apply M1 domain or original coe6 domain.
Mode1 unfolds only the previously diagnosed conormal-module alias. -/
elab "phi_native_comp_domain042% " mode:num supplied:term : term => do
  unless mode.getNat < 3 do
    throwError "Native042 expected pointDomain0, conormalView1 or originalCoe2."
  let supplied ← Term.elabTerm supplied none (catchExPostpone := false)
  let supplied ← phiNativeNoRecovery025 supplied
  let (pointType, leftPoint, compositePoint) ← phiNativeStoredEq018 supplied
  let endpoint := compositePoint.consumeMData.headBeta
  let ea := endpoint.getAppArgs
  unless endpoint.getAppFn.isConstOf ``DFunLike.coe && ea.size == 6 do
    throwError "Native036 expected actual applied Kaehler RHS coe6."
  let composite := ea[4]!.consumeMData.headBeta
  let ca := composite.getAppArgs
  let .const compName compLevels := composite.getAppFn
    | throwError "Native036 RHS function is not a stored constant application."
  unless compName == ``LinearMap.comp do
    throwError "Native036 actual RHS function is {compName}, not LinearMap.comp."
  let compInfo ← getConstInfo ``LinearMap.comp
  let lawInfo ← getConstInfo ``LinearMap.comp_apply
  unless compInfo.levelParams.length == compLevels.length &&
      lawInfo.levelParams.length == compLevels.length do
    throwError "Native036 comp/comp_apply universe counts differ."
  let mut compType := compInfo.instantiateTypeLevelParams compLevels
  let mut lawType := lawInfo.instantiateTypeLevelParams compLevels
  for i in [:ca.size] do
    let .forallE _ compDomain compBody compBinder := compType
      | throwError "Native036 comp prefix ended early at {i}."
    let .forallE _ lawDomain lawBody lawBinder := lawType
      | throwError "Native036 comp_apply prefix ended early at {i}."
    unless compBinder == lawBinder && compDomain.consumeMData.equal lawDomain.consumeMData do
      throwError "Native036 different stored comp/comp_apply binder at {i}."
    compType := compBody.instantiate1 ca[i]!
    lawType := lawBody.instantiate1 ca[i]!
  let .forallE _ pointDomain _ _ := lawType
    | throwError "Native036 comp_apply lacks its final point binder."
  if mode.getNat == 0 then return pointDomain
  if mode.getNat == 1 then return ← phiNativeConormalAliasView040 ea[1]!
  return ea[1]!

end

private lemma actualOriginalGlobalPhiNativeCompDomainViewEq042
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    (phi_native_comp_domain042% 0 (congrArg (fun F => F (G.map cJ z))
      (actualOriginalGlobalConormalKaehlerComparison p hp P hP))) =
      (phi_native_comp_domain042% 1 (congrArg (fun F => F (G.map cJ z))
      (actualOriginalGlobalConormalKaehlerComparison p hp P hP))) := by
  intro C I R L q J T G z cJ
  basis_full_exact142
    (Eq.refl (phi_native_comp_domain042% 0 (congrArg (fun F => F (G.map cJ z))
      (actualOriginalGlobalConormalKaehlerComparison p hp P hP))))

meta section
open Lean Meta Elab Term

elab "phi_native_comp_apply_own043% " supplied:term " using " domainLaw:term : term => do
  let supplied ← Term.elabTerm supplied none (catchExPostpone := false)
  let supplied ← phiNativeNoRecovery025 supplied
  let domainLaw ← Term.elabTerm domainLaw none (catchExPostpone := false)
  let domainLaw ← phiNativeNoRecovery025 domainLaw
  let (domainCarrier, domainLeft, domainRight) ← phiNativeStoredEq018 domainLaw
  let (pointType, leftPoint, compositePoint) ← phiNativeStoredEq018 supplied
  let endpoint := compositePoint.consumeMData.headBeta
  let ea := endpoint.getAppArgs
  unless endpoint.getAppFn.isConstOf ``DFunLike.coe && ea.size == 6 do
    throwError "Native036 expected actual applied Kaehler RHS coe6."
  let composite := ea[4]!.consumeMData.headBeta
  let ca := composite.getAppArgs
  let .const compName compLevels := composite.getAppFn
    | throwError "Native036 RHS function is not a stored constant application."
  unless compName == ``LinearMap.comp do
    throwError "Native036 actual RHS function is {compName}, not LinearMap.comp."
  let compInfo ← getConstInfo ``LinearMap.comp
  let lawInfo ← getConstInfo ``LinearMap.comp_apply
  unless compInfo.levelParams.length == compLevels.length &&
      lawInfo.levelParams.length == compLevels.length do
    throwError "Native036 comp/comp_apply universe counts differ."
  let mut compType := compInfo.instantiateTypeLevelParams compLevels
  let mut lawType := lawInfo.instantiateTypeLevelParams compLevels
  for i in [:ca.size] do
    let .forallE _ compDomain compBody compBinder := compType
      | throwError "Native036 comp prefix ended early at {i}."
    let .forallE _ lawDomain lawBody lawBinder := lawType
      | throwError "Native036 comp_apply prefix ended early at {i}."
    unless compBinder == lawBinder && compDomain.consumeMData.equal lawDomain.consumeMData do
      throwError "Native036 different stored comp/comp_apply binder at {i}."
    compType := compBody.instantiate1 ca[i]!
    lawType := lawBody.instantiate1 ca[i]!
  let .forallE _ pointDomain _ _ := lawType
    | throwError "Native036 comp_apply lacks its final point binder."
  let coeDomainView ← phiNativeConormalAliasView040 ea[1]!
  let domainSort ← inferType pointDomain
  unless domainCarrier.consumeMData.equal domainSort.consumeMData &&
      domainLeft.consumeMData.equal pointDomain.consumeMData &&
      domainRight.consumeMData.equal coeDomainView.consumeMData do
    throwError "Native043 domain Eq042 is not on these exact stored comp/coercion vectors."
  let law ← phiNativeNoRecovery025
    (mkAppN (mkConst ``LinearMap.comp_apply compLevels) (ca.push ea[5]!))
  logInfo "Native043 existing comp_apply emitted on all original21 comp arguments and original point; strict stored DomainEq042 endpoints verified."
  return law

/-- Select original evaluated Kähler RHS, unfolding ONLY the conormal alias.
No equation, instance, category, map or point value is substituted. -/
elab "phi_native_comp_rhs_view043% " supplied:term : term => do
  let supplied ← Term.elabTerm supplied none (catchExPostpone := false)
  let supplied ← phiNativeNoRecovery025 supplied
  let (_, _, endpoint) ← phiNativeStoredEq018 supplied
  return ← phiNativeConormalAliasView040 endpoint.consumeMData.headBeta

end

private lemma actualOriginalGlobalPhiNativeCompApplyOwn043
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_infer010% (letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    phi_native_comp_apply_own043% (congrArg (fun F => F (G.map cJ z))
      (actualOriginalGlobalConormalKaehlerComparison p hp P hP)) using
      (actualOriginalGlobalPhiNativeCompDomainViewEq042 p hp P hP s))) :=
  phi_native_infer010% (letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    phi_native_comp_apply_own043% (congrArg (fun F => F (G.map cJ z))
      (actualOriginalGlobalConormalKaehlerComparison p hp P hP)) using
      (actualOriginalGlobalPhiNativeCompDomainViewEq042 p hp P hP s))

meta section
open Lean Meta Elab Term

/-- The exact output-carrier path reported by the failed LeftHEq043 check. -/
private def phiNativeChartProjectionPair044 (leftType rightType : Expr) :
    MetaM (Expr × Expr) := do
  let mut left := leftType.consumeMData.headBeta
  let mut right := rightType.consumeMData.headBeta
  for (index, arity, headName) in
      #[(2, 3, ``ModuleCat.carrier), (5, 6, ``CategoryTheory.Functor.obj),
        (5, 6, ``CategoryTheory.Functor.obj), (3, 4, ``schemeRelativeDifferentials),
        (2, 3, ``AlgebraicGeometry.Spec.map), (4, 5, ``CommRingCat.ofHom)] do
    let la := left.getAppArgs
    let ra := right.getAppArgs
    unless left.getAppFn.isConstOf headName && right.getAppFn.isConstOf headName &&
        la.size == arity && ra.size == arity do
      throwError m!"Native044 unexpected stored projection path at {headName}/{arity}, arg{index}; left={left.getAppFn}/{la.size}, right={right.getAppFn}/{ra.size}."
    left := la[index]!.consumeMData.headBeta
    right := ra[index]!.consumeMData.headBeta
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless left.getAppFn.isConstOf ``Algebra.algebraMap && la.size == 5 &&
      right.getAppFn.isConstOf ``AllCharacteristics.HomogeneousProjective.chartBaseMap &&
      ra.size == 5 do
    throwError m!"Native044 not the diagnosed algebraMap5/chartBaseMap5 boundary; left={left.getAppFn}/{la.size}, right={right.getAppFn}/{ra.size}."
  let chartRing := la[1]!.consumeMData
  let chartArgs := chartRing.getAppArgs
  unless chartRing.getAppFn.isConstOf ``AllCharacteristics.HomogeneousProjective.ChartRing &&
      chartArgs.size == 5 && la[0]!.consumeMData.equal ra[0]!.consumeMData do
    throwError "Native044 not the original K/ChartRing projection boundary."
  for i in [:ra.size] do
    unless chartArgs[i]!.consumeMData.equal ra[i]!.consumeMData do
      throwError m!"Native044 original ChartRing/chartBaseMap argument{i} differs; source={chartArgs[i]!}, target={ra[i]!}."
  logInfo m!"Native044 SAME original chart vectors verified; algebra instance={la[4]!}."
  return (left, right)

elab "phi_native_chart_projection044% " supplied:term " using " evaluated:term : term => do
  let supplied ← Term.elabTerm supplied none (catchExPostpone := false)
  let evaluated ← Term.elabTerm evaluated none (catchExPostpone := false)
  let supplied ← phiNativeNoRecovery025 supplied
  let evaluated ← phiNativeNoRecovery025 evaluated
  let (_, sourcePoint, _) ← phiNativeStoredEq018 supplied
  let (_, _, originalPoint) ← phiNativeStoredEq018 evaluated
  let originalPoint ← phiNativeConormalAliasView040 originalPoint.consumeMData.headBeta
  let (left, right) ← phiNativeChartProjectionPair044
    (← inferType sourcePoint) (← inferType originalPoint)
  return ← mkHEq left right

end

private lemma actualOriginalGlobalPhiNativeChartProjectionHEq044
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    phi_native_chart_projection044% (actualOriginalGlobalPhiNativeCompApplyOwn043 p hp P hP s) using (congrArg (fun F => F (G.map cJ z))
      (actualOriginalGlobalConormalKaehlerComparison p hp P hP)) := by
  intro C I R L q J T G z cJ
  rfl

meta section
open Lean Meta Elab Term

/-- View BOTH actual points through the SAME existing conormal-module definition.
No q/j identification: each stored occurrence retains its own original three
arguments, universe vector and immersion. -/
elab "phi_native_comp_lhs_view045% " supplied:term : term => do
  let supplied ← Term.elabTerm supplied none (catchExPostpone := false)
  let supplied ← phiNativeNoRecovery025 supplied
  let (_, endpoint, _) ← phiNativeStoredEq018 supplied
  return ← phiNativeConormalAliasView040 endpoint.consumeMData.headBeta

end

private lemma actualOriginalGlobalPhiNativeCompOwnConormalAliasHEq045
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    HEq (phi_native_eq_endpoint017% 0 0
      (actualOriginalGlobalPhiNativeCompApplyOwn043 p hp P hP s))
      (phi_native_comp_lhs_view045% (actualOriginalGlobalPhiNativeCompApplyOwn043 p hp P hP s)) := by
  rfl

private lemma actualOriginalGlobalPhiNativeCompRhsConormalAliasHEq045
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    HEq (phi_native_comp_rhs_view043% (congrArg (fun F => F (G.map cJ z))
      (actualOriginalGlobalConormalKaehlerComparison p hp P hP)))
      (phi_native_eq_endpoint017% 0 1 (congrArg (fun F => F (G.map cJ z))
      (actualOriginalGlobalConormalKaehlerComparison p hp P hP))) := by
  intro C I R L q J T G z cJ
  rfl

namespace PhiNativeChartSeedEngineNamespace044

namespace PhiNativeChartSeed044Diamond145
universe uChartSeed044

/- These are two projections of the SAME commutative-ring structure.
The actual caller parents are compared separately by ordinary congruence. -/
private theorem commRing_semiring_eq {R : Type uChartSeed044} (c : CommRing R) :
    @Ring.toSemiring R (@CommRing.toRing R c) =
      @CommSemiring.toSemiring R (@CommRing.toCommSemiring R c) := by
  rfl

end PhiNativeChartSeed044Diamond145

namespace PhiNativeChartSeed044Diamond146
universe uChartSeed044

/- Compare exactly the diagnosed semiring projections of ONE field. Native
field/ring parents at the actual frontier are proved compatible separately. -/
private theorem field_semiring_eq {R : Type uChartSeed044} (c : Field R) :
    @DivisionSemiring.toSemiring R
      (@Semifield.toDivisionSemiring R (@Field.toSemifield R c)) =
      @CommSemiring.toSemiring R
        (@CommRing.toCommSemiring R (@Field.toCommRing R c)) := by
  rfl

/- The newly diagnosed endpoint uses the Ring projection of the SAME field,
rather than its CommSemiring projection. Actual ring parents are certified
separately by the bounded dispatcher; this lemma assumes no parent equality. -/
private theorem field_ring_semiring_eq152 {R : Type uChartSeed044} (c : Field R) :
    @DivisionSemiring.toSemiring R
      (@Semifield.toDivisionSemiring R (@Field.toSemifield R c)) =
      @Ring.toSemiring R (@CommRing.toRing R (@Field.toCommRing R c)) := by
  rfl

end PhiNativeChartSeed044Diamond146

namespace PhiNativeChartSeed044Diamond150
universe uChartSeed044 vChartSeed044

/- The two additive-monoid structures are projections of the SAME actual
submodule and additive-group parent. Actual parent data is compared separately. -/
private theorem submodule_addCommMonoid_eq
    (R : Type uChartSeed044) (M : Type vChartSeed044) [Ring R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) :
    @Submodule.addCommMonoid R M
      (@Ring.toSemiring R inferInstance)
      (@AddCommGroup.toAddCommMonoid M inferInstance) inferInstance p =
    @AddCommGroup.toAddCommMonoid _
      (@Submodule.addCommGroup R M inferInstance inferInstance inferInstance p) := by
  rfl

end PhiNativeChartSeed044Diamond150

namespace PhiNativeChartSeed044Diamond153
universe uChartSeed044

/- The two diagnosed additive-monoid-with-one paths come from ONE ring.
The actual caller's ring/semiring parents remain separately certified. -/
private theorem ring_addMonoidWithOne_eq {R : Type uChartSeed044} (c : Ring R) :
    @AddGroupWithOne.toAddMonoidWithOne R (@Ring.toAddGroupWithOne R c) =
      @AddCommMonoidWithOne.toAddMonoidWithOne R
        (@NonAssocSemiring.toAddCommMonoidWithOne R
          (@Semiring.toNonAssocSemiring R (@Ring.toSemiring R c))) := by
  rfl

end PhiNativeChartSeed044Diamond153

namespace PhiNativeChartSeed044Diamond154
universe uChartSeed044

/- These are the two actual Ring parents of ONE Field. Caller carrier and
native CommRing parent compatibility are proved independently below. -/
private theorem field_ring_eq {R : Type uChartSeed044} (c : Field R) :
    @DivisionRing.toRing R (@Field.toDivisionRing R c) =
      @CommRing.toRing R (@Field.toCommRing R c) := by
  rfl

end PhiNativeChartSeed044Diamond154

namespace PhiNativeChartSeed044Coercion142
open CategoryTheory
universe uChartSeed044 vChartSeed044

/- The diagnosed ModuleCat wrapper is precisely its declared concrete hom.
This is a genuine ordinary data equality, checked by the enclosing kernel. -/
private theorem module_hom_eq_concrete
    {R : Type uChartSeed044} [Ring R] {M N : ModuleCat.{vChartSeed044} R} (f : M ⟶ N) :
    f.hom = ConcreteCategory.hom (C := ModuleCat.{vChartSeed044} R) f := by
  rfl

end PhiNativeChartSeed044Coercion142

noncomputable section
namespace PhiNativeChartSeed044Residue142
open AlgebraicGeometry
universe uChartSeed044

private theorem native_commRing_eq (S : Scheme.{uChartSeed044}) (x : S) :
    @Field.toCommRing (CommRingCat.carrier (S.residueField x))
      (Scheme.instFieldCarrierResidueField S x) =
    @CommRingCat.instCommRingObjForgetRingHomCarrier (S.residueField x) := by
  rfl

private theorem native_bundle_eq (S : Scheme.{uChartSeed044}) (x : S) :
    @CommRingCat.of (CommRingCat.carrier (S.residueField x))
      (@Field.toCommRing (CommRingCat.carrier (S.residueField x))
        (Scheme.instFieldCarrierResidueField S x)) = S.residueField x := by
  rfl

private theorem native_carrier_eq (S : Scheme.{uChartSeed044}) (x : S) :
    CommRingCat.carrier (S.residueField x) =
      @IsLocalRing.ResidueField (CommRingCat.carrier (S.presheaf.stalk x))
        (@CommRingCat.instCommRingObjForgetRingHomCarrier (S.presheaf.stalk x))
        (inferInstance : IsLocalRing (S.presheaf.stalk x)) := by
  rfl

private theorem native_field_heq (S : Scheme.{uChartSeed044}) (x : S) :
    HEq (Scheme.instFieldCarrierResidueField S x)
      (@IsLocalRing.ResidueField.field (CommRingCat.carrier (S.presheaf.stalk x))
        (@CommRingCat.instCommRingObjForgetRingHomCarrier (S.presheaf.stalk x))
        (inferInstance : IsLocalRing (S.presheaf.stalk x))) := by
  rfl

/-- The native bundled-ring carrier/instance roundtrip. -/
private theorem native_standard_bundle_eq (S : Scheme.{uChartSeed044}) (x : S) :
    @CommRingCat.of (CommRingCat.carrier (S.residueField x))
      (@CommRingCat.instCommRingObjForgetRingHomCarrier (S.residueField x)) =
      S.residueField x := by
  rfl

end PhiNativeChartSeed044Residue142
end

namespace PhiNativeChartSeed044Structural142

universe uChartSeed044 vChartSeed044

/-- Congruence for dependent function types with separate domains. -/
private theorem pi_eq
    {A A' : Sort uChartSeed044} (B : A → Sort vChartSeed044) (B' : A' → Sort vChartSeed044)
    (hA : A = A')
    (hB : ∀ a a', HEq a a' → B a = B' a') :
    (∀ a, B a) = (∀ a', B' a') := by
  cases hA
  have h : B = B' := funext fun a => hB a a (HEq.refl a)
  cases h
  rfl

/-- Congruence for functions with separate domains and dependent ranges. -/
private theorem lambda_heq
    {A A' : Sort uChartSeed044} {B : A → Sort vChartSeed044} {B' : A' → Sort vChartSeed044}
    (f : ∀ a, B a) (f' : ∀ a', B' a')
    (hA : A = A')
    (hB : ∀ a a', HEq a a' → B a = B' a')
    (hf : ∀ a a', HEq a a' → HEq (f a) (f' a')) : HEq f f' := by
  cases hA
  have h : B = B' := funext fun a => hB a a (HEq.refl a)
  cases h
  exact heq_of_eq (funext fun a => eq_of_heq (hf a a (HEq.refl a)))

end PhiNativeChartSeed044Structural142

meta section
namespace PhiNativeChartSeed044Structural142
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
  let proof := mkAppN (mkConst ``PhiNativeChartSeed044Residue142.native_commRing_eq levels) fieldArgs
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
  let proof := mkAppN (mkConst ``PhiNativeChartSeed044Residue142.native_commRing_eq levels) fieldArgs
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
  let proof := mkAppN (mkConst ``PhiNativeChartSeed044Residue142.native_bundle_eq levels) ra
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
  let proof := mkAppN (mkConst ``PhiNativeChartSeed044Residue142.native_carrier_eq levels) nativeArgs
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
  let proof := mkAppN (mkConst ``PhiNativeChartSeed044Residue142.native_field_heq levels) la
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
  let proof := mkAppN (mkConst ``PhiNativeChartSeed044Residue142.native_standard_bundle_eq levels) ra
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
  let proof := mkAppN (mkConst ``PhiNativeChartSeed044Diamond145.commRing_semiring_eq levels) lpa
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
      ``PhiNativeChartSeed044Diamond146.field_ring_semiring_eq152
    else ``PhiNativeChartSeed044Diamond146.field_semiring_eq
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
  let proof := mkAppN (mkConst ``PhiNativeChartSeed044Diamond150.submodule_addCommMonoid_eq levels) ga
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
    (mkConst ``PhiNativeChartSeed044Diamond153.ring_addMonoidWithOne_eq levels) rpa
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
  let proof := mkAppN (mkConst ``PhiNativeChartSeed044Diamond154.field_ring_eq levels) fpa
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
    let uChartSeed044 ← getLevel A
    let leftFamily ← withLocalDecl n bi A fun a => do
      mkLambdaFVars #[a] (B.instantiate1 a)
    let rightFamily ← withLocalDecl n bi A' fun a' => do
      mkLambdaFVars #[a'] (B'.instantiate1 a')
    let vChartSeed044 ← withLocalDecl n bi A fun a => getLevel (B.instantiate1 a)
    let hB ← withLocalDecl n bi A fun a => do
      withLocalDecl (n.appendAfter "'") bi A' fun a' => do
        withLocalDeclD `h (← mkHEq a a') fun h => do
          let bodyEq ← mkEqOfHEq (← structuralHEq
            (B.instantiate1 a) (B'.instantiate1 a') (depth - 1)
            (locals.push (a, a', h)) (path ++ ".body"))
          mkLambdaFVars #[a, a', h] bodyEq
    let eq := mkAppN (mkConst ``pi_eq [uChartSeed044, vChartSeed044])
      #[A, A', leftFamily, rightFamily, hA, hB]
    modify fun s => { s with binderSteps := s.binderSteps + 1 }
    return ← cache left0 right0 (← mkHEqOfEq eq)
  | .lam n A body bi, .lam _ A' body' _ =>
    let hA ← mkEqOfHEq (← structuralHEq A A' (depth - 1) locals (path ++ ".binderType"))
    let uChartSeed044 ← getLevel A
    let B ← withLocalDecl n bi A fun a => do
      mkLambdaFVars #[a] (← inferType (body.instantiate1 a))
    let B' ← withLocalDecl n bi A' fun a' => do
      mkLambdaFVars #[a'] (← inferType (body'.instantiate1 a'))
    let vChartSeed044 ← withLocalDecl n bi A fun a => do getLevel (← inferType (body.instantiate1 a))
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
    let h := mkAppN (mkConst ``lambda_heq [uChartSeed044, vChartSeed044])
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

end PhiNativeChartSeed044Structural142
end

end PhiNativeChartSeedEngineNamespace044

meta section
open Lean Meta Elab Tactic

/-- Cache ONLY the exact passed original chart projection HEq and its reverse.
Everything else uses the unchanged copied full142 bounded dispatcher. -/
elab "phi_native_chart_seeded_exact044 " supplied:term " using " suppliedSeed:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← Term.elabTerm supplied none (catchExPostpone := false)
    let source ← phiNativeNoRecovery025 source
    let sourceType ← instantiateMVars (← inferType source)
    let target ← instantiateMVars (← goal.getType)
    let seed ← Term.elabTerm suppliedSeed none (catchExPostpone := false)
    let seed ← phiNativeNoRecovery025 seed
    let (_, seedLeft, _, seedRight) ← phiNativeStoredHEq027 seed
    let some (leftType, _, rightType, _) := target.consumeMData.headBeta.heq?
      | throwError "Native044 expected the actual endpoint HEq target."
    let (actualLeft, actualRight) ← phiNativeChartProjectionPair044 leftType rightType
    unless seedLeft.consumeMData.equal actualLeft.consumeMData &&
        seedRight.consumeMData.equal actualRight.consumeMData do
      throwError "Native044 refuses a chart projection seed on different actual stored endpoints."
    let reverseSeed ← mkHEqSymm seed
    let (heq, state) ←
      (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.structuralHEq
        sourceType target 96 #[] "full142").run
          { pairs := #[(seedLeft, seedRight, seed), (seedRight, seedLeft, reverseSeed)] }
    let typeProof ← mkEqOfHEq heq
    let proof := mkAppN (mkConst ``Eq.mp [Level.zero])
      #[sourceType, target, typeProof, source]
    let proof ← phiNativeNoRecovery025 proof
    logInfo m!"Native044 seeded ordinary compatibility emitted: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruence steps={state.congrSteps}, binders={state.binderSteps}, unused traversal budget={state.remaining}."
    goal.assign proof
    replaceMainGoal []

end

private lemma actualOriginalGlobalPhiNativeCompApplyViewedLeftHEq045
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    HEq (phi_native_comp_lhs_view045% (actualOriginalGlobalPhiNativeCompApplyOwn043 p hp P hP s))
      (phi_native_comp_rhs_view043% (congrArg (fun F => F (G.map cJ z))
      (actualOriginalGlobalConormalKaehlerComparison p hp P hP))) := by
  intro C I R L q J T G z cJ
  phi_native_chart_seeded_exact044
    (HEq.refl (phi_native_comp_lhs_view045% (actualOriginalGlobalPhiNativeCompApplyOwn043 p hp P hP s))) using
    (actualOriginalGlobalPhiNativeChartProjectionHEq044 p hp P hP s)
/-- Recover literal original evaluated endpoints before any native header comparison.
Every carrier and point is explicit; no definitional carrier conversion is used. -/
private theorem phiNativeCompTransport046.{uTransport046}
    (A B C D : Sort uTransport046)
    (a r : A) (rv : B) (cv : C) (c n : D)
    (hAt : a = r) (hRhs : HEq rv r) (hView : HEq cv rv)
    (hOwn : HEq c cv) (hComp : c = n) : HEq a n := by
  exact (heq_of_eq hAt).trans
    (hRhs.symm.trans (hView.symm.trans (hOwn.symm.trans (heq_of_eq hComp))))

meta section
open Lean Meta Elab Term

elab "phi_native_comp_literal_assembly046% " compLaw:term
    " with_alias " ownAlias:term " with_view " viewLaw:term
    " with_rhs " rhsAlias:term " at_evaluation " evaluated:term : term => do
  let compLaw ← Term.elabTerm compLaw none (catchExPostpone := false)
  let ownAlias ← Term.elabTerm ownAlias none (catchExPostpone := false)
  let viewLaw ← Term.elabTerm viewLaw none (catchExPostpone := false)
  let rhsAlias ← Term.elabTerm rhsAlias none (catchExPostpone := false)
  let evaluated ← Term.elabTerm evaluated none (catchExPostpone := false)
  let compLaw ← phiNativeNoRecovery025 compLaw
  let ownAlias ← phiNativeNoRecovery025 ownAlias
  let viewLaw ← phiNativeNoRecovery025 viewLaw
  let rhsAlias ← phiNativeNoRecovery025 rhsAlias
  let evaluated ← phiNativeNoRecovery025 evaluated
  let (D, c, n) ← phiNativeStoredEq018 compLaw
  let (ownD, ownC, C, cv) ← phiNativeStoredHEq027 ownAlias
  let (viewC, viewCv, B, rv) ← phiNativeStoredHEq027 viewLaw
  let (rhsB, rhsRv, A, r) ← phiNativeStoredHEq027 rhsAlias
  let (evalA, a, evalR) ← phiNativeStoredEq018 evaluated
  unless D.consumeMData.equal ownD.consumeMData && c.consumeMData.equal ownC.consumeMData &&
      C.consumeMData.equal viewC.consumeMData && cv.consumeMData.equal viewCv.consumeMData &&
      B.consumeMData.equal rhsB.consumeMData && rv.consumeMData.equal rhsRv.consumeMData &&
      A.consumeMData.equal evalA.consumeMData && r.consumeMData.equal evalR.consumeMData do
    throwError "Native046 component carrier/point vectors do not exactly join."
  let level ← getLevel A
  unless level == (← getLevel B) && level == (← getLevel C) && level == (← getLevel D) do
    throwError "Native046 actual point sort levels differ."
  let args := #[A, B, C, D, a, r, rv, cv, c, n,
    evaluated, rhsAlias, viewLaw, ownAlias, compLaw]
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``phiNativeCompTransport046 [level]) args)
  let (_, resultLeft, _, resultRight) ← phiNativeStoredHEq027 proof
  unless resultLeft.consumeMData.equal a.consumeMData &&
      resultRight.consumeMData.equal n.consumeMData do
    throwError "Native046 altered literal original evaluated LHS or own normalized RHS."
  logInfo "Native046 ordinary literal HEq assembly consumes all15 stored arguments and all5 actual passed Eq/HEq component values."
  return proof

end

private lemma actualOriginalGlobalPhiNativeKaehlerEvaluatedOwn049
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_infer010% (letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    congrArg (fun F => F (G.map cJ z))
      (actualOriginalGlobalConormalKaehlerComparison p hp P hP))) :=
  phi_native_infer010% (letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    congrArg (fun F => F (G.map cJ z))
      (actualOriginalGlobalConormalKaehlerComparison p hp P hP))

meta section
open Lean Meta Elab Term

/-- Exact endpoint comparison; preserve both actual original points and raw carrier. -/
elab "phi_native_comp_rhs_join049% " rhsAlias:term " with_evaluation " evaluated:term : term => do
  let rhsAlias ← Term.elabTerm rhsAlias none (catchExPostpone := false)
  let evaluated ← Term.elabTerm evaluated none (catchExPostpone := false)
  let rhsAlias ← phiNativeNoRecovery025 rhsAlias
  let evaluated ← phiNativeNoRecovery025 evaluated
  let (_, _, A, originalRhs) ← phiNativeStoredHEq027 rhsAlias
  let (evalA, _, evaluatedRhs) ← phiNativeStoredEq018 evaluated
  unless A.consumeMData.equal evalA.consumeMData do
    throwError "Native049 RHS comparison refuses different actual output carriers."
  logInfo m!"Native049 exact output carrier retained; stored original RHS vs closed evaluated RHS raw={originalRhs.consumeMData.equal evaluatedRhs.consumeMData}."
  return mkAppN (mkConst ``Eq [← getLevel A]) #[A, originalRhs, evaluatedRhs]

elab "phi_native_comp_rhs_stored_point049% " rhsAlias:term : term => do
  let rhsAlias ← Term.elabTerm rhsAlias none (catchExPostpone := false)
  let rhsAlias ← phiNativeNoRecovery025 rhsAlias
  let (_, _, _, originalRhs) ← phiNativeStoredHEq027 rhsAlias
  return originalRhs

end

private lemma actualOriginalGlobalPhiNativeRhsEvaluationPointEq049
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    phi_native_comp_rhs_join049%
      (actualOriginalGlobalPhiNativeCompRhsConormalAliasHEq045 p hp P hP s) with_evaluation
      (actualOriginalGlobalPhiNativeKaehlerEvaluatedOwn049 p hp P hP s) := by
  basis_full_exact142 (Eq.refl (phi_native_comp_rhs_stored_point049%
    (actualOriginalGlobalPhiNativeCompRhsConormalAliasHEq045 p hp P hP s)))

private theorem phiNativeEvaluationRhsTransport049.{uRhsTransport049}
    (A : Sort uRhsTransport049) (a r evaluatedRhs : A)
    (hAt : a = evaluatedRhs) (hPoint : r = evaluatedRhs) : a = r := by
  exact hAt.trans hPoint.symm

meta section
open Lean Meta Elab Term

elab "phi_native_comp_evaluation_transport049% " evaluated:term " using " pointCompatibility:term : term => do
  let evaluated ← Term.elabTerm evaluated none (catchExPostpone := false)
  let pointCompatibility ← Term.elabTerm pointCompatibility none (catchExPostpone := false)
  let evaluated ← phiNativeNoRecovery025 evaluated
  let pointCompatibility ← phiNativeNoRecovery025 pointCompatibility
  let (A, a, evaluatedRhs) ← phiNativeStoredEq018 evaluated
  let (pointA, r, pointRhs) ← phiNativeStoredEq018 pointCompatibility
  unless A.consumeMData.equal pointA.consumeMData &&
      evaluatedRhs.consumeMData.equal pointRhs.consumeMData do
    throwError "Native049 refuses a point compatibility proof on different stored carrier/RHS vectors."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``phiNativeEvaluationRhsTransport049 [← getLevel A])
      #[A, a, r, evaluatedRhs, evaluated, pointCompatibility])
  let (actualA, actualLeft, actualRight) ← phiNativeStoredEq018 proof
  unless actualA.consumeMData.equal A.consumeMData &&
      actualLeft.consumeMData.equal a.consumeMData && actualRight.consumeMData.equal r.consumeMData do
    throwError "Native049 changed original evaluated LHS or exact proven stored RHS."
  logInfo "Native049 ordinary Eq.trans endpoint adapter emitted with all6 original stored arguments and actual point equality."
  return proof

end

private lemma actualOriginalGlobalPhiNativeCompLiteralHEqOwn049
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_infer010% (letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    phi_native_comp_literal_assembly046%
      (actualOriginalGlobalPhiNativeCompApplyOwn043 p hp P hP s)
      with_alias (actualOriginalGlobalPhiNativeCompOwnConormalAliasHEq045 p hp P hP s)
      with_view (actualOriginalGlobalPhiNativeCompApplyViewedLeftHEq045 p hp P hP s)
      with_rhs (actualOriginalGlobalPhiNativeCompRhsConormalAliasHEq045 p hp P hP s)
      at_evaluation (phi_native_comp_evaluation_transport049%
        (actualOriginalGlobalPhiNativeKaehlerEvaluatedOwn049 p hp P hP s) using
        (actualOriginalGlobalPhiNativeRhsEvaluationPointEq049 p hp P hP s)))) :=
  phi_native_infer010% (letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    phi_native_comp_literal_assembly046%
      (actualOriginalGlobalPhiNativeCompApplyOwn043 p hp P hP s)
      with_alias (actualOriginalGlobalPhiNativeCompOwnConormalAliasHEq045 p hp P hP s)
      with_view (actualOriginalGlobalPhiNativeCompApplyViewedLeftHEq045 p hp P hP s)
      with_rhs (actualOriginalGlobalPhiNativeCompRhsConormalAliasHEq045 p hp P hP s)
      at_evaluation (phi_native_comp_evaluation_transport049%
        (actualOriginalGlobalPhiNativeKaehlerEvaluatedOwn049 p hp P hP s) using
        (actualOriginalGlobalPhiNativeRhsEvaluationPointEq049 p hp P hP s)))

meta section
open Lean Meta Elab Term

/-- Eliminate only the sixteen literal top-level let binders of passed044.
No map/carrier/instance subtree is unfolded; the resulting proposition is the
exact stored HEq body. Ordinary id carries the original opaque044 proof. -/
elab "phi_native_chart_projection_top_lets051% " supplied:term : term => do
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  let source ← phiNativeNoRecovery025 source
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeChartProjectionHEq044 &&
      source.getAppArgs.size == 8 do
    throwError "Native051 accepts only the exact passed original ChartProjection044 application."
  let mut body := (← inferType source).consumeMData
  let mut eliminated : Nat := 0
  for _ in [:16] do
    match body with
    | .letE _ _ value innerBody _ =>
      body := (innerBody.instantiate1 value).consumeMData
      eliminated := eliminated + 1
    | _ => pure ()
  unless decide (eliminated > 0) do
    throwError "Native051 expected exactly the original bounded top-let telescope followed by HEq4."
  unless body.heq?.isSome do
    throwError "Native051 expected exactly the original bounded top-let telescope followed by HEq4."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``id [Level.zero]) #[body, source])
  unless (← inferType proof).consumeMData.equal body do
    throwError "Native051 changed the exact zeta-substituted stored proposition."
  logInfo m!"Native051 ordinary id retains original044 proof after {eliminated} top-level native let substitutions; no subtree normalization."
  return proof

end

private lemma actualOriginalGlobalPhiNativeChartProjectionOwn051
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_chart_projection_top_lets051%
      (actualOriginalGlobalPhiNativeChartProjectionHEq044 p hp P hP s)) :=
  phi_native_chart_projection_top_lets051%
    (actualOriginalGlobalPhiNativeChartProjectionHEq044 p hp P hP s)

private def phiNativeKaehlerPointProp047
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) : Prop :=
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let W := schemeRelativeDifferentials (toBase I)
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let Dg := actualGlobalClosedConormalDifferentialMap (toBase I) q
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      W (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      J (closedImmersionModule j) (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let x : RingHom.ker C.residue :=
      ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    G.map (Dg ≫ Et.hom ≫ Ebase.hom) (G.map cJ z) =
      actualAffineConormalDifferentialFiberMap (k := K) C.residue C.residue_surjective
        (G.map Es.hom (G.map cJ z))

meta section
open Lean Meta Elab Term Tactic

/-- Parse the actual native Eq proposition without reconstructing its carrier. -/
private def phiNativeKaehlerNativeEq047 (proposition : Expr) : MetaM (Expr × Expr × Expr) := do
  let actual ← whnf proposition
  let some (carrier, left, right) := actual.consumeMData.eq?
    | throwError "Native047 expected the literal native coefficient Eq proposition."
  return (carrier, left, right)

elab "phi_native_kaehler_header_projection047% " supplied:term " to_prop " proposition:term : term => do
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  let proposition ← Term.elabTerm proposition none (catchExPostpone := false)
  let source ← phiNativeNoRecovery025 source
  let proposition ← phiNativeNoRecovery025 proposition
  let (_, _, sourceRightCarrier, _) ← phiNativeStoredHEq027 source
  let (targetCarrier, _, _) ← phiNativeKaehlerNativeEq047 proposition
  let (left, right) ← phiNativeChartProjectionPair044 sourceRightCarrier targetCarrier
  return ← mkHEq left right

end

private lemma actualOriginalGlobalPhiNativeKaehlerHeaderProjectionHEq047
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    phi_native_kaehler_header_projection047%
      (actualOriginalGlobalPhiNativeCompLiteralHEqOwn049 p hp P hP s) to_prop
      (phiNativeKaehlerPointProp047 p hp P hP s) := by
  basis_full_exact142 (actualOriginalGlobalPhiNativeChartProjectionOwn051 p hp P hP s)

/-- The exact installed conormal module definition, with original scheme/map vector. -/
private theorem phiNativeConormalModuleAliasHEq053.{uConormal053}
    (X Z : Scheme.{uConormal053}) (i : Z ⟶ X) :
    HEq (actualClosedImmersionConormalModule i)
      ((Scheme.Modules.pullback i).obj (closedImmersionModule i)) := by
  rfl

meta section
open Lean Meta Elab Term

/-- Walk only the actual failed Folded052 path with the frozen engine's existing
fuel8 head normalization, then retain both literal module-object endpoints. -/
private def phiNativeConormalBoundary053 (source proposition : Expr) : TermElabM (Expr × Expr) := do
  let mut left ← instantiateMVars (← inferType source)
  let (carrier, pointLeft, pointRight) ← phiNativeKaehlerNativeEq047 proposition
  let mut right := mkAppN (mkConst ``HEq [← getLevel carrier])
    #[carrier, pointLeft, carrier, pointRight]
  for index in (#[3, 5, 0, 6, 2, 5] : Array Nat) do
    left ← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.normalizeHead left 8
    right ← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.normalizeHead right 8
    let la := left.getAppArgs
    let ra := right.getAppArgs
    unless left.getAppFn.consumeMData.equal right.getAppFn.consumeMData &&
        la.size == ra.size && decide (index < la.size) do
      throwError m!"Native053 actual failed path parent differs before arg{index}: source={left.getAppFn}/{la.size}, target={right.getAppFn}/{ra.size}."
    left := la[index]!
    right := ra[index]!
  left ← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.normalizeHead left 8
  right ← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.normalizeHead right 8
  unless left.getAppFn.isConstOf ``actualClosedImmersionConormalModule &&
      left.getAppArgs.size == 3 && right.getAppFn.isConstOf ``CategoryTheory.Functor.obj &&
      right.getAppArgs.size == 6 do
    throwError m!"Native053 refuses an undiagnosed module-object boundary: source={left.getAppFn}/{left.getAppArgs.size}, target={right.getAppFn}/{right.getAppArgs.size}."
  return (left, right)

elab "phi_native_kaehler_conormal_boundary053% " mode:num supplied:term
    " to_prop " proposition:term : term => do
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  let proposition ← Term.elabTerm proposition none (catchExPostpone := false)
  let source ← phiNativeNoRecovery025 source
  let proposition ← phiNativeNoRecovery025 proposition
  let (left, right) ← phiNativeConormalBoundary053 source proposition
  if mode.getNat == 0 then return ← mkHEq left right
  unless mode.getNat == 1 do
    throwError "Native053 expected only statement mode0 or original alias law mode1."
  let .const _ levels := left.getAppFn | throwError "Native053 missing original alias constant."
  let info ← getConstInfo ``phiNativeConormalModuleAliasHEq053
  unless levels.length == info.levelParams.length do
    throwError "Native053 original module alias/law universe vector lengths differ."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``phiNativeConormalModuleAliasHEq053 levels) left.getAppArgs)
  let (_, actualLeft, _, ownExpansion) ← phiNativeStoredHEq027 proof
  let expectedExpansion ← phiNativeConormalAliasView040 left
  unless actualLeft.consumeMData.equal left.consumeMData &&
      ownExpansion.consumeMData.equal expectedExpansion.consumeMData do
    throwError "Native053 generic alias law changed original scheme/map vector or installed expansion."
  logInfo "Native053 exact original three scheme/map arguments and installed conormal module expansion retained."
  return proof

end

private lemma actualOriginalGlobalPhiNativeConormalBoundaryHEq053
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    phi_native_kaehler_conormal_boundary053% 0
      (actualOriginalGlobalPhiNativeCompLiteralHEqOwn049 p hp P hP s) to_prop
      (phiNativeKaehlerPointProp047 p hp P hP s) := by
  basis_full_exact142 (phi_native_kaehler_conormal_boundary053% 1
    (actualOriginalGlobalPhiNativeCompLiteralHEqOwn049 p hp P hP s) to_prop
    (phiNativeKaehlerPointProp047 p hp P hP s))

meta section
open Lean Meta Elab Term Tactic

/-- Compare HEq propositions at exactly the final Eq carrier, then use eq_of_heq
with that same stored carrier and endpoints. The engine and budgets are unchanged. -/
elab "phi_native_kaehler_homogeneous_exact053 " supplied:term " using " suppliedSeed:term
    " with_conormal " suppliedConormal:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← Term.elabTerm supplied none (catchExPostpone := false)
    let source ← phiNativeNoRecovery025 source
    let sourceType ← instantiateMVars (← inferType source)
    let (_, _, sourceRightCarrier, _) ← phiNativeStoredHEq027 source
    let target ← instantiateMVars (← goal.getType)
    let (carrier, left, right) ← phiNativeKaehlerNativeEq047 target
    let seed ← Term.elabTerm suppliedSeed none (catchExPostpone := false)
    let seed ← phiNativeNoRecovery025 seed
    let (_, seedLeft, _, seedRight) ← phiNativeStoredHEq027 seed
    let (actualLeft, actualRight) ← phiNativeChartProjectionPair044 sourceRightCarrier carrier
    unless seedLeft.consumeMData.equal actualLeft.consumeMData &&
        seedRight.consumeMData.equal actualRight.consumeMData do
      throwError "Native047 refuses a chart projection seed on different actual source/header vectors."
    let level ← getLevel carrier
    let homogeneousTarget := mkAppN (mkConst ``HEq [level]) #[carrier, left, carrier, right]
    let reverseSeed ← mkHEqSymm seed
    let conormal ← Term.elabTerm suppliedConormal none (catchExPostpone := false)
    let conormal ← phiNativeNoRecovery025 conormal
    let (_, conormalLeft, _, conormalRight) ← phiNativeStoredHEq027 conormal
    let (actualConormalLeft, actualConormalRight) ← phiNativeConormalBoundary053 source target
    unless conormalLeft.consumeMData.equal actualConormalLeft.consumeMData &&
        conormalRight.consumeMData.equal actualConormalRight.consumeMData do
      throwError "Native053 refuses a conormal certificate on different original module-object vectors."
    let reverseConormal ← mkHEqSymm conormal
    let (typeHEq, state) ←
      (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.structuralHEq
        sourceType homogeneousTarget 96 #[] "full142").run
          { pairs := #[(seedLeft, seedRight, seed), (seedRight, seedLeft, reverseSeed),
            (conormalLeft, conormalRight, conormal), (conormalRight, conormalLeft, reverseConormal)] }
    let typeEq ← mkEqOfHEq typeHEq
    let homogeneousProof := mkAppN (mkConst ``Eq.mp [Level.zero])
      #[sourceType, homogeneousTarget, typeEq, source]
    let proof ← phiNativeNoRecovery025
      (mkAppN (mkConst ``eq_of_heq [level]) #[carrier, left, right, homogeneousProof])
    let (actualCarrier, actualResultLeft, actualResultRight) ← phiNativeStoredEq018 proof
    unless actualCarrier.consumeMData.equal carrier.consumeMData &&
        actualResultLeft.consumeMData.equal left.consumeMData &&
        actualResultRight.consumeMData.equal right.consumeMData do
      throwError "Native047 changed the native equation carrier or endpoints."
    logInfo m!"Native053 homogeneous ordinary compatibility emitted: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruence steps={state.congrSteps}, binders={state.binderSteps}, unused traversal budget={state.remaining}."
    goal.assign proof
    replaceMainGoal []

end

private lemma actualOriginalGlobalPhiNativeKaehlerPointFolded047
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    phiNativeKaehlerPointProp047 p hp P hP s := by
  phi_native_kaehler_homogeneous_exact053
    (actualOriginalGlobalPhiNativeCompLiteralHEqOwn049 p hp P hP s) using
    (actualOriginalGlobalPhiNativeKaehlerHeaderProjectionHEq047 p hp P hP s) with_conormal
    (actualOriginalGlobalPhiNativeConormalBoundaryHEq053 p hp P hP s)

meta section
open Lean Meta Elab Term

/-- Open only the exact native proposition definition and its original nineteen
noninstance top-level lets. The original opaque folded proof is retained by id. -/
elab "phi_native_kaehler_definition_body054% " supplied:term : term => do
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  let source ← phiNativeNoRecovery025 source
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeKaehlerPointFolded047 &&
      source.getAppArgs.size == 8 do
    throwError "Native054 accepts only the actual passed native folded coefficient proof."
  let proposition := (← inferType source).consumeMData
  let .const name levels := proposition.getAppFn
    | throwError "Native054 missing exact original proposition definition."
  unless name == ``phiNativeKaehlerPointProp047 && proposition.getAppArgs.size == 8 do
    throwError "Native054 refuses a different native proposition definition or argument vector."
  let .defnInfo definition ← getConstInfo name
    | throwError "Native054 expected the installed native proposition definition value."
  unless levels.length == definition.levelParams.length do
    throwError "Native054 original proposition universe vector differs."
  let mut body := (mkAppN
    (definition.value.instantiateLevelParams definition.levelParams levels)
    proposition.getAppArgs).headBeta.consumeMData
  let mut eliminated : Nat := 0
  for _ in [:19] do
    match body with
    | .letE _ _ value innerBody _ =>
      body := (innerBody.instantiate1 value).consumeMData
      eliminated := eliminated + 1
    | _ => pure ()
  unless decide (eliminated > 0) do
    throwError "Native054 expected original native local lets."
  unless body.eq?.isSome do
    throwError "Native054 expected the exact original Eq3 body after the bounded original lets."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``id [Level.zero]) #[body, source])
  unless (← inferType proof).consumeMData.equal body do
    throwError "Native054 changed the exact stored native equation body."
  logInfo m!"Native054 ordinary id retains actual folded proof after ONLY Prop047 definition/eight arguments and {eliminated} original top-level let substitutions."
  return proof

end

private lemma actualOriginalGlobalPhiNativeKaehlerPointExpandedOwn054
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_kaehler_definition_body054%
      (actualOriginalGlobalPhiNativeKaehlerPointFolded047 p hp P hP s)) :=
  phi_native_kaehler_definition_body054%
    (actualOriginalGlobalPhiNativeKaehlerPointFolded047 p hp P hP s)

private lemma actualOriginalGlobalPhiNativeKaehlerPointCompatibility047
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let W := schemeRelativeDifferentials (toBase I)
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let Dg := actualGlobalClosedConormalDifferentialMap (toBase I) q
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      W (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      J (closedImmersionModule j) (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let x : RingHom.ker C.residue :=
      ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    G.map (Dg ≫ Et.hom ≫ Ebase.hom) (G.map cJ z) =
      actualAffineConormalDifferentialFiberMap (k := K) C.residue C.residue_surjective
        (G.map Es.hom (G.map cJ z)) := by
  intro C I R L q f j J T W G z cJ Dg Et Ebase Es x sx
  basis_full_exact142 (actualOriginalGlobalPhiNativeKaehlerPointExpandedOwn054 p hp P hP s)

meta section
open Lean Meta Elab Term

/-- Open ONLY the two exact passed original fact telescopes used by the public
coefficient proof. No definition or carrier/map/instance subtree is unfolded. -/
elab "phi_native_public_fact_top_lets055% " mode:num supplied:term : term => do
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  let source ← phiNativeNoRecovery025 source
  let expectedName := if mode.getNat == 0 then
      ``actualOriginalGlobalPhiNativeSourceSection006
    else ``actualOriginalGlobalPhiNativeKaehlerPointCompatibility047
  let bound : Nat := if mode.getNat == 0 then 15 else 19
  unless mode.getNat == 0 || mode.getNat == 1 do
    throwError "Native055 expected only source fact mode0 or native comparison fact mode1."
  unless source.getAppFn.isConstOf expectedName && source.getAppArgs.size == 8 do
    throwError "Native055 refuses a different original source/native proof or argument vector."
  let mut body := (← inferType source).consumeMData
  let mut eliminated : Nat := 0
  for _ in [:bound] do
    match body with
    | .letE _ _ value innerBody _ =>
      body := (innerBody.instantiate1 value).consumeMData
      eliminated := eliminated + 1
    | _ => pure ()
  unless decide (eliminated > 0) do
    throwError "Native055 expected the actual original fact top lets."
  unless body.eq?.isSome do
    throwError "Native055 original bounded top-let telescope did not expose Eq3."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``id [Level.zero]) #[body, source])
  unless (← inferType proof).consumeMData.equal body do
    throwError "Native055 changed the exact original fact equation body."
  logInfo m!"Native055 fact mode{mode.getNat}: ordinary id retains actual original proof after {eliminated} top lets, no subtree normalization."
  return proof

end

private lemma actualOriginalGlobalPhiNativeSourceSectionOwn055
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_public_fact_top_lets055% 0
      (actualOriginalGlobalPhiNativeSourceSection006 p hp P hP s)) :=
  phi_native_public_fact_top_lets055% 0
    (actualOriginalGlobalPhiNativeSourceSection006 p hp P hP s)

private lemma actualOriginalGlobalPhiNativeKaehlerPointOwn055
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_public_fact_top_lets055% 1
      (actualOriginalGlobalPhiNativeKaehlerPointCompatibility047 p hp P hP s)) :=
  phi_native_public_fact_top_lets055% 1
    (actualOriginalGlobalPhiNativeKaehlerPointCompatibility047 p hp P hP s)

meta section
open Lean Meta Elab Term Tactic

/-- Construct only the exact source-rewritten endpoint equation: retain the
original native Eq carrier/LHS and all five affine coercion/function arguments,
replace its final input with the actual source theorem's RHS. -/
private def phiNativePublicSourceRewrittenEq055 (source native : Expr) : TermElabM Expr := do
  let (_, sourceLeft, sourceRight) ← phiNativeStoredEq018 source
  let (carrier, nativeLeft, nativeRight) ← phiNativeStoredEq018 native
  let rhs := nativeRight.consumeMData.headBeta
  let args := rhs.getAppArgs
  unless rhs.getAppFn.isConstOf ``DFunLike.coe && args.size == 6 do
    throwError "Native055 expected the original affine fiber function/coercion6 endpoint."
  unless sourceLeft.consumeMData.headBeta.equal args[5]!.consumeMData.headBeta do
    throwError "Native055 refuses source rewrite on a different original mapped ideal point."
  let rewritten := mkAppN rhs.getAppFn (args.set! 5 sourceRight)
  let result := mkAppN (mkConst ``Eq [← getLevel carrier])
    #[carrier, nativeLeft, rewritten]
  let resultArgs := result.getAppArgs
  unless resultArgs[0]!.consumeMData.equal carrier.consumeMData &&
      resultArgs[1]!.consumeMData.equal nativeLeft.consumeMData &&
      rewritten.getAppFn.equal rhs.getAppFn &&
      rewritten.getAppArgs[5]!.consumeMData.equal sourceRight.consumeMData do
    throwError "Native055 changed original equation carrier/LHS/scalars/function or source RHS."
  for index in [:5] do
    unless rewritten.getAppArgs[index]!.consumeMData.equal args[index]!.consumeMData do
      throwError "Native055 changed an original affine coercion/function argument."
  logInfo "Native055 strict original source-LHS/affine-input join verified; native Eq carrier/LHS and allfive original affine function/coercion arguments retained."
  return result

elab "phi_native_public_source_rewritten_prop055% " suppliedSource:term
    " using " suppliedNative:term : term => do
  let source ← Term.elabTerm suppliedSource none (catchExPostpone := false)
  let native ← Term.elabTerm suppliedNative none (catchExPostpone := false)
  let source ← phiNativeNoRecovery025 source
  let native ← phiNativeNoRecovery025 native
  return ← phiNativePublicSourceRewrittenEq055 source native

elab "phi_native_public_source_endpoint_guard055 " suppliedSource:term
    " using " suppliedNative:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← Term.elabTerm suppliedSource none (catchExPostpone := false)
    let native ← Term.elabTerm suppliedNative none (catchExPostpone := false)
    let source ← phiNativeNoRecovery025 source
    let native ← phiNativeNoRecovery025 native
    let _ ← phiNativePublicSourceRewrittenEq055 source native
    pure ()

end

private lemma actualOriginalGlobalPhiNativeSourceRewrittenOwn055
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    phi_native_public_source_rewritten_prop055%
      (actualOriginalGlobalPhiNativeSourceSectionOwn055 p hp P hP s) using
      (actualOriginalGlobalPhiNativeKaehlerPointOwn055 p hp P hP s) := by
  have hSource := actualOriginalGlobalPhiNativeSourceSectionOwn055 p hp P hP s
  have hAt := actualOriginalGlobalPhiNativeKaehlerPointOwn055 p hp P hP s
  phi_native_public_source_endpoint_guard055 hSource using hAt
  rw [hSource] at hAt
  exact hAt

meta section
open Lean Meta Elab Term Tactic

/-- Select ONLY the exact carrier join which failed056: native contraction Eq
carrier and the domain argument of the original inner mapped-chart coe6.
The two original native points and both enclosing maps are retained literally. -/
private def phiNativeContractionCarrierPair057
    (pointEquation evaluation : Expr) : TermElabM (Expr × Expr) := do
  let some (contractCarrier, contractLeft, _) := pointEquation.consumeMData.eq?
    | throwError "Native057 expected the exact original native contraction Eq3 proposition."
  unless (← inferType pointEquation).consumeMData.equal (mkSort Level.zero) do
    throwError "Native057 accepts only the actual native point equality proposition, not a proof premise."
  let outer := evaluation.consumeMData.headBeta
  let outerArgs := outer.getAppArgs
  unless outer.getAppFn.isConstOf ``DFunLike.coe && outerArgs.size == 6 do
    throwError "Native057 expected the original outer affine-fiber equivalence coe6."
  let inner := outerArgs[5]!.consumeMData.headBeta
  let innerArgs := inner.getAppArgs
  unless inner.getAppFn.isConstOf ``DFunLike.coe && innerArgs.size == 6 do
    throwError "Native057 expected the original inner mapped-chart coe6."
  unless innerArgs[5]!.consumeMData.headBeta.equal contractLeft.consumeMData.headBeta do
    throwError "Native057 refuses different original native contraction/evaluation points."
  let mappedDomain := innerArgs[1]!
  unless (← getLevel contractCarrier) == (← getLevel mappedDomain) do
    throwError "Native057 refuses genuinely different carrier universes."
  logInfo m!"Native057 exact input-carrier join raw={contractCarrier.consumeMData.headBeta.equal mappedDomain.consumeMData.headBeta}; original contraction-LHS/evaluation-input point raw=true."
  return (contractCarrier, mappedDomain)

elab "phi_native_contraction_input_carrier_prop057% " pointEquation:term
    " using " evaluation:term : term => do
  let pointEquation ← Term.elabTerm pointEquation none (catchExPostpone := false)
  let evaluation ← Term.elabTerm evaluation none (catchExPostpone := false)
  let pointEquation ← phiNativeNoRecovery025 pointEquation
  let evaluation ← phiNativeNoRecovery025 evaluation
  let (contractCarrier, mappedDomain) ←
    phiNativeContractionCarrierPair057 pointEquation evaluation
  return ← mkHEq contractCarrier mappedDomain

/-- Prove ONLY the selected carrier HEq with the unchanged passed structural
engine96/1024/8. No assumption or permissive conversion replaces the raw guard. -/
elab "phi_native_contraction_input_carrier_exact057" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let some (leftType, contractCarrier, rightType, mappedDomain) := target.consumeMData.heq?
      | throwError "Native057 expected its actual selected input-carrier HEq4 goal."
    unless leftType.consumeMData.equal rightType.consumeMData do
      throwError "Native057 refuses different carrier Sort vectors."
    let .sort _ := leftType.consumeMData
      | throwError "Native057 accepts only a carrier type HEq, not an arbitrary point/map equality."
    let (proof, state) ←
      (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.structuralHEq
        contractCarrier mappedDomain 96 #[] "native057.inputCarrier").run {}
    let proof ← phiNativeNoRecovery025 proof
    let (_, actualLeft, _, actualRight) ← phiNativeStoredHEq027 proof
    unless actualLeft.consumeMData.equal contractCarrier.consumeMData &&
        actualRight.consumeMData.equal mappedDomain.consumeMData do
      throwError "Native057 ordinary carrier certificate changed its exact original endpoints."
    logInfo m!"Native057 ordinary input-carrier HEq emitted: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruence steps={state.congrSteps}, binders={state.binderSteps}, unused traversal budget={state.remaining}."
    goal.assign proof
    replaceMainGoal []

end

private lemma actualOriginalGlobalPhiNativeContractionInputCarrierHEq057
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let W := schemeRelativeDifferentials (toBase I)
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let cW := (actualPositiveTwistPullbackTensorIso I q W 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let Dg := actualGlobalClosedConormalDifferentialMap (toBase I) q
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      W (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      J (closedImmersionModule j) (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    let Etw := actualOriginalQuadraticConormalPointChartIso p hp P hP
    let x : RingHom.ker C.residue :=
      ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let E := actualAffineSchemeDifferentialPointFiberEquiv (k := K) C.residue
    phi_native_contraction_input_carrier_prop057%
      (G.map cW (actualOriginalGlobalCanonicalQuadraticPhi p hp P s) =
        G.map Dg (G.map cJ z)) using
      (E (G.map (Et.hom ≫ Ebase.hom)
        (G.map cW (actualOriginalGlobalCanonicalQuadraticPhi p hp P s)))) := by
  intro C I R L q f j J T W G z cJ cW Dg Et Ebase Es Ej Etw x sx E
  phi_native_contraction_input_carrier_exact057

meta section
open Lean Meta Elab Term

/-- Open ONLY the exact twenty-three top native lets of the specified actual
ordinary declaration, carrying that SAME proof through ordinary id. -/
private def phiNativeOpenContractionLocalLets058
    (source : Expr) (expectedName : Name) : TermElabM Expr := do
  let source ← phiNativeNoRecovery025 source
  unless source.getAppFn.isConstOf expectedName && source.getAppArgs.size == 8 do
    throwError "Native058 refuses a different native contraction declaration/application vector."
  let mut body := (← inferType source).consumeMData
  let mut eliminated : Nat := 0
  for _ in [:23] do
    match body with
    | .letE _ _ value innerBody _ =>
      body := (innerBody.instantiate1 value).consumeMData
      eliminated := eliminated + 1
    | _ => pure ()
  unless eliminated == 23 && (body.eq?.isSome || body.heq?.isSome) do
    throwError "Native058 expected exactly the original twenty-three top native lets and Eq3/HEq4."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``id [Level.zero]) #[body, source])
  unless (← inferType proof).consumeMData.equal body do
    throwError "Native058 changed the exact native contraction declaration body."
  logInfo "Native058 ordinary id carries original native declaration through only its23 top lets; exact proof head/vector/body guarded."
  return proof

elab "phi_native_contraction_carrier_body058% " supplied:term : term => do
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  phiNativeOpenContractionLocalLets058 source
    ``actualOriginalGlobalPhiNativeContractionInputCarrierHEq057

end

private lemma actualOriginalGlobalPhiNativeContractionCarrierOwn058
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_contraction_carrier_body058%
      (actualOriginalGlobalPhiNativeContractionInputCarrierHEq057 p hp P hP s)) :=
  phi_native_contraction_carrier_body058%
    (actualOriginalGlobalPhiNativeContractionInputCarrierHEq057 p hp P hP s)

meta section
open Lean Meta Elab Term Tactic

/-- Retain BOTH exact native contraction points; change only its Eq carrier
argument to the original mapped-chart coe6 domain selected by passed057. -/
elab "phi_native_contraction_mapped_domain_prop058% " pointEquation:term
    " using " evaluation:term : term => do
  let pointEquation ← Term.elabTerm pointEquation none (catchExPostpone := false)
  let evaluation ← Term.elabTerm evaluation none (catchExPostpone := false)
  let pointEquation ← phiNativeNoRecovery025 pointEquation
  let evaluation ← phiNativeNoRecovery025 evaluation
  let some (carrier, left, right) := pointEquation.consumeMData.eq?
    | throwError "Native058 expected the original native contraction Eq3 proposition."
  let (originalCarrier, mappedDomain) ←
    phiNativeContractionCarrierPair057 pointEquation evaluation
  unless carrier.consumeMData.equal originalCarrier.consumeMData do
    throwError "Native058 carrier selector changed the actual original Eq carrier."
  let proposition := mkAppN (mkConst ``Eq [← getLevel mappedDomain])
    #[mappedDomain, left, right]
  let some (actualCarrier, actualLeft, actualRight) := proposition.eq?
    | throwError "Native058 mapped-domain proposition is not Eq3."
  unless actualCarrier.consumeMData.equal mappedDomain.consumeMData &&
      actualLeft.consumeMData.equal left.consumeMData &&
      actualRight.consumeMData.equal right.consumeMData do
    throwError "Native058 mapped-domain proposition changed either actual native point."
  return proposition

/-- Transport the actual original contraction PROOF through proposition
compatibility seeded ONLY by the exact passed carrier HEq and its reverse.
No casts or replacement point/map expressions enter the result. -/
elab "phi_native_contraction_mapped_domain_exact058 " supplied:term
    " using " suppliedCarrier:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← Term.elabTerm supplied none (catchExPostpone := false)
    let carrierProof ← Term.elabTerm suppliedCarrier none (catchExPostpone := false)
    let source ← phiNativeNoRecovery025 source
    let carrierProof ← phiNativeNoRecovery025 carrierProof
    let sourceProposition ← instantiateMVars (← inferType source)
    let target ← instantiateMVars (← goal.getType)
    let (sourceCarrier, sourceLeft, sourceRight) ← phiNativeStoredEq018 source
    let some (mappedDomain, targetLeft, targetRight) := target.consumeMData.eq?
      | throwError "Native058 expected only the exact mapped-domain contraction Eq3 goal."
    unless sourceLeft.consumeMData.headBeta.equal targetLeft.consumeMData.headBeta &&
        sourceRight.consumeMData.headBeta.equal targetRight.consumeMData.headBeta do
      throwError "Native058 refuses changing either original contraction point."
    let (_, carrierLeft, _, carrierRight) ← phiNativeStoredHEq027 carrierProof
    unless carrierLeft.consumeMData.equal sourceCarrier.consumeMData &&
        carrierRight.consumeMData.equal mappedDomain.consumeMData do
      throwError "Native058 refuses a carrier certificate on different original source/map-domain endpoints."
    let reverseCarrier ← mkHEqSymm carrierProof
    let (compatibility, state) ←
      (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.structuralHEq
        sourceProposition target 96 #[] "native058.mappedDomainEq").run
          { pairs := #[(carrierLeft, carrierRight, carrierProof),
              (carrierRight, carrierLeft, reverseCarrier)] }
    let typeEquality ← mkEqOfHEq compatibility
    let proof ← phiNativeNoRecovery025
      (mkAppN (mkConst ``Eq.mp [Level.zero])
        #[sourceProposition, target, typeEquality, source])
    let (actualCarrier, actualLeft, actualRight) ← phiNativeStoredEq018 proof
    unless actualCarrier.consumeMData.equal mappedDomain.consumeMData &&
        actualLeft.consumeMData.equal targetLeft.consumeMData &&
        actualRight.consumeMData.equal targetRight.consumeMData do
      throwError "Native058 ordinary carrier transport changed exact native Eq carrier/points."
    logInfo m!"Native058 exact passed-carrier-seeded Eq.mp emitted: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruence steps={state.congrSteps}, binders={state.binderSteps}, unused traversal budget={state.remaining}; original point endpoints unchanged."
    goal.assign proof
    replaceMainGoal []

end

private lemma actualOriginalGlobalPhiNativeContractionMappedDomainLocal058
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let W := schemeRelativeDifferentials (toBase I)
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let cW := (actualPositiveTwistPullbackTensorIso I q W 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let Dg := actualGlobalClosedConormalDifferentialMap (toBase I) q
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      W (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      J (closedImmersionModule j) (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    let Etw := actualOriginalQuadraticConormalPointChartIso p hp P hP
    let x : RingHom.ker C.residue :=
      ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let E := actualAffineSchemeDifferentialPointFiberEquiv (k := K) C.residue
    phi_native_contraction_mapped_domain_prop058%
      (G.map cW (actualOriginalGlobalCanonicalQuadraticPhi p hp P s) =
        G.map Dg (G.map cJ z)) using
      (E (G.map (Et.hom ≫ Ebase.hom)
        (G.map cW (actualOriginalGlobalCanonicalQuadraticPhi p hp P s)))) := by
  intro C I R L q f j J T W G z cJ cW Dg Et Ebase Es Ej Etw x sx E
  have hContract := actualOriginalGlobalCanonicalQuadraticPhi_contract p hp P hP s
  change G.map cW (actualOriginalGlobalCanonicalQuadraticPhi p hp P s) =
    G.map Dg (G.map cJ z) at hContract
  have hCarrier : phi_native_contraction_input_carrier_prop057%
      (G.map cW (actualOriginalGlobalCanonicalQuadraticPhi p hp P s) =
        G.map Dg (G.map cJ z)) using
      (E (G.map (Et.hom ≫ Ebase.hom)
        (G.map cW (actualOriginalGlobalCanonicalQuadraticPhi p hp P s)))) := by
    basis_full_exact142
      (actualOriginalGlobalPhiNativeContractionCarrierOwn058 p hp P hP s)
  phi_native_contraction_mapped_domain_exact058 hContract using hCarrier

meta section
open Lean Meta Elab Term

elab "phi_native_contraction_mapped_domain_body058% " supplied:term : term => do
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  phiNativeOpenContractionLocalLets058 source
    ``actualOriginalGlobalPhiNativeContractionMappedDomainLocal058

end

private lemma actualOriginalGlobalPhiNativeContractionMappedDomainOwn058
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_contraction_mapped_domain_body058%
      (actualOriginalGlobalPhiNativeContractionMappedDomainLocal058 p hp P hP s)) :=
  phi_native_contraction_mapped_domain_body058%
    (actualOriginalGlobalPhiNativeContractionMappedDomainLocal058 p hp P hP s)
meta section
open Lean Meta Elab Term Tactic

/-- Lift the actual native contraction equality only through the TWO exact
outer coercion/function vectors already present in this local native Eq goal.
No rewriting, map reassociation or carrier/map/instance unfolding is performed. -/
elab "phi_native_contraction_lift_exact056 " supplied:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let contract ← Term.elabTerm supplied none (catchExPostpone := false)
    let contract ← phiNativeNoRecovery025 contract
    let (inputCarrier, inputLeft, inputRight) ← phiNativeStoredEq018 contract
    let target ← instantiateMVars (← goal.getType)
    let some (outputCarrier, targetLeft, targetRight) := target.consumeMData.eq?
      | throwError "Native056 expected only the actual local contraction-lift Eq3 goal."
    let left := targetLeft.consumeMData.headBeta
    let right := targetRight.consumeMData.headBeta
    let outerLeft := left.getAppArgs
    let outerRight := right.getAppArgs
    unless left.getAppFn.isConstOf ``DFunLike.coe &&
        right.getAppFn.equal left.getAppFn &&
        outerLeft.size == 6 && outerRight.size == 6 do
      throwError "Native056 expected the exact original affine-fiber-equivalence coe6 endpoints."
    let innerLeft := outerLeft[5]!.consumeMData.headBeta
    let innerRight := outerRight[5]!.consumeMData.headBeta
    let innerLeftArgs := innerLeft.getAppArgs
    let innerRightArgs := innerRight.getAppArgs
    unless innerLeft.getAppFn.isConstOf ``DFunLike.coe &&
        innerRight.getAppFn.equal innerLeft.getAppFn &&
        innerLeftArgs.size == 6 && innerRightArgs.size == 6 do
      throwError "Native056 expected the exact original mapped chart-differential coe6 endpoints."
    for i in [:5] do
      unless outerLeft[i]!.consumeMData.equal outerRight[i]!.consumeMData do
        throwError "Native056 refuses changed original outer equivalence/scalar/coercion argument {i}."
      unless innerLeftArgs[i]!.consumeMData.equal innerRightArgs[i]!.consumeMData do
        throwError "Native056 refuses changed original inner chart-map/scalar/coercion argument {i}."
    unless innerLeftArgs[5]!.consumeMData.headBeta.equal inputLeft.consumeMData.headBeta &&
        innerRightArgs[5]!.consumeMData.headBeta.equal inputRight.consumeMData.headBeta do
      throwError "Native056 refuses a contraction equality on different actual native points."
    unless innerLeftArgs[1]!.consumeMData.headBeta.equal inputCarrier.consumeMData.headBeta do
      throwError "Native056 refuses a different original mapped-chart input carrier."
    let evaluator ← withLocalDeclD `contractedPoint inputCarrier fun contractedPoint => do
      let inner := mkAppN innerLeft.getAppFn (innerLeftArgs.set! 5 contractedPoint)
      let outer := mkAppN left.getAppFn (outerLeft.set! 5 inner)
      mkLambdaFVars #[contractedPoint] outer
    let evaluatorType ← inferType evaluator
    let .forallE _ domain codomain _ := evaluatorType.consumeMData
      | throwError "Native056 original evaluator did not retain a function type."
    unless domain.consumeMData.equal inputCarrier.consumeMData &&
        (codomain.instantiate1 inputLeft).consumeMData.headBeta.equal
          outputCarrier.consumeMData.headBeta do
      throwError "Native056 evaluator changed the exact original input/output carriers."
    let proof ← phiNativeNoRecovery025
      (mkAppN (mkConst ``congrArg [← getLevel inputCarrier, ← getLevel outputCarrier])
        #[inputCarrier, outputCarrier, inputLeft, inputRight, evaluator, contract])
    let (actualCarrier, actualLeft, actualRight) ← phiNativeStoredEq018 proof
    unless actualCarrier.consumeMData.equal outputCarrier.consumeMData &&
        actualLeft.consumeMData.headBeta.equal left &&
        actualRight.consumeMData.headBeta.equal right do
      throwError "Native056 ordinary congrArg result changed original literal Eq carrier/endpoints."
    logInfo "Native056 ordinary congrArg consumes exact stored contract Eq vector; both original outer coe6 prefixes and native point/carrier joins raw verified."
    goal.assign proof
    replaceMainGoal []

end


private lemma actualOriginalGlobalPhiNativeContractionLiftLocal058
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let W := schemeRelativeDifferentials (toBase I)
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let cW := (actualPositiveTwistPullbackTensorIso I q W 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let Dg := actualGlobalClosedConormalDifferentialMap (toBase I) q
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      W (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      J (closedImmersionModule j) (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    let Etw := actualOriginalQuadraticConormalPointChartIso p hp P hP
    let x : RingHom.ker C.residue :=
      ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let E := actualAffineSchemeDifferentialPointFiberEquiv (k := K) C.residue
    E (G.map (Et.hom ≫ Ebase.hom)
      (G.map cW (actualOriginalGlobalCanonicalQuadraticPhi p hp P s))) =
    E (G.map (Et.hom ≫ Ebase.hom) (G.map Dg (G.map cJ z))) := by
  intro C I R L q f j J T W G z cJ cW Dg Et Ebase Es Ej Etw x sx E
  have hContract : phi_native_contraction_mapped_domain_prop058%
      (G.map cW (actualOriginalGlobalCanonicalQuadraticPhi p hp P s) =
        G.map Dg (G.map cJ z)) using
      (E (G.map (Et.hom ≫ Ebase.hom)
        (G.map cW (actualOriginalGlobalCanonicalQuadraticPhi p hp P s)))) := by
    basis_full_exact142
      (actualOriginalGlobalPhiNativeContractionMappedDomainOwn058 p hp P hP s)
  phi_native_contraction_lift_exact056 hContract

meta section
open Lean Meta Elab Term

elab "phi_native_contraction_lift_body058% " supplied:term : term => do
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  phiNativeOpenContractionLocalLets058 source
    ``actualOriginalGlobalPhiNativeContractionLiftLocal058

end

private lemma actualOriginalGlobalPhiNativeContractionLiftOwn058
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_contraction_lift_body058%
      (actualOriginalGlobalPhiNativeContractionLiftLocal058 p hp P hP s)) :=
  phi_native_contraction_lift_body058%
    (actualOriginalGlobalPhiNativeContractionLiftLocal058 p hp P hP s)

/-- Evaluate the SAME functorial composite under an arbitrary outer function,
before any native chart/module/dictionary is instantiated. -/
private theorem phiNativeMappedCompositionUnder059.{uMapped059, vMapped059, wMapped059, bMapped059}
    {R : Type uMapped059} [Ring R]
    {A : Type vMapped059} [Category.{wMapped059} A]
    (G : A ⥤ ModuleCat.{uMapped059} R) {X Y Z : A}
    (f : X ⟶ Y) (g : Y ⟶ Z) (z : G.obj X)
    {B : Sort bMapped059} (E : G.obj Z → B) :
    E (G.map g (G.map f z)) = E (G.map (f ≫ g) z) := by
  rw [Functor.map_comp]
  rfl

meta section
open Lean Meta Elab Term

/-- Instantiate ordinary mapped composition from the literal native RHS's
OWN scalar/ring/category/functor/composite-object/f/g/section vector. The
outer evaluator retains ALLfive actual E.coercion arguments. Native category
structure/accessor compatibility is a separate ordinary local declaration. -/
elab "phi_native_mapped_reassociation_own059% " suppliedEndpoint:term : term => do
  let endpoint ← Term.elabTerm suppliedEndpoint none (catchExPostpone := false)
  let endpoint ← phiNativeNoRecovery025 endpoint
  let endpoint := endpoint.consumeMData.headBeta
  let ea := endpoint.getAppArgs
  unless endpoint.getAppFn.isConstOf ``DFunLike.coe && ea.size == 6 do
    throwError "Native059 expected only the exact original outer E.coercion6 endpoint."
  let v ← phiNativePointVectors033 ea[5]!
  let composite := v.mapArgs[7]!.consumeMData.headBeta
  let ca := composite.getAppArgs
  unless composite.getAppFn.isConstOf ``CategoryTheory.CategoryStruct.comp && ca.size == 7 do
    throwError "Native059 expected the exact original Dg/(Et.hom≫Ebase.hom) composite7."
  let destination := v.mapArgs[2]!.consumeMData.headBeta
  let da := destination.getAppArgs
  unless destination.getAppFn.isConstOf ``ModuleCat && da.size == 2 do
    throwError "Native059 expected the actual original module scalar/ring vector."
  unless ca[0]!.consumeMData.equal v.mapArgs[0]!.consumeMData &&
      ca[2]!.consumeMData.equal v.mapArgs[5]!.consumeMData &&
      ca[4]!.consumeMData.equal v.mapArgs[6]!.consumeMData do
    throwError "Native059 refuses changed original composite/functor category or source/target objects."
  let inputCarrier := (← inferType v.endpoint).consumeMData.headBeta
  let outputCarrier := (← inferType endpoint).consumeMData.headBeta
  let evaluator ← withLocalDeclD `mappedPoint inputCarrier fun mappedPoint =>
    mkLambdaFVars #[mappedPoint] (mkAppN endpoint.getAppFn (ea.set! 5 mappedPoint))
  let .forallE _ domain codomain _ := (← inferType evaluator).consumeMData
    | throwError "Native059 original outer evaluator did not retain a function type."
  unless domain.consumeMData.equal inputCarrier.consumeMData &&
      (codomain.instantiate1 v.endpoint).consumeMData.headBeta.equal outputCarrier do
    throwError "Native059 evaluator changed actual native input/output carriers."
  let arguments := #[da[0]!, da[1]!, v.mapArgs[0]!, v.mapArgs[1]!, v.mapArgs[4]!,
    ca[2]!, ca[3]!, ca[4]!, ca[5]!, ca[6]!, v.coeArgs[5]!, outputCarrier, evaluator]
  let resolved ← mkAppOptM ``phiNativeMappedCompositionUnder059 (arguments.map some)
  let resolved ← phiNativeNoRecovery025 resolved
  let proof ← phiNativeNoRecovery025 (mkAppN resolved.getAppFn arguments)
  let (actualCarrier, resultLeft, resultRight) ← phiNativeStoredEq018 proof
  unless actualCarrier.consumeMData.equal outputCarrier do
    throwError "Native059 mapped composition changed the exact native outer output carrier."
  let left := resultLeft.consumeMData.headBeta
  let right := resultRight.consumeMData.headBeta
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless left.getAppFn.equal endpoint.getAppFn && right.getAppFn.equal endpoint.getAppFn &&
      la.size == 6 && ra.size == 6 do
    throwError "Native059 mapped composition changed the original outer E.coercion head."
  for i in [:5] do
    unless la[i]!.consumeMData.equal ea[i]!.consumeMData &&
        ra[i]!.consumeMData.equal ea[i]!.consumeMData do
      throwError "Native059 mapped composition changed original E.coercion argument {i}."
  let resultComposite ← phiNativePointVectors033 ra[5]!
  let resultHom := resultComposite.mapArgs[7]!.consumeMData.headBeta
  let resultHomArgs := resultHom.getAppArgs
  unless resultHom.getAppFn.isConstOf ``CategoryTheory.CategoryStruct.comp &&
      resultHomArgs.size == 7 do
    throwError "Native059 own right endpoint lost its original composite shape."
  for i in #[0, 2, 3, 4, 5, 6] do
    unless resultHomArgs[i]!.consumeMData.equal ca[i]!.consumeMData do
      throwError "Native059 mapped composition changed original composite category/object/f/g argument {i}."
  let nestedOuter ← phiNativePointVectors033 la[5]!
  let nestedInner ← phiNativePointVectors033 nestedOuter.coeArgs[5]!
  unless resultComposite.mapArgs[4]!.consumeMData.equal v.mapArgs[4]!.consumeMData &&
      resultComposite.coeArgs[5]!.consumeMData.equal v.coeArgs[5]!.consumeMData &&
      nestedOuter.mapArgs[4]!.consumeMData.equal v.mapArgs[4]!.consumeMData &&
      nestedInner.mapArgs[4]!.consumeMData.equal v.mapArgs[4]!.consumeMData &&
      nestedOuter.mapArgs[7]!.consumeMData.equal ca[6]!.consumeMData &&
      nestedInner.mapArgs[7]!.consumeMData.equal ca[5]!.consumeMData &&
      nestedInner.coeArgs[5]!.consumeMData.equal v.coeArgs[5]!.consumeMData do
    throwError "Native059 mapped composition changed original functor/maps/section."
  logInfo "Native059 ordinary mapped composition uses all13 stored native scalar/category/functor/object/f/g/section/output/evaluator arguments; both exact original E prefixes and point vectors guarded. Native dictionary/accessor compatibility remains the separate local certificate."
  return proof

end

private lemma actualOriginalGlobalPhiNativeMappedReassociationOwn059
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_infer010% (
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let W := schemeRelativeDifferentials (toBase I)
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let cW := (actualPositiveTwistPullbackTensorIso I q W 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let Dg := actualGlobalClosedConormalDifferentialMap (toBase I) q
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      W (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      J (closedImmersionModule j) (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    let Etw := actualOriginalQuadraticConormalPointChartIso p hp P hP
    let x : RingHom.ker C.residue :=
      ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let E := actualAffineSchemeDifferentialPointFiberEquiv (k := K) C.residue
    phi_native_mapped_reassociation_own059%
      (E (G.map (Dg ≫ Et.hom ≫ Ebase.hom) (G.map cJ z))))) :=
  phi_native_infer010% (
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let W := schemeRelativeDifferentials (toBase I)
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let cW := (actualPositiveTwistPullbackTensorIso I q W 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let Dg := actualGlobalClosedConormalDifferentialMap (toBase I) q
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      W (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      J (closedImmersionModule j) (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    let Etw := actualOriginalQuadraticConormalPointChartIso p hp P hP
    let x : RingHom.ker C.residue :=
      ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let E := actualAffineSchemeDifferentialPointFiberEquiv (k := K) C.residue
    phi_native_mapped_reassociation_own059%
      (E (G.map (Dg ≫ Et.hom ≫ Ebase.hom) (G.map cJ z))))

meta section
open Lean Meta Elab Term

/-- Expose ONLY passed Own059's ACTUAL sixteen retained top-level native lets:
C/I/L/q/f/j/J/T/W/G/z/cJ/Dg/Et/Ebase/E (actual full type/root log read).
No map/coercion/instance/carrier subtree is unfolded or changed. -/
elab "phi_native_mapped_reassociation_own_body060% " supplied:term : term => do
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  let source ← phiNativeNoRecovery025 source
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeMappedReassociationOwn059 &&
      source.getAppArgs.size == 8 do
    throwError "Native060 accepts only the exact passed mapped-reassociation Own059 application/vector."
  let mut body := (← inferType source).consumeMData
  let mut eliminated : Nat := 0
  for _ in [:16] do
    match body with
    | .letE _ _ value innerBody _ =>
      body := (innerBody.instantiate1 value).consumeMData
      eliminated := eliminated + 1
    | _ =>
      throwError "Native060 actual Own059 native top-let telescope ended before its exact sixteen retained lets."
  unless eliminated == 16 && body.eq?.isSome do
    throwError "Native060 expected ONLY actual Own059 sixteen top lets followed immediately by Eq3."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``id [Level.zero]) #[body, source])
  unless (← inferType proof).consumeMData.equal body do
    throwError "Native060 changed the exact actual Own059 native equation body."
  logInfo "Native060 ordinary id retains exact passed Own059 proof after ONLY its actual16 top native lets; exact source head/8-vector/letcount/body guarded, no subtree normalization."
  return proof

end

private lemma actualOriginalGlobalPhiNativeMappedReassociationOwnBody060
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_mapped_reassociation_own_body060%
      (actualOriginalGlobalPhiNativeMappedReassociationOwn059 p hp P hP s)) :=
  phi_native_mapped_reassociation_own_body060%
    (actualOriginalGlobalPhiNativeMappedReassociationOwn059 p hp P hP s)

private lemma actualOriginalGlobalPhiNativeMappedReassociationLocal059
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let W := schemeRelativeDifferentials (toBase I)
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let cW := (actualPositiveTwistPullbackTensorIso I q W 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let Dg := actualGlobalClosedConormalDifferentialMap (toBase I) q
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      W (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      J (closedImmersionModule j) (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    let Etw := actualOriginalQuadraticConormalPointChartIso p hp P hP
    let x : RingHom.ker C.residue :=
      ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let E := actualAffineSchemeDifferentialPointFiberEquiv (k := K) C.residue
    E (G.map (Et.hom ≫ Ebase.hom) (G.map Dg (G.map cJ z))) =
    E (G.map (Dg ≫ Et.hom ≫ Ebase.hom) (G.map cJ z)) := by
  intro C I R L q f j J T W G z cJ cW Dg Et Ebase Es Ej Etw x sx E
  basis_full_exact142
    (actualOriginalGlobalPhiNativeMappedReassociationOwnBody060 p hp P hP s)

meta section
open Lean Meta Elab Term

elab "phi_native_mapped_reassociation_body059% " supplied:term : term => do
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  phiNativeOpenContractionLocalLets058 source
    ``actualOriginalGlobalPhiNativeMappedReassociationLocal059

end

private lemma actualOriginalGlobalPhiNativeMappedReassociationLocalOwn059
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_mapped_reassociation_body059%
      (actualOriginalGlobalPhiNativeMappedReassociationLocal059 p hp P hP s)) :=
  phi_native_mapped_reassociation_body059%
    (actualOriginalGlobalPhiNativeMappedReassociationLocal059 p hp P hP s)

private lemma actualOriginalGlobalPhiNativeDifferentialPointLocal061
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let W := schemeRelativeDifferentials (toBase I)
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let cW := (actualPositiveTwistPullbackTensorIso I q W 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let Dg := actualGlobalClosedConormalDifferentialMap (toBase I) q
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      W (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      J (closedImmersionModule j) (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    let Etw := actualOriginalQuadraticConormalPointChartIso p hp P hP
    let x : RingHom.ker C.residue :=
      ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let E := actualAffineSchemeDifferentialPointFiberEquiv (k := K) C.residue
    G.map (Dg ≫ Et.hom ≫ Ebase.hom) (G.map cJ z) =
    actualAffineDifferentialPointClass (k := K) C.residue x.1 := by
  intro C I R L q f j J T W G z cJ cW Dg Et Ebase Es Ej Etw x sx E
  letI aKRewrite062 : Algebra K
      (ChartRing (equationIdeal p hp)
        (actualOriginalQuarticCotangentChartChoice p hp P hP).index) :=
    (chartBaseMap (equationIdeal p hp)
      (actualOriginalQuarticCotangentChartChoice p hp P hP).index).toAlgebra
  have hAt := actualOriginalGlobalPhiNativeSourceRewrittenOwn055 p hp P hP s
  rw [actualAffineConormalDifferentialFiberMap_nativeSection] at hAt
  basis_full_exact142 hAt

meta section
open Lean Meta Elab Term

elab "phi_native_differential_point_body061% " supplied:term : term => do
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  phiNativeOpenContractionLocalLets058 source
    ``actualOriginalGlobalPhiNativeDifferentialPointLocal061

end

private lemma actualOriginalGlobalPhiNativeDifferentialPointOwn061
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_differential_point_body061%
      (actualOriginalGlobalPhiNativeDifferentialPointLocal061 p hp P hP s)) :=
  phi_native_differential_point_body061%
    (actualOriginalGlobalPhiNativeDifferentialPointLocal061 p hp P hP s)

meta section
open Lean Meta Elab Term

/-- Existing ordinary field diamond at the passed point proof's exact ring
parent vector. No unfolding, instance replacement, or inferred arguments. -/
elab "phi_native_own_field_ring_diamond074% " supplied:term : term => do
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  let source ← phiNativeNoRecovery025 source
  unless source.getAppFn.isConstOf
      ``actualOriginalGlobalPhiNativeDifferentialPointOwn061 && source.getAppArgs.size == 8 do
    throwError "Native074 requires only the passed original native point-own8 application."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (sourceCarrier, _, _) := sourceType.consumeMData.headBeta.eq?
    | throwError "Native074 requires the exact closed original point Eq3 type."
  let carrier := sourceCarrier.consumeMData
  unless carrier.getAppFn.isConstOf ``ModuleCat.carrier && carrier.getAppArgs.size == 3 do
    throwError "Native074 expected actual original ModuleCat.carrier3."
  let object := carrier.getAppArgs[2]!.consumeMData
  unless object.getAppFn.isConstOf ``CategoryTheory.Functor.obj && object.getAppArgs.size == 6 do
    throwError "Native074 expected actual original section-functor obj6."
  let pulledObject := object.getAppArgs[5]!.consumeMData
  unless pulledObject.getAppFn.isConstOf ``CategoryTheory.Functor.obj &&
      pulledObject.getAppArgs.size == 6 do
    throwError "Native074 expected actual original pullback obj6."
  let relative := pulledObject.getAppArgs[5]!.consumeMData
  unless relative.getAppFn.isConstOf ``schemeRelativeDifferentials && relative.getAppArgs.size == 4 do
    throwError "Native074 expected actual original relative-differentials4."
  let chartMap := relative.getAppArgs[3]!.consumeMData
  unless chartMap.getAppFn.isConstOf ``AlgebraicGeometry.Spec.map && chartMap.getAppArgs.size == 3 do
    throwError "Native074 expected actual original chart Spec.map3."
  let ringOf := chartMap.getAppArgs[1]!.consumeMData
  unless ringOf.getAppFn.isConstOf ``CommRingCat.of && ringOf.getAppArgs.size == 2 do
    throwError "Native074 expected actual original chart ring of2."
  let localizationRing := ringOf.getAppArgs[1]!.consumeMData
  unless localizationRing.getAppFn.isConstOf
      ``HomogeneousLocalization.homogeneousLocalizationCommRing &&
      localizationRing.getAppArgs.size == 11 do
    throwError "Native074 expected actual original localization ring11."
  let subgroupClass := localizationRing.getAppArgs[5]!.consumeMData
  unless subgroupClass.getAppFn.isConstOf ``Submodule.addSubgroupClass &&
      subgroupClass.getAppArgs.size == 5 do
    throwError "Native074 expected actual original submodule additive-subgroup5."
  let commRingParent := subgroupClass.getAppArgs[2]!.consumeMData
  unless commRingParent.getAppFn.isConstOf ``CommRing.toRing &&
      commRingParent.getAppArgs.size == 2 do
    throwError "Native074 expected diagnosed original CommRing.toRing2."
  let fieldCommRing := commRingParent.getAppArgs[1]!.consumeMData
  unless fieldCommRing.getAppFn.isConstOf ``Field.toCommRing &&
      fieldCommRing.getAppArgs.size == 2 do
    throwError "Native074 requires the SAME actual Field.toCommRing2 parent."
  let fieldArgs := fieldCommRing.getAppArgs
  unless fieldArgs[0]!.consumeMData.equal commRingParent.getAppArgs[0]!.consumeMData do
    throwError "Native074 refuses changed actual field/ring carriers."
  let .const _ levels := fieldCommRing.getAppFn
    | throwError "Native074 expected actual field projection universes."
  unless levels.length == 1 do
    throwError "Native074 refuses a different field projection universe vector."
  let law ← phiNativeNoRecovery025
    (mkAppN (mkConst
      ``PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Diamond154.field_ring_eq levels)
      fieldArgs)
  let lawType ← phiNativeNoRecovery025 (← whnf (← inferType law))
  let some (ringType, divisionRingParent, actualCommRingParent) := lawType.consumeMData.headBeta.eq?
    | throwError "Native074 existing ordinary field law did not return exact Eq3."
  unless actualCommRingParent.consumeMData.equal commRingParent do
    throwError "Native074 existing field law does not have the exact stored original CommRing endpoint."
  let division := divisionRingParent.consumeMData
  unless division.getAppFn.isConstOf ``DivisionRing.toRing && division.getAppArgs.size == 2 &&
      division.getAppArgs[0]!.consumeMData.equal fieldArgs[0]!.consumeMData do
    throwError "Native074 refuses a changed actual division-ring carrier."
  let fieldDivision := division.getAppArgs[1]!.consumeMData
  unless fieldDivision.getAppFn.isConstOf ``Field.toDivisionRing &&
      fieldDivision.getAppArgs.size == 2 do
    throwError "Native074 expected only the SAME Field.toDivisionRing2 parent."
  for i in [:2] do
    unless fieldDivision.getAppArgs[i]!.consumeMData.equal fieldArgs[i]!.consumeMData do
      throwError "Native074 refuses a changed original field-parent argument."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``Eq.symm [← getLevel ringType])
      #[ringType, divisionRingParent, actualCommRingParent, law])
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (actualRingType, actualLeft, actualRight) := proofType.consumeMData.headBeta.eq?
    | throwError "Native074 reversed ordinary law did not return Eq3."
  unless actualRingType.consumeMData.equal ringType.consumeMData &&
      actualLeft.consumeMData.equal commRingParent &&
      actualRight.consumeMData.equal divisionRingParent.consumeMData do
    throwError "Native074 reversed ordinary law changed original ring-parent vector."
  logInfo "Native074 existing ordinary field_ring_eq applied to exact passed point-own Field carrier/instance vector; both stored projection endpoints raw guarded."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOwnFieldRingDiamond074
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_own_field_ring_diamond074%
      (actualOriginalGlobalPhiNativeDifferentialPointOwn061 p hp P hP s)) :=
  phi_native_own_field_ring_diamond074%
    (actualOriginalGlobalPhiNativeDifferentialPointOwn061 p hp P hP s)

private def phiNativeOriginalDifferentialPointLiftProp075
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) : Prop :=
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let W := schemeRelativeDifferentials (toBase I)
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let cW := (actualPositiveTwistPullbackTensorIso I q W 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let Dg := actualGlobalClosedConormalDifferentialMap (toBase I) q
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      W (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      J (closedImmersionModule j) (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    let Etw := actualOriginalQuadraticConormalPointChartIso p hp P hP
    let x : RingHom.ker C.residue :=
      ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let E := actualAffineSchemeDifferentialPointFiberEquiv (k := K) C.residue
    E (G.map (Dg ≫ Et.hom ≫ Ebase.hom) (G.map cJ z)) =
    E (actualAffineDifferentialPointClass (k := K) C.residue x.1)

meta section
open Lean Meta Elab Term

/-- The exact ring parent at the diagnosed localization/submodule spine. -/
private def phiNativeCarrierRingParent075 (carrier : Expr) : TermElabM Expr := do
  let mut current := carrier.consumeMData.headBeta
  for (index, arity, headName) in
      #[(2, 3, ``ModuleCat.carrier), (5, 6, ``CategoryTheory.Functor.obj),
        (5, 6, ``CategoryTheory.Functor.obj), (3, 4, ``schemeRelativeDifferentials),
        (1, 3, ``AlgebraicGeometry.Spec.map), (1, 2, ``CommRingCat.of),
        (5, 11, ``HomogeneousLocalization.homogeneousLocalizationCommRing),
        (2, 5, ``Submodule.addSubgroupClass)] do
    let expectedAux := Name.str ``actualOriginalGlobalPhiNativeHeaderProposition016 "_proof_4"
    if headName == ``Submodule.addSubgroupClass && current.getAppFn.isConstOf expectedAux then
      unless current.getAppArgs.size == 4 do
        throwError "Native077 refuses a different argument vector for original stored instance016._proof_4."
      let some opened ← delta? current (fun n => n == expectedAux) (allowOpaque := true)
        | throwError "Native077 could not open only exact original stored instance016._proof_4."
      current ← phiNativeNoRecovery025 opened.consumeMData.headBeta
      logInfo "Native077 ONLY exact original stored instance016._proof_4/4 exposed at diagnosed subgroup slot; original carrier expressions unchanged."
    let args := current.getAppArgs
    unless current.getAppFn.isConstOf headName && args.size == arity do
      throwError m!"Native075 unexpected actual ring-parent spine {headName}/{arity}; got {current.getAppFn}/{args.size}."
    current := args[index]!.consumeMData.headBeta
  return current

/-- Read only passed061's stored carrier and the exact original23-let E domain.
The original literal equation is a proposition factory, never a hypothesis. -/
private def phiNativeOriginalCarrierVectors075 (source nativeProp : Expr) :
    TermElabM (Expr × Expr) := do
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeDifferentialPointOwn061 &&
      nativeProp.getAppFn.isConstOf ``phiNativeOriginalDifferentialPointLiftProp075 &&
      source.getAppArgs.size == 8 && nativeProp.getAppArgs.size == 8 do
    throwError "Native075 requires only original PointOwn0618 and exact native proposition0758."
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native075 refuses changed original scalar/point/section/hypothesis arguments."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (sourceCarrier, _, _) := sourceType.consumeMData.headBeta.eq?
    | throwError "Native075 expected exact passed original point Eq3."
  let some unfolded ← delta? nativeProp (fun n => n == ``phiNativeOriginalDifferentialPointLiftProp075)
    | throwError "Native075 could not open only exact original native proposition factory."
  let mut body := unfolded.consumeMData.headBeta
  let mut eliminated : Nat := 0
  for _ in [:23] do
    match body with
    | .letE _ _ value innerBody _ =>
      body := (innerBody.instantiate1 value).consumeMData.headBeta
      eliminated := eliminated + 1
    | _ => pure ()
  unless eliminated == 23 do
    throwError "Native075 expected exact original23-let native proposition telescope."
  let closedBody ← phiNativeNoRecovery025 body
  let some (_, nativeLeft, nativeRight) := closedBody.consumeMData.headBeta.eq?
    | throwError "Native075 original telescope did not expose exact native E-lift Eq3."
  let nativeLeft := nativeLeft.consumeMData.headBeta
  let nativeRight := nativeRight.consumeMData.headBeta
  let la := nativeLeft.getAppArgs
  let ra := nativeRight.getAppArgs
  unless nativeLeft.getAppFn.isConstOf ``DFunLike.coe &&
      nativeRight.getAppFn.equal nativeLeft.getAppFn && la.size == 6 && ra.size == 6 do
    throwError "Native075 expected original literal E.coercion6 endpoints."
  for i in [:5] do
    unless la[i]!.consumeMData.equal ra[i]!.consumeMData do
      throwError "Native075 refuses changed original E function/scalar/carrier prefix."
  return (sourceCarrier, la[1]!)

private def phiNativeCarrierRingSeed075 (sourceCarrier nativeCarrier ringProof : Expr) :
    TermElabM (Expr × Expr × Expr) := do
  unless ringProof.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOwnFieldRingDiamond074 &&
      ringProof.getAppArgs.size == 8 do
    throwError "Native075 requires only passed ordinary original field-ring074 certificate."
  let ringType ← phiNativeNoRecovery025 (← whnf (← inferType ringProof))
  let some (_, ringLeft, ringRight) := ringType.consumeMData.headBeta.eq?
    | throwError "Native075 requires exact closed ordinary field-ring Eq3."
  let actualLeft ← phiNativeCarrierRingParent075 sourceCarrier
  let actualRight ← phiNativeCarrierRingParent075 nativeCarrier
  unless ringLeft.consumeMData.headBeta.equal actualLeft &&
      ringRight.consumeMData.headBeta.equal actualRight do
    throwError "Native075 rejects field-ring certificate on different actual original parent vectors."
  return (ringLeft, ringRight, ← mkHEqOfEq ringProof)

elab "phi_native_carrier_projection075% " supplied:term " with_native " nativeProp:term
    " using_ring " suppliedRing:term " using_projection " suppliedProjection:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let (sourceCarrier, nativeCarrier) ← phiNativeOriginalCarrierVectors075 source nativeProp
  let ringProof ← phiNativeNoRecovery025 (← Term.elabTerm suppliedRing none (catchExPostpone := false))
  let (ringLeft, ringRight, ringHEq) ← phiNativeCarrierRingSeed075 sourceCarrier nativeCarrier ringProof
  let ringReverse ← mkHEqSymm ringHEq
  let (algebraProjection, chartMap) ← phiNativeChartProjectionPair044 nativeCarrier sourceCarrier
  let desiredType ← mkHEq algebraProjection chartMap
  let projectionProof ← phiNativeNoRecovery025
    (← Term.elabTerm suppliedProjection none (catchExPostpone := false))
  unless projectionProof.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeChartProjectionOwn051 &&
      projectionProof.getAppArgs.size == 8 do
    throwError "Native075 requires only passed original chart-projection-own051 certificate."
  for i in [:8] do
    unless projectionProof.getAppArgs[i]!.consumeMData.equal source.getAppArgs[i]!.consumeMData &&
        ringProof.getAppArgs[i]!.consumeMData.equal source.getAppArgs[i]!.consumeMData do
      throwError "Native075 refuses changed original projection/ring certificate argument vectors."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType projectionProof))
  let (typeHEq, state) ←
    (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.structuralHEq
      sourceType desiredType 96 #[] "full142").run
        { pairs := #[(ringLeft, ringRight, ringHEq), (ringRight, ringLeft, ringReverse)] }
  let typeEq ← mkEqOfHEq typeHEq
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``Eq.mp [Level.zero]) #[sourceType, desiredType, typeEq, projectionProof])
  let actualType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  unless actualType.consumeMData.headBeta.equal desiredType.consumeMData.headBeta do
    throwError "Native075 ordinary projection transport changed exact actual endpoint proposition."
  logInfo m!"Native075 ordinary actual carrier projection transport consumes074: native={state.wrapperLeaves}, proof={state.proofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}."
  return proof

end

private lemma actualOriginalGlobalPhiNativeCarrierProjection075
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_carrier_projection075%
      (actualOriginalGlobalPhiNativeDifferentialPointOwn061 p hp P hP s)
      with_native (phiNativeOriginalDifferentialPointLiftProp075 p hp P hP s)
      using_ring (actualOriginalGlobalPhiNativeOwnFieldRingDiamond074 p hp P hP s)
      using_projection (actualOriginalGlobalPhiNativeChartProjectionOwn051 p hp P hP s)) :=
  phi_native_carrier_projection075%
      (actualOriginalGlobalPhiNativeDifferentialPointOwn061 p hp P hP s)
      with_native (phiNativeOriginalDifferentialPointLiftProp075 p hp P hP s)
      using_ring (actualOriginalGlobalPhiNativeOwnFieldRingDiamond074 p hp P hP s)
      using_projection (actualOriginalGlobalPhiNativeChartProjectionOwn051 p hp P hP s)

meta section
open Lean Meta Elab Term

elab "phi_native_input_carrier075% " supplied:term " with_native " nativeProp:term
    " using_ring " suppliedRing:term " using_projection " suppliedProjection:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let (sourceCarrier, nativeCarrier) ← phiNativeOriginalCarrierVectors075 source nativeProp
  let ringProof ← phiNativeNoRecovery025 (← Term.elabTerm suppliedRing none (catchExPostpone := false))
  let (ringLeft, ringRight, ringHEq) ← phiNativeCarrierRingSeed075 sourceCarrier nativeCarrier ringProof
  let ringReverse ← mkHEqSymm ringHEq
  let projectionProof ← phiNativeNoRecovery025
    (← Term.elabTerm suppliedProjection none (catchExPostpone := false))
  unless projectionProof.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeCarrierProjection075 &&
      projectionProof.getAppArgs.size == 8 do
    throwError "Native075 requires only actual carrier projection075 certificate."
  for i in [:8] do
    unless projectionProof.getAppArgs[i]!.consumeMData.equal source.getAppArgs[i]!.consumeMData &&
        ringProof.getAppArgs[i]!.consumeMData.equal source.getAppArgs[i]!.consumeMData do
      throwError "Native075 refuses changed original carrier seed argument vectors."
  let projectionType ← phiNativeNoRecovery025 (← whnf (← inferType projectionProof))
  let some (_, projectionLeft, _, projectionRight) := projectionType.consumeMData.headBeta.heq?
    | throwError "Native075 requires exact closed actual projection HEq4."
  let (actualLeft, actualRight) ← phiNativeChartProjectionPair044 nativeCarrier sourceCarrier
  unless projectionLeft.consumeMData.equal actualLeft.consumeMData &&
      projectionRight.consumeMData.equal actualRight.consumeMData do
    throwError "Native075 actual chart certificate does not join original carrier projection vectors."
  let projectionReverse ← mkHEqSymm projectionProof
  let (proof, state) ←
    (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.structuralHEq
      sourceCarrier nativeCarrier 96 #[] "full142").run
        { pairs := #[(ringLeft, ringRight, ringHEq), (ringRight, ringLeft, ringReverse),
          (projectionLeft, projectionRight, projectionProof),
          (projectionRight, projectionLeft, projectionReverse)] }
  let proof ← phiNativeNoRecovery025 proof
  let actualType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (_, actualSource, _, actualNative) := actualType.consumeMData.headBeta.heq?
    | throwError "Native075 ordinary carrier transport did not return actual HEq4."
  unless actualSource.consumeMData.equal sourceCarrier.consumeMData &&
      actualNative.consumeMData.equal nativeCarrier.consumeMData do
    throwError "Native075 ordinary carrier transport changed exact original carrier endpoints."
  logInfo m!"Native075 ordinary original input-carrier HEq consumes074 and projection075: native={state.wrapperLeaves}, proof={state.proofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}."
  return proof

end
private lemma actualOriginalGlobalPhiNativeInputCarrierHEq075
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_input_carrier075%
      (actualOriginalGlobalPhiNativeDifferentialPointOwn061 p hp P hP s)
      with_native (phiNativeOriginalDifferentialPointLiftProp075 p hp P hP s)
      using_ring (actualOriginalGlobalPhiNativeOwnFieldRingDiamond074 p hp P hP s)
      using_projection (actualOriginalGlobalPhiNativeCarrierProjection075 p hp P hP s)) :=
  phi_native_input_carrier075%
      (actualOriginalGlobalPhiNativeDifferentialPointOwn061 p hp P hP s)
      with_native (phiNativeOriginalDifferentialPointLiftProp075 p hp P hP s)
      using_ring (actualOriginalGlobalPhiNativeOwnFieldRingDiamond074 p hp P hP s)
      using_projection (actualOriginalGlobalPhiNativeCarrierProjection075 p hp P hP s)

meta section
open Lean Meta Elab Term Tactic

private def phiNativeJoinHead070 (e : Expr) : String :=
  let e := e.consumeMData
  let label := match e.getAppFn with
    | .const n levels => s!"const {n}; levels={reprStr levels}"
    | .fvar id => s!"fvar {id.name}"
    | .bvar i => s!"bvar {i}"
    | .proj n i _ => s!"projection {n}[{i}]"
    | .lam .. => "lambda"
    | .forallE .. => "forall"
    | .letE .. => "let"
    | .sort level => s!"sort {reprStr level}"
    | .lit value => s!"literal {reprStr value}"
    | .mvar id => s!"mvar {id.name}"
    | _ => "other"
  s!"{label}; arguments={e.getAppArgs.size}"

/-- Eight raw nodes on the first unequal child path; no normalization or proof. -/
private def phiNativeJoinPath070 (label : String) (initialLeft initialRight : Expr) : TermElabM Unit := do
  let mut left := initialLeft.consumeMData
  let mut right := initialRight.consumeMData
  let mut path := label
  for _ in [:8] do
    if left.equal right then
      logInfo m!"Native070 {path}: raw equal."
      return
    logInfo m!"Native070 {path}: left={phiNativeJoinHead070 left}; right={phiNativeJoinHead070 right}."
    logInfo m!"Native070 {path}: left local={← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.diagnosticLocal093 left}; right local={← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.diagnosticLocal093 right}."
    if left.getAppFn.equal right.getAppFn then
      let la := left.getAppArgs
      let ra := right.getAppArgs
      if la.size != ra.size then return
      let mut child : Option Nat := none
      for i in [:la.size] do
        if child.isNone && !(la[i]!.consumeMData.equal ra[i]!.consumeMData) then
          child := some i
      match child with
      | some i =>
        left := la[i]!.consumeMData
        right := ra[i]!.consumeMData
        path := path ++ s!".arg[{i}]"
      | none => return
    else
      match left, right with
      | .lam _ lt lb li, .lam _ rt rb ri =>
        logInfo m!"Native070 {path}: lambda binderInfo equal={li == ri}; domain raw={lt.consumeMData.equal rt.consumeMData}; body raw={lb.consumeMData.equal rb.consumeMData}."
        if !(lt.consumeMData.equal rt.consumeMData) then
          left := lt.consumeMData; right := rt.consumeMData; path := path ++ ".domain"
        else
          left := lb.consumeMData; right := rb.consumeMData; path := path ++ ".body"
      | .forallE _ lt lb li, .forallE _ rt rb ri =>
        logInfo m!"Native070 {path}: forall binderInfo equal={li == ri}."
        if !(lt.consumeMData.equal rt.consumeMData) then
          left := lt.consumeMData; right := rt.consumeMData; path := path ++ ".domain"
        else
          left := lb.consumeMData; right := rb.consumeMData; path := path ++ ".body"
      | .letE _ lt lv lb ln, .letE _ rt rv rb rn =>
        logInfo m!"Native070 {path}: let nondependent equal={ln == rn}."
        if !(lt.consumeMData.equal rt.consumeMData) then
          left := lt.consumeMData; right := rt.consumeMData; path := path ++ ".type"
        else if !(lv.consumeMData.equal rv.consumeMData) then
          left := lv.consumeMData; right := rv.consumeMData; path := path ++ ".value"
        else
          left := lb.consumeMData; right := rb.consumeMData; path := path ++ ".body"
      | .proj ln li le, .proj rn ri re =>
        if ln != rn || li != ri then return
        left := le.consumeMData; right := re.consumeMData; path := path ++ ".major"
      | _, _ => return
  logInfo m!"Native070 {path}: eight-node raw diagnostic frontier; left={phiNativeJoinHead070 left}; right={phiNativeJoinHead070 right}."

/- Lift ONLY the actual independently proved native differential-point Eq
through the SAME original E.coercion6. All five function/scalar/type/coercion
arguments, both point values, exact input/output carriers are raw guarded. -/
/-- View only the two original local lets diagnosed by066. The complete viewed
carrier and point must equal the original target vectors before ordinary id. -/
private def phiNativePointOriginalLocalLetView067
    (source sourceCarrier sourceLeft sourceRight targetCarrier targetLeft targetRight : Expr) :
    TermElabM (Expr × Expr × Expr × Expr) := do
  unless sourceLeft.consumeMData.headBeta.equal targetLeft.consumeMData.headBeta do
    throwError "Native067 refuses a changed original mapped left point."
  let point := sourceRight.consumeMData.headBeta
  let pointArgs := point.getAppArgs
  unless point.getAppFn.isConstOf ``actualAffineDifferentialPointClass &&
      pointArgs.size == 9 do
    throwError "Native067 expected exactly the diagnosed original point-class9 vector."
  let .fvar algebraId := pointArgs[6]!.consumeMData
    | throwError "Native067 expected only diagnosed local chart Algebra aKLift063."
  let algebraDecl ← algebraId.getDecl
  unless algebraDecl.userName == `aKLift063 do
    throwError "Native067 refuses a different local chart Algebra."
  let some algebraValue := algebraDecl.value?
    | throwError "Native067 requires actual original chart Algebra let value."
  let algebraValue ← phiNativeNoRecovery025 algebraValue
  unless algebraValue.getAppFn.isConstOf ``RingHom.toAlgebra &&
      algebraValue.getAppArgs.size == 5 do
    throwError "Native067 refuses a different chart Algebra constructor."
  let originalPoint := targetRight.consumeMData.headBeta
  let originalPointArgs := originalPoint.getAppArgs
  unless originalPoint.getAppFn.equal point.getAppFn && originalPointArgs.size == 9 do
    throwError "Native068 refuses a different original point-class constructor."
  let originalAlgebra := originalPointArgs[6]!.consumeMData
  unless originalAlgebra.getAppFn.isConstOf ``RingHom.toAlgebra &&
      originalAlgebra.getAppArgs.size == 5 do
    throwError "Native068 expected the original chart RingHom.toAlgebra5 dictionary."
  let some idealDecl := (← getLCtx).findFromUserName? `I
    | throwError "Native068 requires the original local ideal let I."
  let some idealValue := idealDecl.value?
    | throwError "Native068 refuses an assumed ideal instead of original local let I."
  let idealValue ← phiNativeNoRecovery025 idealValue
  unless idealValue.getAppFn.isConstOf ``AllCharacteristics.HomogeneousProjective.equationIdeal do
    throwError "Native068 refuses a different original ideal-let definition."
  let viewedOriginalAlgebra := originalAlgebra.replace fun e =>
    if e.isFVar && e.fvarId! == idealDecl.fvarId then some idealValue else none
  unless !(viewedOriginalAlgebra.equal originalAlgebra) &&
      viewedOriginalAlgebra.consumeMData.headBeta.equal algebraValue.consumeMData.headBeta do
    logInfo m!"Native068 actual original ideal-let value: {idealValue}"
    logInfo m!"Native068 original chart dictionary after ONLY I substitution: {viewedOriginalAlgebra}"
    logInfo m!"Native068 source chart-Algebra let value: {algebraValue}"
    throwError "Native068 original I-let view does not exactly recover source chart-Algebra value."
  let viewedRight := mkAppN point.getAppFn (pointArgs.set! 6 originalAlgebra)
  let carrier := sourceCarrier.consumeMData
  let ca := carrier.getAppArgs
  unless carrier.getAppFn.isConstOf ``ModuleCat.carrier && ca.size == 3 do
    throwError "Native067 expected exact diagnosed ModuleCat.carrier3."
  let outerCarrier := ca[0]!.consumeMData
  let oa := outerCarrier.getAppArgs
  unless outerCarrier.getAppFn.isConstOf ``CommRingCat.carrier && oa.size == 1 do
    throwError "Native067 expected exact diagnosed outer ring carrier."
  let ringOf := oa[0]!.consumeMData
  let ba := ringOf.getAppArgs
  unless ringOf.getAppFn.isConstOf ``CommRingCat.of && ba.size == 2 do
    throwError "Native067 expected exact diagnosed bundled ring of2."
  let innerCarrier := ba[0]!.consumeMData
  let ia := innerCarrier.getAppArgs
  unless innerCarrier.getAppFn.isConstOf ``CommRingCat.carrier && ia.size == 1 do
    throwError "Native067 expected exact diagnosed inner ring carrier."
  let .fvar residueId := ia[0]!.consumeMData
    | throwError "Native067 expected only diagnosed local residue-field L."
  let residueDecl ← residueId.getDecl
  unless residueDecl.userName == `L do
    throwError "Native067 refuses a different local residue-field let."
  let some residueValue := residueDecl.value?
    | throwError "Native067 requires actual original residue-field let value."
  let residueValue ← phiNativeNoRecovery025 residueValue
  unless residueValue.getAppFn.isConstOf ``AlgebraicGeometry.Scheme.residueField &&
      residueValue.getAppArgs.size == 2 do
    throwError "Native067 refuses a different original residue-field constructor."
  let viewedCarrier := carrier.replace fun e =>
    if e.isFVar && e.fvarId! == residueId then some residueValue else none
  let sourceObject := viewedCarrier.getAppArgs[2]!.consumeMData
  let originalCarrier := targetCarrier.consumeMData
  unless originalCarrier.getAppFn.equal carrier.getAppFn &&
      originalCarrier.getAppArgs.size == 3 do
    throwError "Native070 refuses a different original E carrier constructor."
  let originalObject := originalCarrier.getAppArgs[2]!.consumeMData
  let sourceObjectArgs := sourceObject.getAppArgs
  let originalObjectArgs := originalObject.getAppArgs
  unless sourceObject.getAppFn.isConstOf ``CategoryTheory.Functor.obj &&
      originalObject.getAppFn.equal sourceObject.getAppFn &&
      sourceObjectArgs.size == 6 && originalObjectArgs.size == 6 do
    throwError "Native070 expected the exact diagnosed Functor.obj6 carrier objects."
  let .fvar functorId := sourceObjectArgs[4]!.consumeMData
    | throwError "Native070 expected only the diagnosed original local functor G."
  let functorDecl ← functorId.getDecl
  unless functorDecl.userName == `G do
    throwError "Native070 refuses a different local section functor."
  let some functorValue := functorDecl.value?
    | throwError "Native070 requires the actual original functor G let value."
  let functorValue ← phiNativeNoRecovery025 functorValue
  unless functorValue.getAppFn.isConstOf ``AlgebraicGeometry.moduleSpecΓFunctor &&
      functorValue.getAppArgs.size == 1 do
    throwError "Native070 refuses a different original section functor constructor."
  let originalFunctor := originalObjectArgs[4]!.consumeMData
  unless originalFunctor.getAppFn.equal functorValue.getAppFn &&
      originalFunctor.getAppArgs.size == 1 do
    throwError "Native070 refuses a different original E section functor."
  let viewedFunctorValue := functorValue.replace fun e =>
    if e.isFVar && e.fvarId! == residueId then some residueValue else none
  unless viewedFunctorValue.consumeMData.headBeta.equal originalFunctor.consumeMData.headBeta do
    phiNativeJoinPath070 "G.own-let-value-after-L-view-to-original-functor"
      viewedFunctorValue.consumeMData.headBeta originalFunctor.consumeMData.headBeta
    throwError "Native070 exact G let value does not recover original section functor."
  let viewedCarrier := viewedCarrier.replace fun e =>
    if e.isFVar && e.fvarId! == functorId then some viewedFunctorValue else none
  logInfo "Native070 ONLY original local G replaced by its actual moduleSpecΓFunctor let value after existing L view; exact original functor vector raw guarded."
  let viewedObject := viewedCarrier.getAppArgs[2]!.consumeMData
  let sourcePullbackObject := viewedObject.getAppArgs[5]!.consumeMData
  let originalPullbackObject := originalObjectArgs[5]!.consumeMData
  let sourcePullbackObjectArgs := sourcePullbackObject.getAppArgs
  let originalPullbackObjectArgs := originalPullbackObject.getAppArgs
  unless sourcePullbackObject.getAppFn.isConstOf ``CategoryTheory.Functor.obj &&
      originalPullbackObject.getAppFn.equal sourcePullbackObject.getAppFn &&
      sourcePullbackObjectArgs.size == 6 && originalPullbackObjectArgs.size == 6 do
    throwError "Native071 expected exact diagnosed pullback Functor.obj6 vectors."
  let sourcePullback := sourcePullbackObjectArgs[4]!.consumeMData
  let originalPullback := originalPullbackObjectArgs[4]!.consumeMData
  let sourcePullbackArgs := sourcePullback.getAppArgs
  let originalPullbackArgs := originalPullback.getAppArgs
  unless sourcePullback.getAppFn.isConstOf ``AlgebraicGeometry.Scheme.Modules.pullback &&
      originalPullback.getAppFn.equal sourcePullback.getAppFn &&
      sourcePullbackArgs.size == 3 && originalPullbackArgs.size == 3 do
    throwError "Native071 expected exact diagnosed pullback3 functors."
  let .fvar immersionId := sourcePullbackArgs[2]!.consumeMData
    | throwError "Native071 expected only diagnosed original local immersion j."
  let immersionDecl ← immersionId.getDecl
  unless immersionDecl.userName == `j do
    throwError "Native071 refuses a different original local immersion."
  let some immersionValue := immersionDecl.value?
    | throwError "Native071 requires the actual original j let value."
  let immersionValue ← phiNativeNoRecovery025 immersionValue
  unless immersionValue.getAppFn.isConstOf ``AlgebraicGeometry.Spec.map &&
      immersionValue.getAppArgs.size == 3 do
    throwError "Native071 refuses a different original immersion constructor."
  let originalImmersion := originalPullbackArgs[2]!.consumeMData
  unless originalImmersion.getAppFn.equal immersionValue.getAppFn &&
      originalImmersion.getAppArgs.size == 3 do
    throwError "Native071 refuses a different original E immersion."
  let viewedImmersionValue := immersionValue.replace fun e =>
    if e.isFVar && e.fvarId! == residueId then some residueValue else none
  unless viewedImmersionValue.consumeMData.headBeta.equal originalImmersion.consumeMData.headBeta do
    phiNativeJoinPath070 "j.own-let-value-after-L-view-to-original-immersion"
      viewedImmersionValue.consumeMData.headBeta originalImmersion.consumeMData.headBeta
    throwError "Native071 exact j let value does not recover original immersion."
  let viewedCarrier := viewedCarrier.replace fun e =>
    if e.isFVar && e.fvarId! == immersionId then some viewedImmersionValue else none
  logInfo "Native071 ONLY original local j replaced by its actual Spec.map let value after existing L view; exact original immersion vector raw guarded."
  let carrierObject := viewedCarrier.getAppArgs[2]!.consumeMData
  let pulledObject := carrierObject.getAppArgs[5]!.consumeMData
  let sourceRelative := pulledObject.getAppArgs[5]!.consumeMData
  let originalRelative := originalPullbackObjectArgs[5]!.consumeMData
  unless sourceRelative.getAppFn.isConstOf ``schemeRelativeDifferentials &&
      originalRelative.getAppFn.equal sourceRelative.getAppFn &&
      sourceRelative.getAppArgs.size == 4 && originalRelative.getAppArgs.size == 4 do
    throwError "Native072 expected exact diagnosed relative-differentials4 vectors."
  let sourceChartMap := sourceRelative.getAppArgs[3]!.consumeMData
  let originalChartMap := originalRelative.getAppArgs[3]!.consumeMData
  unless sourceChartMap.getAppFn.isConstOf ``AlgebraicGeometry.Spec.map &&
      originalChartMap.getAppFn.equal sourceChartMap.getAppFn &&
      sourceChartMap.getAppArgs.size == 3 && originalChartMap.getAppArgs.size == 3 do
    throwError "Native072 expected exact diagnosed chart Spec.map3 vectors."
  let sourceChartRingOf := sourceChartMap.getAppArgs[1]!.consumeMData
  let originalChartRingOf := originalChartMap.getAppArgs[1]!.consumeMData
  unless sourceChartRingOf.getAppFn.isConstOf ``CommRingCat.of &&
      originalChartRingOf.getAppFn.equal sourceChartRingOf.getAppFn &&
      sourceChartRingOf.getAppArgs.size == 2 && originalChartRingOf.getAppArgs.size == 2 do
    throwError "Native072 expected exact diagnosed chart ring of2 vectors."
  let sourceChartRing := sourceChartRingOf.getAppArgs[0]!.consumeMData
  let originalChartRing := originalChartRingOf.getAppArgs[0]!.consumeMData
  unless sourceChartRing.getAppFn.isConstOf ``AllCharacteristics.HomogeneousProjective.ChartRing &&
      originalChartRing.getAppFn.equal sourceChartRing.getAppFn &&
      sourceChartRing.getAppArgs.size == 5 && originalChartRing.getAppArgs.size == 5 do
    throwError "Native072 expected exact diagnosed ChartRing5 vectors."
  let .fvar carrierIdealId := sourceChartRing.getAppArgs[3]!.consumeMData
    | throwError "Native072 expected only diagnosed original I in chart carrier."
  unless carrierIdealId == idealDecl.fvarId do
    throwError "Native072 refuses a different chart-ring ideal let."
  let viewedChartRing := sourceChartRing.replace fun e =>
    if e.isFVar && e.fvarId! == idealDecl.fvarId then some idealValue else none
  unless viewedChartRing.consumeMData.headBeta.equal originalChartRing.consumeMData.headBeta do
    phiNativeJoinPath070 "I.own-let-value-chart-ring-to-original-chart-ring"
      viewedChartRing.consumeMData.headBeta originalChartRing.consumeMData.headBeta
    throwError "Native072 exact I let view does not recover original chart-ring vector."
  let viewedCarrier := viewedCarrier.replace fun e =>
    if e.isFVar && e.fvarId! == idealDecl.fvarId then some idealValue else none
  logInfo "Native072 ONLY same original I let replaced by its actual equationIdeal value in carrier; entire diagnosed ChartRing vector raw guarded."
  unless viewedRight.consumeMData.headBeta.equal targetRight.consumeMData.headBeta do
    logInfo m!"Native067 chart-let value: {algebraValue}"
    logInfo m!"Native067 original point dictionary: {targetRight.getAppArgs[6]!}"
    throwError "Native067 diagnosed chart-let view does not exactly recover the original point vector."
  unless viewedCarrier.consumeMData.headBeta.equal targetCarrier.consumeMData.headBeta do
    phiNativeJoinPath070 "inputcarrier.after-exact-L-G-j-I-views-to-original-E-domain"
      viewedCarrier.consumeMData.headBeta targetCarrier.consumeMData.headBeta
    logInfo m!"Native067 residue-let viewed carrier: {viewedCarrier}"
    logInfo m!"Native067 original E input carrier: {targetCarrier}"
    throwError "Native067 diagnosed residue-let view does not exactly recover original input carrier."
  let proposition := mkAppN (mkConst ``Eq [← getLevel viewedCarrier])
    #[viewedCarrier, sourceLeft, viewedRight]
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``id [Level.zero]) #[proposition, source])
  let actualType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  unless actualType.consumeMData.headBeta.equal proposition.consumeMData.headBeta do
    throwError "Native067 ordinary id did not retain the exact original viewed Eq vector."
  logInfo "Native067 ordinary id preserves original point proof through ONLY actual chart-Algebra and residue-field local-let values; complete resulting carrier/points raw guarded."
  return (proof, viewedCarrier, sourceLeft, viewedRight)

elab "phi_native_differential_point_lift_exact061 " supplied:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let pointProof ← Term.elabTerm supplied none (catchExPostpone := false)
    let pointProof ← phiNativeNoRecovery025 pointProof
    let pointProposition ← phiNativeNoRecovery025 (← whnf (← inferType pointProof))
    let some (inputCarrier, inputLeft, inputRight) :=
        pointProposition.consumeMData.headBeta.eq?
      | throwError "Native065 expected a fully instantiated original native point Eq3 type."
    let target ← instantiateMVars (← goal.getType)
    let some (outputCarrier, targetLeft, targetRight) := target.consumeMData.eq?
      | throwError "Native061 expected only the literal native E-lift Eq3 goal."
    let left := targetLeft.consumeMData.headBeta
    let right := targetRight.consumeMData.headBeta
    let la := left.getAppArgs
    let ra := right.getAppArgs
    unless left.getAppFn.isConstOf ``DFunLike.coe &&
        right.getAppFn.equal left.getAppFn && la.size == 6 && ra.size == 6 do
      throwError "Native061 expected exact original E.coercion6 endpoints."
    for i in [:5] do
      unless la[i]!.consumeMData.equal ra[i]!.consumeMData do
        throwError "Native061 refuses changed original E.coercion argument {i}."
    let (pointProof, inputCarrier, inputLeft, inputRight) ←
      phiNativePointOriginalLocalLetView067 pointProof inputCarrier inputLeft inputRight
        la[1]! la[5]! ra[5]!
    unless la[5]!.consumeMData.headBeta.equal inputLeft.consumeMData.headBeta &&
        ra[5]!.consumeMData.headBeta.equal inputRight.consumeMData.headBeta do
      throwError "Native061 refuses an equality on different original native differential points."
    unless la[1]!.consumeMData.headBeta.equal inputCarrier.consumeMData.headBeta do
      logInfo m!"Native061 point Eq carrier: {inputCarrier}"
      logInfo m!"Native061 original E input domain: {la[1]!}"
      throwError "Native061 refuses a different original E input carrier; ordinary exact carrier certificate required."
    let evaluator ← withLocalDeclD `differentialPoint inputCarrier fun differentialPoint =>
      mkLambdaFVars #[differentialPoint]
        (mkAppN left.getAppFn (la.set! 5 differentialPoint))
    let .forallE _ domain codomain _ := (← inferType evaluator).consumeMData
      | throwError "Native061 original evaluator did not retain a function type."
    unless domain.consumeMData.equal inputCarrier.consumeMData &&
        (codomain.instantiate1 inputLeft).consumeMData.headBeta.equal
          outputCarrier.consumeMData.headBeta do
      throwError "Native061 evaluator changed exact original input/output carriers."
    let proof ← phiNativeNoRecovery025
      (mkAppN (mkConst ``congrArg [← getLevel inputCarrier, ← getLevel outputCarrier])
        #[inputCarrier, outputCarrier, inputLeft, inputRight, evaluator, pointProof])
    let (actualCarrier, actualLeft, actualRight) ← phiNativeStoredEq018 proof
    unless actualCarrier.consumeMData.equal outputCarrier.consumeMData &&
        actualLeft.consumeMData.headBeta.equal left &&
        actualRight.consumeMData.headBeta.equal right do
      throwError "Native061 ordinary congrArg changed original literal E-lift carrier/endpoints."
    logInfo "Native061 ordinary congrArg lifts exact native point Eq with full stored original input/output/points/evaluator/proof vectors; original E prefix and carrier raw guarded."
    goal.assign proof
    replaceMainGoal []

end

meta section
open Lean Meta Elab Term

private def phiNativeLiteralLiftBody078 (nativeProp : Expr) : TermElabM Expr := do
  unless nativeProp.getAppFn.isConstOf ``phiNativeOriginalDifferentialPointLiftProp075 &&
      nativeProp.getAppArgs.size == 8 do
    throwError "Native078 requires only exact original native proposition0758."
  let some unfolded ← delta? nativeProp (fun n => n == ``phiNativeOriginalDifferentialPointLiftProp075)
    | throwError "Native078 could not open exact original native proposition factory."
  let mut body := unfolded.consumeMData.headBeta
  let mut eliminated : Nat := 0
  for _ in [:23] do
    match body with
    | .letE _ _ value innerBody _ =>
      body := (innerBody.instantiate1 value).consumeMData.headBeta
      eliminated := eliminated + 1
    | _ => pure ()
  unless eliminated == 23 do
    throwError "Native078 requires exact original23-let native proposition telescope."
  let closedBody ← phiNativeNoRecovery025 body
  unless closedBody.consumeMData.headBeta.eq?.isSome do
    throwError "Native078 requires literal native E-lift Eq3 after only original top lets."
  return closedBody

private def phiNativeLiftBodyVectors078 (body : Expr) : TermElabM (Expr × Expr × Expr × Array Expr × Array Expr) := do
  let some (outputCarrier, nativeLeft, nativeRight) := body.consumeMData.headBeta.eq?
    | throwError "Native078 expected literal native E-lift Eq3."
  let nativeLeft := nativeLeft.consumeMData.headBeta
  let nativeRight := nativeRight.consumeMData.headBeta
  let la := nativeLeft.getAppArgs
  let ra := nativeRight.getAppArgs
  unless nativeLeft.getAppFn.isConstOf ``DFunLike.coe &&
      nativeRight.getAppFn.equal nativeLeft.getAppFn && la.size == 6 && ra.size == 6 do
    throwError "Native078 expected only original E.coercion6 endpoints."
  for i in [:5] do
    unless la[i]!.consumeMData.equal ra[i]!.consumeMData do
      throwError "Native078 refuses changed original E coercion/function/scalar/carrier prefix."
  return (outputCarrier, nativeLeft, nativeRight, la, ra)

/-- Prove compatibility of each actual point separately, rather than treating
raw equality of elaborated dictionaries as a certificate. Source values come
only from passed PointOwn061; target values come only from the original075
literal E inputs. Every seed carries an ordinary proved original equality. -/
elab "phi_native_point_endpoint079% " side:num supplied:term " with_native " nativeProp:term
    " using_carrier " suppliedCarrier:term " using_ring " suppliedRing:term
    " using_projection " suppliedProjection:term : term => do
  unless side.getNat < 2 do
    throwError "Native079 requires only actual original left or right input point."
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let (sourceCarrier, nativeCarrier) ← phiNativeOriginalCarrierVectors075 source nativeProp
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (_, sourceLeft, sourceRight) := sourceType.consumeMData.headBeta.eq?
    | throwError "Native079 requires exact passed original point Eq3."
  let body ← phiNativeLiteralLiftBody078 nativeProp
  let (_, _, _, la, ra) ← phiNativeLiftBodyVectors078 body
  let sourcePoint := if side.getNat == 0 then sourceLeft else sourceRight
  let nativePoint := if side.getNat == 0 then la[5]! else ra[5]!
  let carrierProof ← phiNativeNoRecovery025
    (← Term.elabTerm suppliedCarrier none (catchExPostpone := false))
  let ringProof ← phiNativeNoRecovery025
    (← Term.elabTerm suppliedRing none (catchExPostpone := false))
  let projectionProof ← phiNativeNoRecovery025
    (← Term.elabTerm suppliedProjection none (catchExPostpone := false))
  unless carrierProof.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeInputCarrierHEq075 &&
      ringProof.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOwnFieldRingDiamond074 &&
      projectionProof.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeCarrierProjection075 &&
      carrierProof.getAppArgs.size == 8 && ringProof.getAppArgs.size == 8 &&
      projectionProof.getAppArgs.size == 8 do
    throwError "Native079 requires only passed original carrier075/ring074/projection075 values."
  for i in [:8] do
    unless carrierProof.getAppArgs[i]!.consumeMData.equal source.getAppArgs[i]!.consumeMData &&
        ringProof.getAppArgs[i]!.consumeMData.equal source.getAppArgs[i]!.consumeMData &&
        projectionProof.getAppArgs[i]!.consumeMData.equal source.getAppArgs[i]!.consumeMData do
      throwError "Native079 refuses changed original eight-argument seed vectors."
  let carrierType ← phiNativeNoRecovery025 (← whnf (← inferType carrierProof))
  let some (_, carrierLeft, _, carrierRight) := carrierType.consumeMData.headBeta.heq?
    | throwError "Native079 requires original carrier HEq4."
  unless carrierLeft.consumeMData.equal sourceCarrier.consumeMData &&
      carrierRight.consumeMData.equal nativeCarrier.consumeMData do
    throwError "Native079 carrier certificate does not join exact original carriers."
  let (ringLeft, ringRight, ringHEq) ← phiNativeCarrierRingSeed075 sourceCarrier nativeCarrier ringProof
  let projectionType ← phiNativeNoRecovery025 (← whnf (← inferType projectionProof))
  let some (_, projectionLeft, _, projectionRight) := projectionType.consumeMData.headBeta.heq?
    | throwError "Native079 requires original projection HEq4."
  let (actualProjection, actualChartMap) ← phiNativeChartProjectionPair044 nativeCarrier sourceCarrier
  unless projectionLeft.consumeMData.equal actualProjection.consumeMData &&
      projectionRight.consumeMData.equal actualChartMap.consumeMData do
    throwError "Native079 projection certificate does not join exact original map vectors."
  let carrierReverse ← mkHEqSymm carrierProof
  let ringReverse ← mkHEqSymm ringHEq
  let projectionReverse ← mkHEqSymm projectionProof
  let (proof, state) ←
    (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.structuralHEq
      sourcePoint nativePoint 96 #[] "full142").run
        { pairs := #[(sourceCarrier, nativeCarrier, carrierProof),
          (nativeCarrier, sourceCarrier, carrierReverse),
          (ringLeft, ringRight, ringHEq), (ringRight, ringLeft, ringReverse),
          (projectionLeft, projectionRight, projectionProof),
          (projectionRight, projectionLeft, projectionReverse)] }
  let proof ← phiNativeNoRecovery025 proof
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (_, actualSource, _, actualNative) := proofType.consumeMData.headBeta.heq?
    | throwError "Native079 ordinary point compatibility did not return HEq4."
  unless actualSource.consumeMData.equal sourcePoint.consumeMData &&
      actualNative.consumeMData.equal nativePoint.consumeMData do
    throwError "Native079 ordinary point compatibility changed original literal endpoints."
  logInfo m!"Native079 actual original input side{side.getNat} HEq consumes passed carrier/ring/projection: native={state.wrapperLeaves}, proof={state.proofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}."
  return proof

end

private lemma actualOriginalGlobalPhiNativePointInputLeftHEq079
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_point_endpoint079% 0
      (actualOriginalGlobalPhiNativeDifferentialPointOwn061 p hp P hP s)
      with_native (phiNativeOriginalDifferentialPointLiftProp075 p hp P hP s)
      using_carrier (actualOriginalGlobalPhiNativeInputCarrierHEq075 p hp P hP s)
      using_ring (actualOriginalGlobalPhiNativeOwnFieldRingDiamond074 p hp P hP s)
      using_projection (actualOriginalGlobalPhiNativeCarrierProjection075 p hp P hP s)) :=
  phi_native_point_endpoint079% 0
      (actualOriginalGlobalPhiNativeDifferentialPointOwn061 p hp P hP s)
      with_native (phiNativeOriginalDifferentialPointLiftProp075 p hp P hP s)
      using_carrier (actualOriginalGlobalPhiNativeInputCarrierHEq075 p hp P hP s)
      using_ring (actualOriginalGlobalPhiNativeOwnFieldRingDiamond074 p hp P hP s)
      using_projection (actualOriginalGlobalPhiNativeCarrierProjection075 p hp P hP s)

private lemma actualOriginalGlobalPhiNativePointInputRightHEq079
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_point_endpoint079% 1
      (actualOriginalGlobalPhiNativeDifferentialPointOwn061 p hp P hP s)
      with_native (phiNativeOriginalDifferentialPointLiftProp075 p hp P hP s)
      using_carrier (actualOriginalGlobalPhiNativeInputCarrierHEq075 p hp P hP s)
      using_ring (actualOriginalGlobalPhiNativeOwnFieldRingDiamond074 p hp P hP s)
      using_projection (actualOriginalGlobalPhiNativeCarrierProjection075 p hp P hP s)) :=
  phi_native_point_endpoint079% 1
      (actualOriginalGlobalPhiNativeDifferentialPointOwn061 p hp P hP s)
      with_native (phiNativeOriginalDifferentialPointLiftProp075 p hp P hP s)
      using_carrier (actualOriginalGlobalPhiNativeInputCarrierHEq075 p hp P hP s)
      using_ring (actualOriginalGlobalPhiNativeOwnFieldRingDiamond074 p hp P hP s)
      using_projection (actualOriginalGlobalPhiNativeCarrierProjection075 p hp P hP s)

meta section
open Lean Meta Elab Term

elab "phi_native_point_retag078% " supplied:term " with_native " nativeProp:term
    " using_carrier " suppliedCarrier:term " using_left " suppliedLeft:term
    " using_right " suppliedRight:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeDifferentialPointOwn061 &&
      source.getAppArgs.size == 8 do
    throwError "Native078 requires only passed original point-own0618."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (sourceCarrier, sourceLeft, sourceRight) := sourceType.consumeMData.headBeta.eq?
    | throwError "Native078 requires exact original point Eq3."
  let body ← phiNativeLiteralLiftBody078 nativeProp
  let (_, _, _, la, ra) ← phiNativeLiftBodyVectors078 body
  let leftProof ← phiNativeNoRecovery025
    (← Term.elabTerm suppliedLeft none (catchExPostpone := false))
  let rightProof ← phiNativeNoRecovery025
    (← Term.elabTerm suppliedRight none (catchExPostpone := false))
  unless leftProof.getAppFn.isConstOf ``actualOriginalGlobalPhiNativePointInputLeftHEq079 &&
      rightProof.getAppFn.isConstOf ``actualOriginalGlobalPhiNativePointInputRightHEq079 &&
      leftProof.getAppArgs.size == 8 && rightProof.getAppArgs.size == 8 do
    throwError "Native079 requires only exact ordinary original point endpoint certificates."
  for i in [:8] do
    unless leftProof.getAppArgs[i]!.consumeMData.equal source.getAppArgs[i]!.consumeMData &&
        rightProof.getAppArgs[i]!.consumeMData.equal source.getAppArgs[i]!.consumeMData do
      throwError "Native079 refuses changed original point certificate argument vectors."
  let leftType ← phiNativeNoRecovery025 (← whnf (← inferType leftProof))
  let rightType ← phiNativeNoRecovery025 (← whnf (← inferType rightProof))
  let some (_, leftSource, _, leftNative) := leftType.consumeMData.headBeta.heq?
    | throwError "Native079 requires actual original left endpoint HEq4."
  let some (_, rightSource, _, rightNative) := rightType.consumeMData.headBeta.heq?
    | throwError "Native079 requires actual original right endpoint HEq4."
  unless leftSource.consumeMData.equal sourceLeft.consumeMData &&
      leftNative.consumeMData.equal la[5]!.consumeMData &&
      rightSource.consumeMData.equal sourceRight.consumeMData &&
      rightNative.consumeMData.equal ra[5]!.consumeMData do
    throwError "Native079 ordinary point certificates do not exactly join the original point/E input vectors."
  let nativeCarrier := la[1]!
  let carrierProof ← phiNativeNoRecovery025
    (← Term.elabTerm suppliedCarrier none (catchExPostpone := false))
  unless carrierProof.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeInputCarrierHEq075 &&
      carrierProof.getAppArgs.size == 8 do
    throwError "Native078 requires only passed genuine input-carrier075 certificate."
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData &&
        carrierProof.getAppArgs[i]!.consumeMData.equal source.getAppArgs[i]!.consumeMData do
      throwError "Native078 refuses changed original source/native/carrier argument vector."
  let carrierType ← phiNativeNoRecovery025 (← whnf (← inferType carrierProof))
  let some (_, carrierLeft, _, carrierRight) := carrierType.consumeMData.headBeta.heq?
    | throwError "Native078 requires exact original carrier HEq4."
  unless carrierLeft.consumeMData.equal sourceCarrier.consumeMData &&
      carrierRight.consumeMData.equal nativeCarrier.consumeMData do
    throwError "Native078 carrier certificate does not join exact original point/E carrier vectors."
  let reverseCarrier ← mkHEqSymm carrierProof
  let leftReverse ← mkHEqSymm leftProof
  let rightReverse ← mkHEqSymm rightProof
  let desiredType := mkAppN (mkConst ``Eq [← getLevel nativeCarrier])
    #[nativeCarrier, la[5]!, ra[5]!]
  let (typeHEq, state) ←
    (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.structuralHEq
      sourceType desiredType 96 #[] "full142").run
        { pairs := #[(sourceCarrier, nativeCarrier, carrierProof),
          (nativeCarrier, sourceCarrier, reverseCarrier),
          (leftSource, leftNative, leftProof), (leftNative, leftSource, leftReverse),
          (rightSource, rightNative, rightProof), (rightNative, rightSource, rightReverse)] }
  let typeEq ← mkEqOfHEq typeHEq
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``Eq.mp [Level.zero]) #[sourceType, desiredType, typeEq, source])
  let actualType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  unless actualType.consumeMData.headBeta.equal desiredType.consumeMData.headBeta do
    throwError "Native078 ordinary point carrier transport changed exact original carrier/points."
  logInfo m!"Native079 genuine input Eq transport consumes passed075 carrier and two ordinary exact endpoint HEqs: native={state.wrapperLeaves}, proof={state.proofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}."
  return proof

end

private lemma actualOriginalGlobalPhiNativePointNativeInputOwn078
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_point_retag078%
      (actualOriginalGlobalPhiNativeDifferentialPointOwn061 p hp P hP s)
      with_native (phiNativeOriginalDifferentialPointLiftProp075 p hp P hP s)
      using_carrier (actualOriginalGlobalPhiNativeInputCarrierHEq075 p hp P hP s)
      using_left (actualOriginalGlobalPhiNativePointInputLeftHEq079 p hp P hP s)
      using_right (actualOriginalGlobalPhiNativePointInputRightHEq079 p hp P hP s)) :=
  phi_native_point_retag078%
      (actualOriginalGlobalPhiNativeDifferentialPointOwn061 p hp P hP s)
      with_native (phiNativeOriginalDifferentialPointLiftProp075 p hp P hP s)
      using_carrier (actualOriginalGlobalPhiNativeInputCarrierHEq075 p hp P hP s)
      using_left (actualOriginalGlobalPhiNativePointInputLeftHEq079 p hp P hP s)
      using_right (actualOriginalGlobalPhiNativePointInputRightHEq079 p hp P hP s)

meta section
open Lean Meta Elab Term

elab "phi_native_owned_point_lift078% " supplied:term " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativePointNativeInputOwn078 &&
      source.getAppArgs.size == 8 do
    throwError "Native078 requires only original certified point-input-own0788."
  let body ← phiNativeLiteralLiftBody078 nativeProp
  let (outputCarrier, nativeLeft, nativeRight, la, ra) ← phiNativeLiftBodyVectors078 body
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native078 refuses changed original point/native argument vectors."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (inputCarrier, inputLeft, inputRight) := sourceType.consumeMData.headBeta.eq?
    | throwError "Native078 requires exact certified native input Eq3."
  unless inputCarrier.consumeMData.equal la[1]!.consumeMData &&
      inputLeft.consumeMData.headBeta.equal la[5]!.consumeMData.headBeta &&
      inputRight.consumeMData.headBeta.equal ra[5]!.consumeMData.headBeta do
    throwError "Native078 refuses different original certified input carrier/point vectors."
  let evaluator ← withLocalDeclD `originalNativePoint inputCarrier fun pointValue =>
    mkLambdaFVars #[pointValue]
      (mkAppN nativeLeft.getAppFn (la.set! 5 pointValue))
  let evaluatorType ← phiNativeNoRecovery025 (← inferType evaluator)
  let .forallE _ domain codomain _ := evaluatorType.consumeMData
    | throwError "Native078 original evaluator did not retain its actual function type."
  unless domain.consumeMData.equal inputCarrier.consumeMData &&
      (codomain.instantiate1 inputLeft).consumeMData.headBeta.equal outputCarrier.consumeMData.headBeta do
    throwError "Native078 original evaluator changed exact input/output carriers."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``congrArg [← getLevel inputCarrier, ← getLevel outputCarrier])
      #[inputCarrier, outputCarrier, inputLeft, inputRight, evaluator, source])
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (actualCarrier, actualLeft, actualRight) := proofType.consumeMData.headBeta.eq?
    | throwError "Native078 ordinary owned congrArg did not return Eq3."
  unless actualCarrier.consumeMData.equal outputCarrier.consumeMData &&
      actualLeft.consumeMData.headBeta.equal nativeLeft &&
      actualRight.consumeMData.headBeta.equal nativeRight do
    throwError "Native078 ordinary congrArg changed original literal E-lift endpoints."
  logInfo "Native078 exact congrArg full vector lifts actual certified point input through original literal native E prefix; complete carrier/point/function/output guards retained."
  return proof

end

private lemma actualOriginalGlobalPhiNativePointNativeLiftOwn078
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_owned_point_lift078%
      (actualOriginalGlobalPhiNativePointNativeInputOwn078 p hp P hP s)
      with_native (phiNativeOriginalDifferentialPointLiftProp075 p hp P hP s)) :=
  phi_native_owned_point_lift078%
      (actualOriginalGlobalPhiNativePointNativeInputOwn078 p hp P hP s)
      with_native (phiNativeOriginalDifferentialPointLiftProp075 p hp P hP s)

meta section
open Lean Meta Elab Term Tactic

elab "phi_native_original_local_lift_exact078 " supplied:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← phiNativeNoRecovery025
      (← Term.elabTerm supplied none (catchExPostpone := false))
    unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativePointNativeLiftOwn078 &&
        source.getAppArgs.size == 8 do
      throwError "Native078 requires only original owned native E-lift0788."
    let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
    let target ← phiNativeNoRecovery025 (← goal.getType)
    let (_, sourceLeft, sourceRight, _, _) ← phiNativeLiftBodyVectors078 sourceType
    let (_, targetLeft, targetRight, _, _) ← phiNativeLiftBodyVectors078 target
    unless sourceLeft.getAppFn.equal targetLeft.getAppFn &&
        sourceRight.getAppFn.equal targetRight.getAppFn do
      throwError "Native078 refuses different original literal E coercion heads."
    let (typeHEq, state) ←
      (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.structuralHEq
        sourceType target 96 #[] "full142").run {}
    let typeEq ← mkEqOfHEq typeHEq
    let proof ← phiNativeNoRecovery025
      (mkAppN (mkConst ``Eq.mp [Level.zero]) #[sourceType, target, typeEq, source])
    let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
    let some (actualCarrier, actualLeft, actualRight) := proofType.consumeMData.headBeta.eq?
      | throwError "Native078 original local-header transport did not return Eq3."
    let some (targetCarrier, expectedLeft, expectedRight) := target.consumeMData.headBeta.eq?
      | throwError "Native078 original local header did not retain its literal Eq3 target."
    unless actualCarrier.consumeMData.equal targetCarrier.consumeMData &&
        actualLeft.consumeMData.equal expectedLeft.consumeMData &&
        actualRight.consumeMData.equal expectedRight.consumeMData do
      throwError "Native078 ordinary local-header transport changed original literal carrier/points."
    logInfo m!"Native078 original local-let header compatibility consumes ordinary owned E-lift: native={state.wrapperLeaves}, proof={state.proofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}."
    goal.assign proof
    replaceMainGoal []

end

private lemma actualOriginalGlobalPhiNativeDifferentialPointLiftLocal061
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let W := schemeRelativeDifferentials (toBase I)
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let cW := (actualPositiveTwistPullbackTensorIso I q W 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let Dg := actualGlobalClosedConormalDifferentialMap (toBase I) q
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      W (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      J (closedImmersionModule j) (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    let Etw := actualOriginalQuadraticConormalPointChartIso p hp P hP
    let x : RingHom.ker C.residue :=
      ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let E := actualAffineSchemeDifferentialPointFiberEquiv (k := K) C.residue
    E (G.map (Dg ≫ Et.hom ≫ Ebase.hom) (G.map cJ z)) =
    E (actualAffineDifferentialPointClass (k := K) C.residue x.1) := by
  intro C I R L q f j J T W G z cJ cW Dg Et Ebase Es Ej Etw x sx E
  phi_native_original_local_lift_exact078
    (actualOriginalGlobalPhiNativePointNativeLiftOwn078 p hp P hP s)

meta section
open Lean Meta Elab Term

elab "phi_native_differential_point_lift_body061% " supplied:term : term => do
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  phiNativeOpenContractionLocalLets058 source
    ``actualOriginalGlobalPhiNativeDifferentialPointLiftLocal061

end

private lemma actualOriginalGlobalPhiNativeDifferentialPointLiftOwn061
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_differential_point_lift_body061%
      (actualOriginalGlobalPhiNativeDifferentialPointLiftLocal061 p hp P hP s)) :=
  phi_native_differential_point_lift_body061%
    (actualOriginalGlobalPhiNativeDifferentialPointLiftLocal061 p hp P hP s)

/-- The ordinary point-class action followed by the SAME universal residue
 derivation; the tower is obtained from the actual base-map compatibility. -/
private lemma phiNativeDifferentialPointEvaluation080
    {K R L : Type u} [Field K] [CommRing R] [Field L]
    [Algebra K R] [Algebra K L]
    (rho : R →+* L)
    (base : rho.comp (algebraMap K R) = algebraMap K L) (r : R) :
    letI : Algebra R L := rho.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun base c).symm)
    actualAffineSchemeDifferentialPointFiberEquiv (k := K) rho
      (actualAffineDifferentialPointClass (k := K) rho r) =
        actualResidueDifferentialDerivation (K := K) (R := R) (L := L) r := by
  letI : Algebra R L := rho.toAlgebra
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun base c).symm)
  calc
    _ = (1 : L) ⊗ₜ[R] KaehlerDifferential.D K R r :=
      actualAffineDifferentialPointFiberEquiv_pointClass (k := K) rho r
    _ = _ := (actualResidueDifferentialDerivation_apply (K := K) (R := R) (L := L) r).symm

private lemma actualOriginalGlobalPhiNativePointEvaluationLocal080
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    actualAffineSchemeDifferentialPointFiberEquiv (k := K) C.residue
      (actualAffineDifferentialPointClass (k := K) C.residue
        (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s)) =
      actualResidueDifferentialDerivation (K := K) (R := R) (L := L)
        (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s) := by
  intro C I R L
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
  letI : SMul K R := aK.toSMul
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun C.base c).symm)
  exact phiNativeDifferentialPointEvaluation080 (K := K) (R := R) (L := L)
    C.residue C.base (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s)

meta section
open Lean Meta Elab Term

/-- Eliminate ONLY the four stored top chart lets of the original point
 evaluation certificate. No point, map, scalar or dictionary subtree is rewritten. -/
elab "phi_native_point_evaluation_body080% " supplied:term : term => do
  let source ← phiNativeNoRecovery025
    (← Term.elabTerm supplied none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativePointEvaluationLocal080 &&
      source.getAppArgs.size == 8 do
    throwError "Native080 requires only the original point-evaluation-local0808 certificate."
  let mut body ← phiNativeNoRecovery025 (← inferType source)
  let mut eliminated : Nat := 0
  for _ in [:4] do
    match body.consumeMData with
    | .letE _ _ value innerBody _ =>
      body := (innerBody.instantiate1 value).consumeMData.headBeta
      eliminated := eliminated + 1
    | _ => pure ()
  unless eliminated == 4 do
    throwError "Native080 requires exactly the original four top chart lets."
  let closedBody ← phiNativeNoRecovery025 body
  unless closedBody.consumeMData.headBeta.eq?.isSome do
    throwError "Native080 original four-let evaluation did not retain literal Eq3."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``id [Level.zero]) #[closedBody, source])
  let proofType ← phiNativeNoRecovery025 (← inferType proof)
  unless proofType.consumeMData.headBeta.equal closedBody.consumeMData.headBeta do
    throwError "Native080 ordinary id changed actual original point-evaluation proposition."
  logInfo "Native080 ordinary id retains passed original point-evaluation proof after exactly four top chart lets; scalar dictionaries and literal point/derivation endpoints unchanged."
  return proof

end

private lemma actualOriginalGlobalPhiNativePointEvaluationOwn080
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_point_evaluation_body080%
      (actualOriginalGlobalPhiNativePointEvaluationLocal080 p hp P hP s)) :=
  phi_native_point_evaluation_body080%
    (actualOriginalGlobalPhiNativePointEvaluationLocal080 p hp P hP s)

/-- Evaluate the SAME original ker section projection used by the public
calculation. The projection equals its actual native restriction by construction;
no section or differential action is replaced. -/
private lemma actualOriginalGlobalPhiNativeSectionPointEvaluationLocal081
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let x : RingHom.ker C.residue :=
      ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
    let E := actualAffineSchemeDifferentialPointFiberEquiv (k := K) C.residue
    E (actualAffineDifferentialPointClass (k := K) C.residue x.1) =
      actualResidueDifferentialDerivation (K := K) (R := R) (L := L)
        (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s) := by
  intro C I R L x E
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
  letI : SMul K R := aK.toSMul
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun C.base c).symm)
  have hValue : x.1 = actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s := rfl
  rw [hValue]
  exact phiNativeDifferentialPointEvaluation080 (K := K) (R := R) (L := L)
    C.residue C.base (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s)

meta section
open Lean Meta Elab Term

/-- Carry the actual x/E section certificate through ONLY its six original top
lets. In particular, leave the Subtype.val endpoint literally present. -/
elab "phi_native_section_point_evaluation_body081% " supplied:term : term => do
  let source ← phiNativeNoRecovery025
    (← Term.elabTerm supplied none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeSectionPointEvaluationLocal081 &&
      source.getAppArgs.size == 8 do
    throwError "Native081 requires only original section-evaluation-local0818."
  let mut body ← phiNativeNoRecovery025 (← inferType source)
  let mut eliminated : Nat := 0
  for _ in [:6] do
    match body.consumeMData with
    | .letE _ _ value innerBody _ =>
      body := (innerBody.instantiate1 value).consumeMData.headBeta
      eliminated := eliminated + 1
    | _ => pure ()
  unless eliminated == 6 do
    throwError "Native081 requires exactly original C/I/R/L/x/E top lets."
  let closedBody ← phiNativeNoRecovery025 body
  unless closedBody.consumeMData.headBeta.eq?.isSome do
    throwError "Native081 original section evaluation did not retain literal Eq3."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``id [Level.zero]) #[closedBody, source])
  let proofType ← phiNativeNoRecovery025 (← inferType proof)
  unless proofType.consumeMData.headBeta.equal closedBody.consumeMData.headBeta do
    throwError "Native081 ordinary id changed exact original section-evaluation proposition."
  logInfo "Native081 ordinary id retains original ker section projection and E after exactly six top lets; no Subtype.val or nativeRestriction subtree normalization."
  return proof

end

private lemma actualOriginalGlobalPhiNativeSectionPointEvaluationOwn081
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_section_point_evaluation_body081%
      (actualOriginalGlobalPhiNativeSectionPointEvaluationLocal081 p hp P hP s)) :=
  phi_native_section_point_evaluation_body081%
    (actualOriginalGlobalPhiNativeSectionPointEvaluationLocal081 p hp P hP s)

/-- Ordinary equality transitivity only; no geometric compatibility is
part of the assembly proof. -/
private lemma phiNativeEqFiveLinks082 {alpha : Sort u}
    (x0 x1 x2 x3 x4 x5 : alpha)
    (h01 : x0 = x1) (h12 : x1 = x2) (h23 : x2 = x3)
    (h34 : x3 = x4) (h45 : x4 = x5) : x0 = x5 :=
  h01.trans (h12.trans (h23.trans (h34.trans h45)))

/-- Literal original coefficient links under one shared original chart
context. Explicit Eq carrier is the SAME original residue tensor carrier in all
five cases; fixed numerals merely select a link, never assert it. -/
private def phiNativeOriginalCoefficientStageProp082
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) (stage : Nat) : Prop :=
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let J := closedImmersionModule q
    let T := positiveSheafOfModules (grading I) 2
    let W := schemeRelativeDifferentials (toBase I)
    let G := moduleSpecΓFunctor (R := .of L)
    let z := actualModulePointSectionClass q (closedImmersionIdealTwist q T)
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s)
    let cJ := (actualPositiveTwistPullbackTensorIso I q J 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj J)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let cW := (actualPositiveTwistPullbackTensorIso I q W 2).hom ≫
      (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj W)
        ((Scheme.Modules.pullback q).obj T)
        (actualOriginalPositiveTwoPointTrivialization p hp P hP)).hom
    let Dg := actualGlobalClosedConormalDifferentialMap (toBase I) q
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      W (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      J (closedImmersionModule j) (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Ej := actualOriginalUntwistedIdealPointChartIso p hp P hP
    let Etw := actualOriginalQuadraticConormalPointChartIso p hp P hP
    let x : RingHom.ker C.residue :=
      ⟨actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s,
        actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s⟩
    let sx := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom C.residue x
    let E := actualAffineSchemeDifferentialPointFiberEquiv (k := K) C.residue
    match stage with
    | 0 => @Eq (L ⊗[R] KaehlerDifferential K R)
        (actualOriginalPositiveTwoContractedNativeDifferentialMap p hp P hP
          (actualOriginalGlobalCanonicalQuadraticPhi p hp P s))
        (E (G.map (Et.hom ≫ Ebase.hom)
          (G.map cW (actualOriginalGlobalCanonicalQuadraticPhi p hp P s))))
    | 1 => @Eq (L ⊗[R] KaehlerDifferential K R)
        (E (G.map (Et.hom ≫ Ebase.hom)
          (G.map cW (actualOriginalGlobalCanonicalQuadraticPhi p hp P s))))
        (E (G.map (Et.hom ≫ Ebase.hom) (G.map Dg (G.map cJ z))))
    | 2 => @Eq (L ⊗[R] KaehlerDifferential K R)
        (E (G.map (Et.hom ≫ Ebase.hom) (G.map Dg (G.map cJ z))))
        (E (G.map (Dg ≫ Et.hom ≫ Ebase.hom) (G.map cJ z)))
    | 3 => @Eq (L ⊗[R] KaehlerDifferential K R)
        (E (G.map (Dg ≫ Et.hom ≫ Ebase.hom) (G.map cJ z)))
        (E (actualAffineDifferentialPointClass (k := K) C.residue x.1))
    | 4 => @Eq (L ⊗[R] KaehlerDifferential K R)
        (E (actualAffineDifferentialPointClass (k := K) C.residue x.1))
        (actualResidueDifferentialDerivation (K := K) (R := R) (L := L)
          (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s))
    | _ => False

meta section
open Lean Meta Elab Term

/-- Read ONLY the passed original stage factory's coefficient endpoint and
open ONLY the actual original map definition and its one chart-choice let.
The resulting producer argument vector is taken from the definition VALUE. -/
private def phiNativeOriginalProducerVector083 (nativeProp : Expr) :
    TermElabM (Expr × Expr) := do
  unless nativeProp.getAppFn.isConstOf ``phiNativeOriginalCoefficientStageProp082 &&
      nativeProp.getAppArgs.size == 9 do
    throwError "Native083 requires only exact original coefficient stage factory/nine-vector."
  -- The surface numeral can be an OfNat application. Read ONLY its stored
  -- Nat argument to whnf; the factory/point/map/proof vectors stay unchanged.
  let storedStage ← phiNativeNoRecovery025 (← whnf nativeProp.getAppArgs[8]!)
  let .lit (.natVal stage) := storedStage.consumeMData
    | throwError "Native083 requires literal original stage0 after only Nat-argument whnf."
  unless stage == 0 do
    throwError "Native083 refuses a different original coefficient stage."
  let some unfolded ← delta? nativeProp (fun n => n == ``phiNativeOriginalCoefficientStageProp082)
    | throwError "Native083 could not open exact original shared stage factory."
  let mut body := unfolded.consumeMData.headBeta
  let mut eliminated : Nat := 0
  for _ in [:23] do
    match body with
    | .letE _ _ value innerBody _ =>
      body := (innerBody.instantiate1 value).consumeMData.headBeta
      eliminated := eliminated + 1
    | _ => pure ()
  unless eliminated == 23 do
    throwError "Native083 requires exactly original23 stage context lets."
  let closedBody ← phiNativeNoRecovery025 (← whnf body)
  let some (_, nativePoint, _) := closedBody.consumeMData.headBeta.eq?
    | throwError "Native083 original stage0 did not expose literal Eq3."
  let nativePoint := nativePoint.consumeMData.headBeta
  let pointArgs := nativePoint.getAppArgs
  unless nativePoint.getAppFn.isConstOf ``DFunLike.coe && pointArgs.size == 6 do
    throwError "Native083 requires original coefficient DFunLike.coercion6."
  let nativeMap := pointArgs[4]!.consumeMData.headBeta
  let mapArgs := nativeMap.getAppArgs
  unless nativeMap.getAppFn.isConstOf ``actualOriginalPositiveTwoContractedNativeDifferentialMap &&
      mapArgs.size == 7 do
    throwError "Native083 requires only actual original contracted native map/seven-vector."
  for i in [:7] do
    unless mapArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native083 refuses changed original coefficient map argument vector."
  let some mapValue ← delta? nativeMap
      (fun n => n == ``actualOriginalPositiveTwoContractedNativeDifferentialMap)
    | throwError "Native083 could not open only the original native map definition."
  let .defnInfo declaration ← getConstInfo ``actualOriginalPositiveTwoContractedNativeDifferentialMap
    | throwError "Native086 requires the exact installed original native map definition VALUE."
  logInfo m!"Native086 entire installed original NativeMap declaration VALUE: {declaration.value}"
  logInfo m!"Native086 exact applied original NativeMap delta VALUE: {mapValue}"
  let mut storedValue ← phiNativeNoRecovery025 mapValue.consumeMData.headBeta
  let mut chartLets : Nat := 0
  let mut wrappers : Nat := 0
  -- Same existing eight-step normalization ceiling, confined to id and the
  -- single exact original C let. No other definition/let/fvar is unfolded.
  for i in [:8] do
    logInfo m!"Native086 stored VALUE spine[{i}]: {phiNativeJoinHead070 storedValue}."
    if storedValue.getAppFn.isConstOf ``id then
      let args := storedValue.getAppArgs
      let .const _ levels := storedValue.getAppFn
        | throwError "Native086 expected actual id constant universe vector."
      unless args.size == 2 && levels.length == 1 do
        throwError "Native086 refuses a different identity wrapper arity/universe vector."
      logInfo m!"Native086 exact id wrapper type argument: {args[0]!}; stored payload head: {phiNativeJoinHead070 args[1]!}."
      let some opened ← delta? storedValue (fun n => n == ``id)
        | throwError "Native086 could not open only exact id wrapper."
      let opened ← phiNativeNoRecovery025 opened.consumeMData.headBeta
      unless opened.consumeMData.equal args[1]!.consumeMData.headBeta do
        throwError "Native086 identity unfolding changed its exact stored VALUE payload."
      storedValue := opened
      wrappers := wrappers + 1
    else
      match storedValue with
      | .letE _ _ chartValue mapBody _ =>
        unless chartLets == 0 &&
            chartValue.getAppFn.isConstOf ``actualOriginalQuarticCotangentChartChoice &&
            chartValue.getAppArgs.size == 7 do
          throwError "Native086 permits only ONE exact original C chart-choice let."
        for j in [:7] do
          unless chartValue.getAppArgs[j]!.consumeMData.equal mapArgs[j]!.consumeMData do
            throwError "Native086 refuses changed original retained chart-choice arguments."
        storedValue ← phiNativeNoRecovery025
          (mapBody.instantiate1 chartValue).consumeMData.headBeta
        chartLets := chartLets + 1
      | _ => break
  let producer := storedValue
  logInfo m!"Native086 original VALUE reader: id wrappers={wrappers}, chart lets={chartLets}; final exact stored head={phiNativeJoinHead070 producer}."
  unless producer.getAppFn.isConstOf ``actualCubicPositiveTwoChartContractedNativeDifferentialMap &&
      producer.getAppArgs.size == 11 do
    logInfo m!"Native083 actual original producer head={producer.getAppFn}, arity={producer.getAppArgs.size}."
    throwError "Native083 original map definition does not give exact shared cubic producer/eleven-vector."
  let pa := producer.getAppArgs
  for (producerIndex, originalIndex) in #[(0, 0), (2, 1), (4, 3), (5, 4)] do
    unless pa[producerIndex]!.consumeMData.equal mapArgs[originalIndex]!.consumeMData do
      throwError "Native085 original definition producer changed K/FieldK/p/hp argument vector."
  return (nativeMap, producer)

/-- Separate ordinary conversion of the original map VALUE, before any
point evaluation, Functor.map_comp, or native geometric endpoint comparison. -/
elab "phi_native_original_producer_heq083% " nativeProp:term : term => do
  let nativeProp ← phiNativeNoRecovery025
    (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let (nativeMap, producer) ← phiNativeOriginalProducerVector083 nativeProp
  let desiredType ← mkHEq nativeMap producer
  let reflexive ← mkHEqRefl nativeMap
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``id [Level.zero]) #[desiredType, reflexive])
  let proofType ← phiNativeNoRecovery025 (← inferType proof)
  let some (_, actualNative, _, actualProducer) := proofType.consumeMData.headBeta.heq?
    | throwError "Native083 original map value identity did not return HEq4."
  unless actualNative.consumeMData.equal nativeMap.consumeMData &&
      actualProducer.consumeMData.equal producer.consumeMData do
    throwError "Native083 original definition identity changed exact stored map values."
  logInfo "Native083 ordinary original map VALUE HEq opens only original definition/seven arguments and exact one chart-choice let; producer eleven-vector retained unchanged."
  return proof

/-- Existing formula law, applied ONLY to the original definition's exact
producer arguments/universes; no native expected target is supplied. -/
elab "phi_native_original_producer_formula083% " nativeProp:term : term => do
  let nativeProp ← phiNativeNoRecovery025
    (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let (_, producer) ← phiNativeOriginalProducerVector083 nativeProp
  let .const _ levels := producer.getAppFn
    | throwError "Native083 requires stored producer universe vector."
  let producerInfo ← getConstInfo ``actualCubicPositiveTwoChartContractedNativeDifferentialMap
  let lawInfo ← getConstInfo ``actualCubicPositiveTwoChartContractedNativeDifferentialMap_eq_formula
  unless levels.length == 1 && producerInfo.levelParams.length == 1 &&
      lawInfo.levelParams.length == 1 do
    throwError "Native083 requires exactly the original producer/law single universe."
  let canonical := [Level.param `phiNativeProducerCanonical083]
  let mut producerType := producerInfo.type.instantiateLevelParams producerInfo.levelParams canonical
  let mut lawType := lawInfo.type.instantiateLevelParams lawInfo.levelParams canonical
  for i in [:11] do
    let .forallE _ producerDomain producerBody producerBinder := producerType
      | throwError "Native083 missing exact producer prefix binder."
    let .forallE _ lawDomain lawBody lawBinder := lawType
      | throwError "Native083 missing exact formula prefix binder."
    unless producerDomain.consumeMData.equal lawDomain.consumeMData &&
        producerBinder == lawBinder do
      logInfo m!"Native083 producer/formula prefix{i}: producer={producerDomain}; law={lawDomain}."
      throwError "Native083 refuses different stored producer/formula prefix domains or binder kinds."
    producerType := producerBody
    lawType := lawBody
  let law ← phiNativeNoRecovery025
    (mkAppN (mkConst ``actualCubicPositiveTwoChartContractedNativeDifferentialMap_eq_formula levels)
      producer.getAppArgs)
  let mut body ← phiNativeNoRecovery025 (← inferType law)
  let mut eliminated : Nat := 0
  for _ in [:9] do
    match body.consumeMData with
    | .letE _ _ value innerBody _ =>
      body := (innerBody.instantiate1 value).consumeMData.headBeta
      eliminated := eliminated + 1
    | _ => pure ()
  unless eliminated == 9 do
    throwError "Native083 requires exactly existing formula's nine original I/R/f/j/W/T/Et/Ebase/c lets."
  let closedBody ← phiNativeNoRecovery025 body
  let some (_, formulaLeft, _) := closedBody.consumeMData.headBeta.eq?
    | throwError "Native083 actual existing formula did not expose Eq3."
  unless formulaLeft.consumeMData.equal producer.consumeMData do
    throwError "Native083 formula does not retain exact original definition producer on its left."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``id [Level.zero]) #[closedBody, law])
  let proofType ← phiNativeNoRecovery025 (← inferType proof)
  unless proofType.consumeMData.headBeta.equal closedBody.consumeMData.headBeta do
    throwError "Native083 ordinary formula id changed exact original map formula."
  logInfo "Native083 existing generic formula emitted from all eleven original stored producer arguments/universes and exact prefix guard; only nine top formula lets opened with ordinary id."
  return proof

/-- Metadata diagnostic only. A successful True proves no map equality. -/
elab "phi_native_original_value_diagnostic086% " nativeProp:term : term => do
  let nativeProp ← phiNativeNoRecovery025
    (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let (nativeMap, producer) ← phiNativeOriginalProducerVector083 nativeProp
  logInfo m!"Native086 original stored native-map vector: {nativeMap}"
  for i in [:producer.getAppArgs.size] do
    logInfo m!"Native086 exact producer argument[{i}]: head={phiNativeJoinHead070 producer.getAppArgs[i]!}; value={producer.getAppArgs[i]!}."
  return mkConst ``True.intro

end

private lemma actualOriginalGlobalPhiNativeOriginalProducerHEq083
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_producer_heq083%
      (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_producer_heq083%
    (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

private lemma actualOriginalGlobalPhiNativeOriginalProducerFormulaOwn083
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_producer_formula083%
      (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_producer_formula083%
    (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

/-- Read only the literal original Stage0 proposition, preserving all map,
point and scalar subexpressions. No native endpoint equality is assumed. -/
private def phiNativeCoefficientBody087 (nativeProp : Expr) : TermElabM Expr := do
  unless nativeProp.getAppFn.isConstOf ``phiNativeOriginalCoefficientStageProp082 &&
      nativeProp.getAppArgs.size == 9 do
    throwError "Native087 requires exact original coefficient stage factory/nine-vector."
  let storedStage ← phiNativeNoRecovery025 (← whnf nativeProp.getAppArgs[8]!)
  let .lit (.natVal stage) := storedStage.consumeMData
    | throwError "Native087 requires literal original stage numeral."
  unless stage == 0 do
    throwError "Native087 requires only original coefficient stage0."
  let some unfolded ← delta? nativeProp (fun n => n == ``phiNativeOriginalCoefficientStageProp082)
    | throwError "Native087 could not open exact original coefficient factory."
  let mut body := unfolded.consumeMData.headBeta
  let mut eliminated : Nat := 0
  for _ in [:23] do
    match body with
    | .letE _ _ value innerBody _ =>
      body := (innerBody.instantiate1 value).consumeMData.headBeta
      eliminated := eliminated + 1
    | _ => pure ()
  unless eliminated == 23 do
    throwError "Native087 requires exactly original23 coefficient context lets."
  let closedBody ← phiNativeNoRecovery025 (← whnf body)
  unless closedBody.consumeMData.headBeta.eq?.isSome do
    throwError "Native087 exact original stage0 did not expose Eq3."
  return closedBody

end

meta section
open Lean Meta Elab Term

/-- Read only the two actually diagnosed original intermediate objects.
Both mapped morphisms and all original category/G/Phi arguments are retained. -/
private def phiNativeOriginalMiddleObjects090 (nativeProp : Expr) :
    TermElabM (Expr × Expr) := do
  let body ← phiNativeCoefficientBody087 nativeProp
  let some (_, coefficient, nestedPoint) := body.consumeMData.headBeta.eq?
    | throwError "Native090 requires exact original Stage0 body."
  let nestedPoint := nestedPoint.consumeMData.headBeta
  let ea := nestedPoint.getAppArgs
  unless nestedPoint.getAppFn.isConstOf ``DFunLike.coe && ea.size == 6 do
    throwError "Native090 requires original E.coercion6."
  let outer ← phiNativePointVectors033 ea[5]!
  let inner ← phiNativePointVectors033 outer.coeArgs[5]!
  for i in [:5] do
    unless outer.mapArgs[i]!.consumeMData.equal inner.mapArgs[i]!.consumeMData do
      throwError "Native090 refuses changed original category/functor prefix."
  let coefficient := coefficient.consumeMData.headBeta
  unless coefficient.getAppFn.isConstOf ``DFunLike.coe && coefficient.getAppArgs.size == 6 &&
      coefficient.getAppArgs[5]!.consumeMData.equal inner.coeArgs[5]!.consumeMData do
    throwError "Native090 refuses changed original Phi."
  return (inner.mapArgs[6]!, outer.mapArgs[5]!)

/-- Separate equality of the two actual intermediate object TYPES. The
existing ordinary category bridge is a certified cache leaf, not a substitute
for either actual type; every further step uses the unchanged bounded engine. -/
elab "phi_native_original_middle_type090% " supplied:term
    " with_native " nativeProp:term : term => do
  let seed ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  unless seed.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeAssociationCategoryEq022 &&
      seed.getAppArgs.size == 8 do
    throwError "Native090 requires only passed exact original category Eq022."
  let (originalTarget, originalSource) ← phiNativeOriginalMiddleObjects090 nativeProp
  for i in [:8] do
    unless seed.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native090 refuses a category seed from different original arguments."
  let targetType ← phiNativeNoRecovery025 (← inferType originalTarget)
  let sourceType ← phiNativeNoRecovery025 (← inferType originalSource)
  let targetSort ← phiNativeNoRecovery025 (← inferType targetType)
  let sourceSort ← phiNativeNoRecovery025 (← inferType sourceType)
  unless targetSort.consumeMData.equal sourceSort.consumeMData do
    throwError "Native090 actual intermediate object type universes differ."
  let seedType ← phiNativeNoRecovery025 (← whnf (← inferType seed))
  let some (_, seedLeft, seedRight) := seedType.consumeMData.headBeta.eq?
    | throwError "Native090 existing category certificate is not Eq3."
  let seedHEq ← phiNativeNoRecovery025 (← mkHEqOfEq seed)
  let seedReverse ← phiNativeNoRecovery025 (← mkHEqSymm seedHEq)
  let (heq, state) ←
    (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.structuralHEq
      targetType sourceType 96 #[] "full142").run
        { pairs := #[(seedLeft, seedRight, seedHEq), (seedRight, seedLeft, seedReverse)] }
  let heq ← phiNativeNoRecovery025 heq
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``eq_of_heq [← getLevel targetSort])
      #[targetSort, targetType, sourceType, heq])
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (actualSort, actualTargetType, actualSourceType) := proofType.consumeMData.headBeta.eq?
    | throwError "Native090 actual intermediate type certificate is not Eq3."
  unless actualSort.consumeMData.equal targetSort.consumeMData &&
      actualTargetType.consumeMData.equal targetType.consumeMData &&
      actualSourceType.consumeMData.equal sourceType.consumeMData do
    throwError "Native090 type certificate changed original intermediate object types."
  logInfo m!"Native090 original middle TYPE compatibility: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}; exact original type endpoints guarded, existing category022 leaf retained."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalMiddleTypeEqOwn090
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_middle_type090%
      (actualOriginalGlobalPhiNativeAssociationCategoryEq022 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_middle_type090%
    (actualOriginalGlobalPhiNativeAssociationCategoryEq022 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

/-- Independently certify the literal original intermediate OBJECTS across
their separately proved type equality. No f/g or functor value is replaced. -/
elab "phi_native_original_middle_object090% " supplied:term
    " with_native " nativeProp:term : term => do
  let seed ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  unless seed.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalMiddleTypeEqOwn090 &&
      seed.getAppArgs.size == 8 do
    throwError "Native090 requires only exact checked middle type Eq090."
  let (originalTarget, originalSource) ← phiNativeOriginalMiddleObjects090 nativeProp
  for i in [:8] do
    unless seed.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native090 refuses type equality on different original arguments."
  let targetType ← phiNativeNoRecovery025 (← inferType originalTarget)
  let sourceType ← phiNativeNoRecovery025 (← inferType originalSource)
  let seedType ← phiNativeNoRecovery025 (← whnf (← inferType seed))
  let some (_, seedLeft, seedRight) := seedType.consumeMData.headBeta.eq?
    | throwError "Native090 requires actual original intermediate type Eq3."
  unless seedLeft.consumeMData.equal targetType.consumeMData &&
      seedRight.consumeMData.equal sourceType.consumeMData do
    throwError "Native090 middle type certificate does not raw join these exact object types."
  let seedHEq ← phiNativeNoRecovery025 (← mkHEqOfEq seed)
  let seedReverse ← phiNativeNoRecovery025 (← mkHEqSymm seedHEq)
  let (proof, state) ←
    (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.structuralHEq
      originalTarget originalSource 96 #[] "full142").run
        { pairs := #[(seedLeft, seedRight, seedHEq), (seedRight, seedLeft, seedReverse)] }
  let proof ← phiNativeNoRecovery025 proof
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (actualTargetType, actualTarget, actualSourceType, actualSource) :=
      proofType.consumeMData.headBeta.heq?
    | throwError "Native090 original middle object certificate is not HEq4."
  unless actualTarget.consumeMData.equal originalTarget.consumeMData &&
      actualSource.consumeMData.equal originalSource.consumeMData &&
      actualTargetType.consumeMData.equal targetType.consumeMData &&
      actualSourceType.consumeMData.equal sourceType.consumeMData do
    throwError "Native090 object certificate changed literal original object/type endpoints."
  logInfo m!"Native090 original middle OBJECT compatibility: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}; literal original f/g intermediate objects/type vectors retained, no application guard relaxed."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalMiddleObjectHEqOwn090
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_middle_object090%
      (actualOriginalGlobalPhiNativeOriginalMiddleTypeEqOwn090 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_middle_object090%
    (actualOriginalGlobalPhiNativeOriginalMiddleTypeEqOwn090 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

private structure PhiNativeCommonCategoryVectors093 where
  source : Expr
  sourceProposition : Expr
  targetType : Expr
  targetObject : Expr
  sourceType : Expr
  sourceObject : Expr
  commonCategory : Expr

/-- Exact actual090 HEq values and the common map category diagnosed092.
Both original object values must already raw join; their TYPES remain literal. -/
private def phiNativeOriginalCommonCategoryVectors093 (source nativeProp : Expr) :
    TermElabM PhiNativeCommonCategoryVectors093 := do
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalMiddleObjectHEqOwn090 &&
      source.getAppArgs.size == 8 do
    throwError "Native093 requires only passed exact original object HEq090."
  let (expectedTarget, expectedSource) ← phiNativeOriginalMiddleObjects090 nativeProp
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native093 refuses changed original category/object arguments."
  let body ← phiNativeCoefficientBody087 nativeProp
  let some (_, _, nestedPoint) := body.consumeMData.headBeta.eq?
    | throwError "Native093 requires original Stage0 body."
  let ea := nestedPoint.consumeMData.headBeta.getAppArgs
  unless nestedPoint.consumeMData.headBeta.getAppFn.isConstOf ``DFunLike.coe && ea.size == 6 do
    throwError "Native093 requires original E.coercion6."
  let outer ← phiNativePointVectors033 ea[5]!
  let inner ← phiNativePointVectors033 outer.coeArgs[5]!
  let sourceProposition ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (targetType, targetObject, sourceType, sourceObject) :=
      sourceProposition.consumeMData.headBeta.heq?
    | throwError "Native093 requires actual source HEq4."
  unless targetObject.consumeMData.equal expectedTarget.consumeMData &&
      sourceObject.consumeMData.equal expectedSource.consumeMData &&
      inner.mapArgs[0]!.consumeMData.equal outer.mapArgs[0]!.consumeMData do
    throwError "Native093 actual original object values/common map categories do not raw join."
  return ⟨source, sourceProposition, targetType, targetObject,
    sourceType, sourceObject, outer.mapArgs[0]!⟩

end

meta section
open Lean Meta Elab Term

/-- Exact single ring in actual source TYPE and inner single ring of the
actual common double bundle. Only the diagnosed carrier spine is inspected. -/
private def phiNativeOriginalRingPair094 (source nativeProp : Expr) :
    TermElabM (Expr × Expr) := do
  let v ← phiNativeOriginalCommonCategoryVectors093 source nativeProp
  let sourceCategory := v.sourceType.consumeMData.headBeta
  let commonCategory := v.commonCategory.consumeMData.headBeta
  unless sourceCategory.getAppFn.isConstOf ``AlgebraicGeometry.Scheme.Modules &&
      sourceCategory.getAppFn.equal commonCategory.getAppFn &&
      sourceCategory.getAppArgs.size == 1 && commonCategory.getAppArgs.size == 1 do
    throwError "Native094 requires diagnosed original Modules one-vector categories."
  let sourceSpec := sourceCategory.getAppArgs[0]!.consumeMData.headBeta
  let commonSpec := commonCategory.getAppArgs[0]!.consumeMData.headBeta
  unless sourceSpec.getAppFn.isConstOf ``AlgebraicGeometry.Spec &&
      sourceSpec.getAppFn.equal commonSpec.getAppFn &&
      sourceSpec.getAppArgs.size == 1 && commonSpec.getAppArgs.size == 1 do
    throwError "Native094 requires diagnosed original Spec ring vectors."
  let sourceRing := sourceSpec.getAppArgs[0]!
  let doubleRing := commonSpec.getAppArgs[0]!.consumeMData.headBeta
  unless sourceRing.getAppFn.isConstOf ``CommRingCat.of && sourceRing.getAppArgs.size == 2 &&
      doubleRing.getAppFn.isConstOf ``CommRingCat.of && doubleRing.getAppArgs.size == 2 do
    throwError "Native094 requires original source single/common double rings."
  let doubleCarrier := doubleRing.getAppArgs[0]!.consumeMData.headBeta
  unless doubleCarrier.getAppFn.isConstOf ``CommRingCat.carrier && doubleCarrier.getAppArgs.size == 1 do
    throwError "Native094 refuses a different original double-ring carrier spine."
  let innerRing := doubleCarrier.getAppArgs[0]!
  unless innerRing.getAppFn.isConstOf ``CommRingCat.of && innerRing.getAppArgs.size == 2 &&
      innerRing.getAppFn.equal sourceRing.getAppFn &&
      innerRing.getAppArgs[0]!.consumeMData.equal sourceRing.getAppArgs[0]!.consumeMData do
    throwError "Native094 actual original single rings have different carriers/universes."
  return (sourceRing, innerRing)

end

meta section
open Lean Meta Elab Term

/-- Genuine heterogeneous identity of the exact original projections. Both
actual OWN instance TYPES are retained, including the reported forget-object
carrier on the right; homogeneous Eq is neither assumed nor requested. -/
elab "phi_native_original_projection_heq095% " supplied:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let (sourceRing, innerRing) ← phiNativeOriginalRingPair094 source nativeProp
  let sourceProjection := sourceRing.getAppArgs[1]!
  let targetProjection := innerRing.getAppArgs[1]!
  unless sourceProjection.getAppFn.isConstOf ``Field.toCommRing && sourceProjection.getAppArgs.size == 2 &&
      targetProjection.getAppFn.isConstOf ``CommRingCat.instCommRingObjForgetRingHomCarrier &&
      targetProjection.getAppArgs.size == 1 do
    throwError "Native095 refuses a different original projection diamond."
  let sourceType ← phiNativeNoRecovery025 (← inferType sourceProjection)
  let targetType ← phiNativeNoRecovery025 (← inferType targetProjection)
  let sourceLevel ← getLevel sourceType
  let targetLevel ← getLevel targetType
  unless sourceLevel == targetLevel do
    throwError "Native095 original projection TYPE universes differ."
  logInfo m!"Native095 actual source projection: {sourceProjection}; OWN type={sourceType}."
  logInfo m!"Native095 actual target projection: {targetProjection}; OWN type={targetType}."
  let (certificate, state) ←
    (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.structuralHEq
      sourceProjection targetProjection 96 #[] "full142").run {}
  let certificate ← phiNativeNoRecovery025 certificate
  let certificateType ← phiNativeNoRecovery025 (← whnf (← inferType certificate))
  let some (_, actualSource, _, actualTarget) := certificateType.consumeMData.headBeta.heq?
    | throwError "Native095 frozen projection certificate did not return HEq4."
  unless actualSource.consumeMData.equal sourceProjection.consumeMData &&
      actualTarget.consumeMData.equal targetProjection.consumeMData do
    throwError "Native095 projection certificate changed exact original instance values."
  let expected := mkAppN (mkConst ``HEq [sourceLevel])
    #[sourceType, sourceProjection, targetType, targetProjection]
  -- Existing ordinary native leaves can state both data values on their own
  -- homogeneous type. This isolated ordinary id retains the ACTUAL two TYPES
  -- of these literal instances rather than silently replacing the right one.
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``id [Level.zero]) #[expected, certificate])
  let proofType ← phiNativeNoRecovery025 (← inferType proof)
  unless proofType.consumeMData.headBeta.equal expected.consumeMData.headBeta do
    throwError "Native095 projection HEq changed either original instance/type endpoint."
  logInfo m!"Native095 genuine literal projection HEq: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}; BOTH actual original projection TYPES and VALUES retained, no homogeneous carrier equality assumed."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalRingProjectionHEqOwn095
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_projection_heq095%
      (actualOriginalGlobalPhiNativeOriginalMiddleObjectHEqOwn090 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_projection_heq095%
    (actualOriginalGlobalPhiNativeOriginalMiddleObjectHEqOwn090 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

/-- Ordinary type_eq_of_heq uses the genuine actual projection HEq's stored
five-vector. It independently certifies the reported carrier/type boundary. -/
elab "phi_native_original_projection_type095% " supplied:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalRingProjectionHEqOwn095 &&
      source.getAppArgs.size == 8 do
    throwError "Native095 requires only certified literal projection HEq095."
  let proposition ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (sourceType, sourceProjection, targetType, targetProjection) := proposition.consumeMData.headBeta.heq?
    | throwError "Native095 projection type extraction requires real HEq4."
  let .const heqName levels := proposition.consumeMData.headBeta.getAppFn
    | throwError "Native095 requires exact stored HEq universe head."
  let info ← getConstInfo ``type_eq_of_heq
  unless heqName == ``HEq && levels.length == 1 && info.levelParams.length == 1 do
    throwError "Native095 type_eq_of_heq stored universe count differs."
  let sourceSort ← phiNativeNoRecovery025 (← inferType sourceType)
  let targetSort ← phiNativeNoRecovery025 (← inferType targetType)
  let args := #[sourceType, targetType, sourceProjection, targetProjection, source]
  let expectedDomains := #[sourceSort, targetSort, sourceType, targetType, proposition]
  let mut lawType := info.instantiateTypeLevelParams levels
  for i in [:5] do
    let .forallE _ domain body _ := lawType
      | throwError "Native095 type_eq_of_heq actual prefix ended early."
    unless domain.consumeMData.equal expectedDomains[i]!.consumeMData do
      phiNativeJoinPath070 "type095.actual-type-equality-binder" domain expectedDomains[i]!
      throwError "Native095 type_eq_of_heq does not preserve exact stored source HEq arguments."
    lawType := body.instantiate1 args[i]!
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``type_eq_of_heq levels) args)
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (actualSort, actualSourceType, actualTargetType) := proofType.consumeMData.headBeta.eq?
    | throwError "Native095 existing type_eq_of_heq did not return Eq3."
  unless actualSort.consumeMData.equal sourceSort.consumeMData &&
      actualSourceType.consumeMData.equal sourceType.consumeMData &&
      actualTargetType.consumeMData.equal targetType.consumeMData do
    throwError "Native095 ordinary type equality changed actual original projection TYPE endpoints."
  logInfo "Native095 existing type_eq_of_heq full five-vector certifies ONLY the actual CommRing(projection-left-carrier) = CommRing(projection-right-forget-object-carrier), preserving all stored original projection/type values."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalRingProjectionTypeEqOwn095
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_projection_type095%
      (actualOriginalGlobalPhiNativeOriginalRingProjectionHEqOwn095 p hp P hP s)) :=
  phi_native_original_projection_type095%
    (actualOriginalGlobalPhiNativeOriginalRingProjectionHEqOwn095 p hp P hP s)

meta section
open Lean Meta Elab Term

/-- Lift genuine heterogeneous projections through ONLY the actual of2
constructor, retaining both original instance TYPE representations. -/
elab "phi_native_original_inner_ring096% " supplied:term " with_types " typeLaw:term
    " with_objects " objectLaw:term " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let typeLaw ← phiNativeNoRecovery025 (← Term.elabTerm typeLaw none (catchExPostpone := false))
  let objectLaw ← phiNativeNoRecovery025 (← Term.elabTerm objectLaw none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalRingProjectionHEqOwn095 &&
      source.getAppArgs.size == 8 &&
      typeLaw.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalRingProjectionTypeEqOwn095 &&
      typeLaw.getAppArgs.size == 8 do
    throwError "Native096 requires only passed exact projection HEq/TYPE Eq095."
  let (sourceRing, innerRing) ← phiNativeOriginalRingPair094 objectLaw nativeProp
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData &&
        typeLaw.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native096 refuses projection/type proofs on different original arguments."
  let sourceProposition ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (sourceProjectionType, sourceProjection, targetProjectionType, targetProjection) :=
      sourceProposition.consumeMData.headBeta.heq?
    | throwError "Native096 requires actual original projection HEq4."
  let typeProposition ← phiNativeNoRecovery025 (← whnf (← inferType typeLaw))
  let some (_, actualSourceType, actualTargetType) := typeProposition.consumeMData.headBeta.eq?
    | throwError "Native096 requires actual original projection TYPE Eq3."
  unless sourceProjection.consumeMData.equal sourceRing.getAppArgs[1]!.consumeMData &&
      targetProjection.consumeMData.equal innerRing.getAppArgs[1]!.consumeMData &&
      actualSourceType.consumeMData.equal sourceProjectionType.consumeMData &&
      actualTargetType.consumeMData.equal targetProjectionType.consumeMData do
    throwError "Native096 literal projection/type certificates do not raw join original ring vectors."
  let congruence ← mkHCongrWithArity sourceRing.getAppFn 2
  let projectionLevel ← getLevel sourceProjectionType
  let mut arguments := #[]
  for i in [:2] do
    let compatibility ← if i == 1 then
      match congruence.argKinds[i]! with
      | .heq => pure source
      | .eq => pure (mkAppN (mkConst ``eq_of_heq [projectionLevel])
          #[sourceProjectionType, sourceProjection, targetProjection, source])
      | _ => throwError "Native096 unsupported original instance constructor congruence kind."
    else do
      let heq ← mkHEqRefl sourceRing.getAppArgs[i]!
      match congruence.argKinds[i]! with
      | .eq => mkEqOfHEq heq
      | .heq => pure heq
      | _ => throwError "Native096 unsupported original carrier constructor congruence kind."
    arguments := arguments ++ #[sourceRing.getAppArgs[i]!, innerRing.getAppArgs[i]!, compatibility]
  let ringHEq ← phiNativeNoRecovery025 (mkAppN congruence.proof arguments)
  let ringHEqType ← phiNativeNoRecovery025 (← whnf (← inferType ringHEq))
  let some (sourceRingType, actualSourceRing, targetRingType, actualInnerRing) :=
      ringHEqType.consumeMData.headBeta.heq?
    | throwError "Native096 ordinary constructor congruence did not return ring HEq4."
  unless actualSourceRing.consumeMData.equal sourceRing.consumeMData &&
      actualInnerRing.consumeMData.equal innerRing.consumeMData &&
      sourceRingType.consumeMData.equal targetRingType.consumeMData do
    throwError "Native096 ordinary constructor congruence changed original ring values/type."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``eq_of_heq [← getLevel sourceRingType])
      #[sourceRingType, sourceRing, innerRing, ringHEq])
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (actualRingType, actualSourceRing, actualInnerRing) := proofType.consumeMData.headBeta.eq?
    | throwError "Native096 original ring constructor lift is not Eq3."
  unless actualRingType.consumeMData.equal sourceRingType.consumeMData &&
      actualSourceRing.consumeMData.equal sourceRing.consumeMData &&
      actualInnerRing.consumeMData.equal innerRing.consumeMData do
    throwError "Native096 heterogeneous projection lift changed literal original single rings."
  logInfo "Native096 actual CommRingCat.of2 hcongr consumes genuine projectionHEq095 with both TYPE095 vectors guarded; source carrier unchanged. Full eq_of_heq4 yields exact original source single ring = actual common inner single ring."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalInnerRingEqOwn096
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_inner_ring096%
      (actualOriginalGlobalPhiNativeOriginalRingProjectionHEqOwn095 p hp P hP s)
      with_types (actualOriginalGlobalPhiNativeOriginalRingProjectionTypeEqOwn095 p hp P hP s)
      with_objects (actualOriginalGlobalPhiNativeOriginalMiddleObjectHEqOwn090 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_inner_ring096%
    (actualOriginalGlobalPhiNativeOriginalRingProjectionHEqOwn095 p hp P hP s)
    with_types (actualOriginalGlobalPhiNativeOriginalRingProjectionTypeEqOwn095 p hp P hP s)
    with_objects (actualOriginalGlobalPhiNativeOriginalMiddleObjectHEqOwn090 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

/-- The existing canonical bundle law now receives the ACTUAL common inner
ring, whose equality to source is independently certified, not guessed. -/
elab "phi_native_original_common_ring096% " supplied:term " with_objects " objectLaw:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let objectLaw ← phiNativeNoRecovery025 (← Term.elabTerm objectLaw none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalInnerRingEqOwn096 &&
      source.getAppArgs.size == 8 do
    throwError "Native096 requires only certified exact original inner-ring Eq096."
  let (sourceRing, innerRing) ← phiNativeOriginalRingPair094 objectLaw nativeProp
  let v ← phiNativeOriginalCommonCategoryVectors093 objectLaw nativeProp
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native096 refuses inner-ring equality on different original arguments."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (ringType, actualSourceRing, actualInnerRing) := sourceType.consumeMData.headBeta.eq?
    | throwError "Native096 requires actual inner-ring Eq3."
  unless actualSourceRing.consumeMData.equal sourceRing.consumeMData &&
      actualInnerRing.consumeMData.equal innerRing.consumeMData do
    throwError "Native096 inner-ring certificate does not raw join original single rings."
  let commonSpec := v.commonCategory.consumeMData.headBeta.getAppArgs[0]!.consumeMData.headBeta
  let commonRing := commonSpec.getAppArgs[0]!
  let .const _ levels := innerRing.getAppFn
    | throwError "Native096 requires actual common inner-ring universe head."
  let info ← getConstInfo ``phiNativeCanonicalBundle013
  unless levels.length == 1 && info.levelParams.length == 1 do
    throwError "Native096 canonical bundle universe count differs."
  let bundleLaw ← phiNativeNoRecovery025
    (mkAppN (mkConst ``phiNativeCanonicalBundle013 levels) #[innerRing])
  let bundleType ← phiNativeNoRecovery025 (← whnf (← inferType bundleLaw))
  let some (bundleRingType, actualDouble, actualSingle) := bundleType.consumeMData.headBeta.eq?
    | throwError "Native096 existing canonical bundle law did not return Eq3."
  unless bundleRingType.consumeMData.equal ringType.consumeMData &&
      actualDouble.consumeMData.equal commonRing.consumeMData &&
      actualSingle.consumeMData.equal innerRing.consumeMData do
    phiNativeJoinPath070 "common096.actual-inner-canonical-double-to-map-ring" actualDouble commonRing
    throwError "Native096 existing canonical law does not raw join actual common inner/double rings."
  let forward ← phiNativeNoRecovery025
    (mkAppN (mkConst ``Eq.symm [← getLevel ringType])
      #[ringType, commonRing, innerRing, bundleLaw])
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``Eq.trans [← getLevel ringType])
      #[ringType, sourceRing, innerRing, commonRing, source, forward])
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (actualRingType, actualSource, actualCommon) := proofType.consumeMData.headBeta.eq?
    | throwError "Native096 actual common-ring assembly did not return Eq3."
  unless actualRingType.consumeMData.equal ringType.consumeMData &&
      actualSource.consumeMData.equal sourceRing.consumeMData &&
      actualCommon.consumeMData.equal commonRing.consumeMData do
    throwError "Native096 common ring assembly changed original source/common ring endpoints."
  logInfo "Native096 existing CanonicalBundle013 on EXACT actual common inner ring, original single-ring Eq096 and full Eq.symm4/Eq.trans6 produce original source single ring = actual common double ring; all ordinary law/endpoints raw guarded."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalCommonRingEqOwn096
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_common_ring096%
      (actualOriginalGlobalPhiNativeOriginalInnerRingEqOwn096 p hp P hP s)
      with_objects (actualOriginalGlobalPhiNativeOriginalMiddleObjectHEqOwn090 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_common_ring096%
    (actualOriginalGlobalPhiNativeOriginalInnerRingEqOwn096 p hp P hP s)
    with_objects (actualOriginalGlobalPhiNativeOriginalMiddleObjectHEqOwn090 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

/-- Project ONLY certified original ring equality through the original
Modules∘Spec heads, giving the exact category boundary required by091. -/
elab "phi_native_original_common_category096% " supplied:term " with_objects " objectLaw:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let objectLaw ← phiNativeNoRecovery025 (← Term.elabTerm objectLaw none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalCommonRingEqOwn096 &&
      source.getAppArgs.size == 8 do
    throwError "Native096 requires only certified original common-ring Eq096."
  let v ← phiNativeOriginalCommonCategoryVectors093 objectLaw nativeProp
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native096 refuses category projection on different original arguments."
  let sourceCategory := v.sourceType.consumeMData.headBeta
  let commonCategory := v.commonCategory.consumeMData.headBeta
  unless sourceCategory.getAppFn.isConstOf ``AlgebraicGeometry.Scheme.Modules &&
      sourceCategory.getAppFn.equal commonCategory.getAppFn &&
      sourceCategory.getAppArgs.size == 1 && commonCategory.getAppArgs.size == 1 do
    throwError "Native096 requires exact original Modules category heads."
  let sourceSpec := sourceCategory.getAppArgs[0]!.consumeMData.headBeta
  let commonSpec := commonCategory.getAppArgs[0]!.consumeMData.headBeta
  unless sourceSpec.getAppFn.isConstOf ``AlgebraicGeometry.Spec &&
      sourceSpec.getAppFn.equal commonSpec.getAppFn &&
      sourceSpec.getAppArgs.size == 1 && commonSpec.getAppArgs.size == 1 do
    throwError "Native096 requires exact original Spec category heads."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (ringType, sourceRing, commonRing) := sourceType.consumeMData.headBeta.eq?
    | throwError "Native096 requires actual common-ring Eq3."
  unless sourceRing.consumeMData.equal sourceSpec.getAppArgs[0]!.consumeMData &&
      commonRing.consumeMData.equal commonSpec.getAppArgs[0]!.consumeMData do
    throwError "Native096 common-ring equality does not raw join original category ring vectors."
  let outputSort ← phiNativeNoRecovery025 (← inferType sourceCategory)
  let commonSort ← phiNativeNoRecovery025 (← inferType commonCategory)
  unless outputSort.consumeMData.equal commonSort.consumeMData do
    throwError "Native096 actual original category universes differ."
  let evaluator ← withLocalDeclD `originalCategoryRing ringType fun originalCategoryRing =>
    mkLambdaFVars #[originalCategoryRing]
      (mkAppN sourceCategory.getAppFn #[mkAppN sourceSpec.getAppFn #[originalCategoryRing]])
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``congrArg [← getLevel ringType, ← getLevel outputSort])
      #[ringType, outputSort, sourceRing, commonRing, evaluator, source])
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (actualSort, actualSourceCategory, actualCommonCategory) := proofType.consumeMData.headBeta.eq?
    | throwError "Native096 original category lift did not return Eq3."
  unless actualSort.consumeMData.equal outputSort.consumeMData &&
      actualSourceCategory.consumeMData.headBeta.equal sourceCategory &&
      actualCommonCategory.consumeMData.headBeta.equal commonCategory do
    throwError "Native096 ring/category lift changed literal original category endpoints."
  logInfo "Native096 full congrArg6 lifts separately certified original ring Eq through exact original Modules/Spec heads, giving actual sourceHEq TYPE = common map category, no object/functor application aggregated."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalCommonCategoryEqOwn096
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_common_category096%
      (actualOriginalGlobalPhiNativeOriginalCommonRingEqOwn096 p hp P hP s)
      with_objects (actualOriginalGlobalPhiNativeOriginalMiddleObjectHEqOwn090 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_common_category096%
    (actualOriginalGlobalPhiNativeOriginalCommonRingEqOwn096 p hp P hP s)
    with_objects (actualOriginalGlobalPhiNativeOriginalMiddleObjectHEqOwn090 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)
meta section
open Lean Meta Elab Term

/-- Ordinary proposition transport changes ONLY the source HEq's right TYPE
to the independently certified original map category, with SAME literal objects. -/
elab "phi_native_original_common_object097% " supplied:term " using_category " categoryLaw:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let categoryLaw ← phiNativeNoRecovery025 (← Term.elabTerm categoryLaw none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let v ← phiNativeOriginalCommonCategoryVectors093 source nativeProp
  unless categoryLaw.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalCommonCategoryEqOwn096 &&
      categoryLaw.getAppArgs.size == 8 do
    throwError "Native097 requires only independently certified original category Eq096."
  for i in [:8] do
    unless categoryLaw.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native097 refuses category transport on different original arguments."
  let categoryType ← phiNativeNoRecovery025 (← whnf (← inferType categoryLaw))
  let some (_, actualSourceType, actualCommonCategory) := categoryType.consumeMData.headBeta.eq?
    | throwError "Native097 requires real original category Eq3."
  unless actualSourceType.consumeMData.equal v.sourceType.consumeMData &&
      actualCommonCategory.consumeMData.equal v.commonCategory.consumeMData do
    throwError "Native097 category equality does not raw join exact sourceHEq/map type vectors."
  let heqHead := v.sourceProposition.consumeMData.headBeta.getAppFn
  unless heqHead.isConstOf ``HEq do
    throwError "Native097 requires exact original HEq constant/universe head."
  let target ← phiNativeNoRecovery025
    (mkAppN heqHead #[v.targetType, v.targetObject, v.commonCategory, v.sourceObject])
  let seed ← phiNativeNoRecovery025 (← mkHEqOfEq categoryLaw)
  let reverseSeed ← phiNativeNoRecovery025 (← mkHEqSymm seed)
  let (compatibility, state) ←
    (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.structuralHEq
      v.sourceProposition target 96 #[] "full142").run
        { pairs := #[(v.sourceType, v.commonCategory, seed),
          (v.commonCategory, v.sourceType, reverseSeed)] }
  let typeEq ← phiNativeNoRecovery025 (← mkEqOfHEq compatibility)
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``Eq.mp [Level.zero]) #[v.sourceProposition, target, typeEq, source])
  let proofType ← phiNativeNoRecovery025 (← inferType proof)
  unless proofType.consumeMData.headBeta.equal target.consumeMData.headBeta do
    throwError "Native097 certified HEq type transport changed original literal object values."
  logInfo m!"Native097 original common-category OBJECT HEq transport: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}; only exact certified right TYPE changes, original object values preserved."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalCommonObjectHEqOwn097
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_common_object097%
      (actualOriginalGlobalPhiNativeOriginalMiddleObjectHEqOwn090 p hp P hP s)
      using_category (actualOriginalGlobalPhiNativeOriginalCommonCategoryEqOwn096 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_common_object097%
    (actualOriginalGlobalPhiNativeOriginalMiddleObjectHEqOwn090 p hp P hP s)
    using_category (actualOriginalGlobalPhiNativeOriginalCommonCategoryEqOwn096 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

/-- Same original091 homogeneous category/object guard, now fed an ordinary
proof whose right TYPE genuinely equals the exact common map-category vector. -/
elab "phi_native_original_common_eq097% " supplied:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalCommonObjectHEqOwn097 &&
      source.getAppArgs.size == 8 do
    throwError "Native097 requires only certified common-category original object HEq097."
  let (expectedTarget, expectedSource) ← phiNativeOriginalMiddleObjects090 nativeProp
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native097 refuses homogeneous object equality on different original arguments."
  let body ← phiNativeCoefficientBody087 nativeProp
  let some (_, _, nestedPoint) := body.consumeMData.headBeta.eq?
    | throwError "Native097 requires original Stage0 body."
  let outer ← phiNativePointVectors033 nestedPoint.consumeMData.headBeta.getAppArgs[5]!
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (_, originalTarget, originalSourceType, originalSource) := sourceType.consumeMData.headBeta.heq?
    | throwError "Native097 requires actual common-category original object HEq4."
  let commonCategory := outer.mapArgs[0]!
  unless originalTarget.consumeMData.equal expectedTarget.consumeMData &&
      originalSource.consumeMData.equal expectedSource.consumeMData &&
      originalSourceType.consumeMData.equal commonCategory.consumeMData do
    throwError "Native097 object certificate does not raw join exact original common map category/objects."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``eq_of_heq [← getLevel commonCategory])
      #[commonCategory, originalTarget, originalSource, source])
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (actualCategory, actualTarget, actualSource) := proofType.consumeMData.headBeta.eq?
    | throwError "Native097 actual homogeneous object identity is not Eq3."
  unless actualCategory.consumeMData.equal commonCategory.consumeMData &&
      actualTarget.consumeMData.equal originalTarget.consumeMData &&
      actualSource.consumeMData.equal originalSource.consumeMData do
    throwError "Native097 ordinary object Eq changed original category/object values."
  logInfo "Native097 ordinary eq_of_heq4 on actual common-category object HEq; all original091 category/object raw guards retained and genuinely satisfied. No incoming map or point application aggregated."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalCommonObjectEqOwn097
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_common_eq097%
      (actualOriginalGlobalPhiNativeOriginalCommonObjectHEqOwn097 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_common_eq097%
    (actualOriginalGlobalPhiNativeOriginalCommonObjectHEqOwn097 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)
meta section
open Lean Meta Elab Term

/-- Retain both original maps and point values while exposing their actual
nested functor application vectors. -/
private def phiNativeOriginalNestedVectors097 (nativeProp : Expr) :
    TermElabM (Expr × PhiNativePointVectors033 × PhiNativePointVectors033) := do
  let _ ← phiNativeOriginalMiddleObjects090 nativeProp
  let body ← phiNativeCoefficientBody087 nativeProp
  let some (_, _, nestedPoint) := body.consumeMData.headBeta.eq?
    | throwError "Native097 requires exact original Stage0 Eq."
  let nestedPoint := nestedPoint.consumeMData.headBeta
  let ea := nestedPoint.getAppArgs
  unless nestedPoint.getAppFn.isConstOf ``DFunLike.coe && ea.size == 6 do
    throwError "Native097 requires literal original E.coercion6."
  let outer ← phiNativePointVectors033 ea[5]!
  let inner ← phiNativePointVectors033 outer.coeArgs[5]!
  return (nestedPoint, outer, inner)

/-- Isolate incoming Functor.map compatibility, changing ONLY its proved
intermediate target object; SAME original f/G/X and every remaining argument. -/
elab "phi_native_original_incoming_map097% " supplied:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalCommonObjectEqOwn097 &&
      source.getAppArgs.size == 8 do
    throwError "Native097 requires only original common-category object Eq097."
  let (_, outer, inner) ← phiNativeOriginalNestedVectors097 nativeProp
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native097 refuses incoming map comparison on different original arguments."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (category, originalTarget, originalSource) := sourceType.consumeMData.headBeta.eq?
    | throwError "Native097 requires exact original common-category object Eq3."
  unless category.consumeMData.equal outer.mapArgs[0]!.consumeMData &&
      originalTarget.consumeMData.equal inner.mapArgs[6]!.consumeMData &&
      originalSource.consumeMData.equal outer.mapArgs[5]!.consumeMData do
    throwError "Native097 object Eq does not join exact incoming/outgoing map object vector."
  let alignedArgs := inner.mapArgs.set! 6 originalSource
  let congruence ← mkHCongrWithArity inner.mapped.getAppFn 8
  let mut arguments := #[]
  for i in [:8] do
    let compatibility ← if i == 6 then
      match congruence.argKinds[i]! with
      | .eq => pure source
      | .heq => mkHEqOfEq source
      | _ => throwError "Native097 unsupported intermediate object congruence argument kind."
    else do
      let heq ← mkHEqRefl inner.mapArgs[i]!
      match congruence.argKinds[i]! with
      | .eq => mkEqOfHEq heq
      | .heq => pure heq
      | _ => throwError "Native097 unsupported unchanged map congruence argument kind."
    arguments := arguments ++ #[inner.mapArgs[i]!, alignedArgs[i]!, compatibility]
  let proof ← phiNativeNoRecovery025 (mkAppN congruence.proof arguments)
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (_, actualOriginal, _, actualAligned) := proofType.consumeMData.headBeta.heq?
    | throwError "Native097 incoming map comparison is not HEq4."
  let aligned := mkAppN inner.mapped.getAppFn alignedArgs
  unless actualOriginal.consumeMData.equal inner.mapped.consumeMData &&
      actualAligned.consumeMData.equal aligned.consumeMData do
    throwError "Native097 incoming map comparison changed original f/G/X or non-middle arguments."
  logInfo "Native097 ordinary full-eight-argument hcongr changes ONLY certified intermediate Y; every original f/G/X value and other map argument retained. No Phi/accessor/E application aggregated."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalIncomingMapHEqOwn097
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_incoming_map097%
      (actualOriginalGlobalPhiNativeOriginalCommonObjectEqOwn097 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_incoming_map097%
    (actualOriginalGlobalPhiNativeOriginalCommonObjectEqOwn097 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

/-- Own generic law on the exact original f/g/Phi and proved common Y.
Its incoming-map vector must raw join the independently certified alignment.
This is NOT yet comparison with the original nested coercion endpoint. -/
elab "phi_native_original_nested_own097% " supplied:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalIncomingMapHEqOwn097 &&
      source.getAppArgs.size == 8 do
    throwError "Native097 requires only certified original incoming map HEq097."
  let (nestedPoint, outer, inner) ← phiNativeOriginalNestedVectors097 nativeProp
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native097 refuses generic composition on different original arguments."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (_, originalMap, _, alignedMap) := sourceType.consumeMData.headBeta.heq?
    | throwError "Native097 requires actual incoming map HEq4."
  let alignedArgs := inner.mapArgs.set! 6 outer.mapArgs[5]!
  unless originalMap.consumeMData.equal inner.mapped.consumeMData &&
      alignedMap.consumeMData.equal (mkAppN inner.mapped.getAppFn alignedArgs).consumeMData do
    throwError "Native097 incoming map certificate does not join exact certified common-Y vector."
  let ea := nestedPoint.getAppArgs
  let destination := outer.mapArgs[2]!.consumeMData.headBeta
  let da := destination.getAppArgs
  unless destination.getAppFn.isConstOf ``ModuleCat && da.size == 2 do
    throwError "Native097 requires exact original destination scalar/ring vector."
  let inputCarrier ← phiNativeNoRecovery025 (← inferType outer.endpoint)
  let inputCarrier := inputCarrier.consumeMData.headBeta
  let outputCarrier ← phiNativeNoRecovery025 (← inferType nestedPoint)
  let outputCarrier := outputCarrier.consumeMData.headBeta
  let evaluator ← withLocalDeclD `originalCompositionPoint inputCarrier fun originalCompositionPoint =>
    mkLambdaFVars #[originalCompositionPoint]
      (mkAppN nestedPoint.getAppFn (ea.set! 5 originalCompositionPoint))
  let evaluatorType ← phiNativeNoRecovery025 (← inferType evaluator)
  let .forallE _ domain codomain _ := evaluatorType.consumeMData
    | throwError "Native097 original E evaluator lacks its mapped-point domain."
  unless domain.consumeMData.equal inputCarrier.consumeMData &&
      (codomain.instantiate1 outer.endpoint).consumeMData.headBeta.equal outputCarrier do
    throwError "Native097 E evaluator changed original mapped input/output carrier."
  let args := #[da[0]!, da[1]!, outer.mapArgs[0]!, outer.mapArgs[1]!, outer.mapArgs[4]!,
    inner.mapArgs[5]!, outer.mapArgs[5]!, outer.mapArgs[6]!,
    inner.mapArgs[7]!, outer.mapArgs[7]!, inner.coeArgs[5]!, outputCarrier, evaluator]
  let resolved ← phiNativeNoRecovery025
    (← mkAppOptM ``phiNativeMappedCompositionUnder059 (args.map some))
  let proof ← phiNativeNoRecovery025 (mkAppN resolved.getAppFn args)
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (actualCarrier, actualNested, actualComposite) := proofType.consumeMData.headBeta.eq?
    | throwError "Native097 own generic composition did not return Eq3."
  unless actualCarrier.consumeMData.equal outputCarrier.consumeMData do
    throwError "Native097 generic composition changed original E output carrier."
  let actualNested := actualNested.consumeMData.headBeta
  let actualComposite := actualComposite.consumeMData.headBeta
  for endpoint in #[actualNested, actualComposite] do
    let endpointArgs := endpoint.getAppArgs
    unless endpoint.getAppFn.equal nestedPoint.getAppFn && endpointArgs.size == 6 do
      throwError "Native097 generic composition changed original E coercion head."
    for i in [:5] do
      unless endpointArgs[i]!.consumeMData.equal ea[i]!.consumeMData do
        throwError "Native097 generic composition changed original E prefix."
  let actualOuter ← phiNativePointVectors033 actualNested.getAppArgs[5]!
  let actualInner ← phiNativePointVectors033 actualOuter.coeArgs[5]!
  for i in [:8] do
    unless actualOuter.mapArgs[i]!.consumeMData.equal outer.mapArgs[i]!.consumeMData &&
        actualInner.mapArgs[i]!.consumeMData.equal alignedArgs[i]!.consumeMData do
      throwError "Native097 generic source changed original f/g/category/G/object map vector."
  unless actualInner.coeArgs[5]!.consumeMData.equal inner.coeArgs[5]!.consumeMData do
    throwError "Native097 generic source changed original Phi."
  let result ← phiNativePointVectors033 actualComposite.getAppArgs[5]!
  let composite := result.mapArgs[7]!.consumeMData.headBeta
  let fa := composite.getAppArgs
  unless composite.getAppFn.isConstOf ``CategoryTheory.CategoryStruct.comp && fa.size == 7 &&
      fa[0]!.consumeMData.equal outer.mapArgs[0]!.consumeMData &&
      fa[2]!.consumeMData.equal inner.mapArgs[5]!.consumeMData &&
      fa[3]!.consumeMData.equal outer.mapArgs[5]!.consumeMData &&
      fa[4]!.consumeMData.equal outer.mapArgs[6]!.consumeMData &&
      fa[5]!.consumeMData.equal inner.mapArgs[7]!.consumeMData &&
      fa[6]!.consumeMData.equal outer.mapArgs[7]!.consumeMData &&
      result.mapArgs[4]!.consumeMData.equal outer.mapArgs[4]!.consumeMData &&
      result.coeArgs[5]!.consumeMData.equal inner.coeArgs[5]!.consumeMData do
    throwError "Native097 generic composite changed original G/f/g/Phi or certified middle Y."
  logInfo "Native097 existing generic059 full thirteen-vector uses SAME original f/g/Phi and independently certified common Y/incoming map; canonical original map values raw guarded. Literal original nested coercion compatibility remains separate, not assumed."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalNestedCompositionOwn097
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_nested_own097%
      (actualOriginalGlobalPhiNativeOriginalIncomingMapHEqOwn097 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_nested_own097%
    (actualOriginalGlobalPhiNativeOriginalIncomingMapHEqOwn097 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

private structure PhiNativeNestedPointPair098 where
  originalNested : Expr
  canonicalNested : Expr
  composite : Expr
  carrier : Expr
  originalOuter : PhiNativePointVectors033
  canonicalOuter : PhiNativePointVectors033
  originalInner : PhiNativePointVectors033
  canonicalInner : PhiNativePointVectors033

/-- Exact original Stage0 RHS and actually checked generic097 source point.
EVERY original map/Phi/E prefix is retained; ONLY proved middle Y differs. -/
private def phiNativeOriginalNestedPointPair098 (source nativeProp : Expr) :
    TermElabM PhiNativeNestedPointPair098 := do
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalNestedCompositionOwn097 &&
      source.getAppArgs.size == 8 do
    throwError "Native098 requires only passed original nested generic Eq097."
  let (originalNested, originalOuter, originalInner) ← phiNativeOriginalNestedVectors097 nativeProp
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native098 refuses generic point comparison on different original arguments."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (carrier, canonicalNested, composite) := sourceType.consumeMData.headBeta.eq?
    | throwError "Native098 requires actual generic nested Eq3."
  let canonicalNested := canonicalNested.consumeMData.headBeta
  let oa := originalNested.getAppArgs
  let ca := canonicalNested.getAppArgs
  unless originalNested.getAppFn.equal canonicalNested.getAppFn && oa.size == 6 && ca.size == 6 do
    throwError "Native098 requires original E.coercion6 on both nested endpoints."
  for i in [:5] do
    unless oa[i]!.consumeMData.equal ca[i]!.consumeMData do
      throwError "Native098 refuses different original E/scalar/coercion prefixes."
  let canonicalOuter ← phiNativePointVectors033 ca[5]!
  let canonicalInner ← phiNativePointVectors033 canonicalOuter.coeArgs[5]!
  let aligned := originalInner.mapArgs.set! 6 originalOuter.mapArgs[5]!
  for i in [:8] do
    unless canonicalOuter.mapArgs[i]!.consumeMData.equal originalOuter.mapArgs[i]!.consumeMData &&
        canonicalInner.mapArgs[i]!.consumeMData.equal aligned[i]!.consumeMData do
      throwError "Native098 refuses changed original f/g/G/category/objects beyond certified middle Y."
  unless canonicalInner.coeArgs[5]!.consumeMData.equal originalInner.coeArgs[5]!.consumeMData do
    throwError "Native098 refuses different original Phi."
  return ⟨originalNested, canonicalNested, composite, carrier,
    originalOuter, canonicalOuter, originalInner, canonicalInner⟩

/-- Isolate actual incoming mapped-point compatibility; passed original map
and object certificates are exact cache leaves, not arbitrary replacements. -/
elab "phi_native_original_incoming_point098% " supplied:term " using_map " mapLaw:term
    " using_object " objectLaw:term " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let mapLaw ← phiNativeNoRecovery025 (← Term.elabTerm mapLaw none (catchExPostpone := false))
  let objectLaw ← phiNativeNoRecovery025 (← Term.elabTerm objectLaw none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let v ← phiNativeOriginalNestedPointPair098 source nativeProp
  unless mapLaw.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalIncomingMapHEqOwn097 &&
      mapLaw.getAppArgs.size == 8 &&
      objectLaw.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalCommonObjectEqOwn097 &&
      objectLaw.getAppArgs.size == 8 do
    throwError "Native098 requires only passed literal incoming map/object097 certificates."
  for i in [:8] do
    unless mapLaw.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData &&
        objectLaw.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native098 refuses incoming certificates on different original arguments."
  let mapType ← phiNativeNoRecovery025 (← whnf (← inferType mapLaw))
  let some (_, mapLeft, _, mapRight) := mapType.consumeMData.headBeta.heq?
    | throwError "Native098 requires actual incoming map HEq4."
  let objectType ← phiNativeNoRecovery025 (← whnf (← inferType objectLaw))
  let some (objectCategory, objectLeft, objectRight) := objectType.consumeMData.headBeta.eq?
    | throwError "Native098 requires actual original object Eq3."
  unless mapLeft.consumeMData.equal v.originalInner.mapped.consumeMData &&
      mapRight.consumeMData.equal v.canonicalInner.mapped.consumeMData &&
      objectLeft.consumeMData.equal v.originalInner.mapArgs[6]!.consumeMData &&
      objectRight.consumeMData.equal v.canonicalInner.mapArgs[6]!.consumeMData &&
      objectCategory.consumeMData.equal v.originalInner.mapArgs[0]!.consumeMData do
    throwError "Native098 incoming certificates do not raw join literal original/generic point vectors."
  let mapReverse ← phiNativeNoRecovery025 (← mkHEqSymm mapLaw)
  let objectHEq ← phiNativeNoRecovery025 (← mkHEqOfEq objectLaw)
  let objectReverse ← phiNativeNoRecovery025 (← mkHEqSymm objectHEq)
  let originalPoint := v.originalInner.endpoint
  let canonicalPoint := v.canonicalInner.endpoint
  let originalType ← phiNativeNoRecovery025 (← inferType originalPoint)
  let canonicalType ← phiNativeNoRecovery025 (← inferType canonicalPoint)
  let originalLevel ← getLevel originalType
  let canonicalLevel ← getLevel canonicalType
  unless originalLevel == canonicalLevel do
    throwError "Native098 actual original incoming point universes differ."
  let (certificate, state) ←
    (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.structuralHEq
      originalPoint canonicalPoint 96 #[] "full142").run
        { pairs := #[(mapLeft, mapRight, mapLaw), (mapRight, mapLeft, mapReverse),
          (objectLeft, objectRight, objectHEq), (objectRight, objectLeft, objectReverse)] }
  let certificate ← phiNativeNoRecovery025 certificate
  let certificateType ← phiNativeNoRecovery025 (← whnf (← inferType certificate))
  let some (_, actualOriginal, _, actualCanonical) := certificateType.consumeMData.headBeta.heq?
    | throwError "Native098 incoming point certificate is not HEq4."
  unless actualOriginal.consumeMData.equal originalPoint.consumeMData &&
      actualCanonical.consumeMData.equal canonicalPoint.consumeMData do
    throwError "Native098 incoming point compatibility changed original map/Phi values."
  let expected := mkAppN (mkConst ``HEq [originalLevel])
    #[originalType, originalPoint, canonicalType, canonicalPoint]
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``id [Level.zero]) #[expected, certificate])
  let proofType ← phiNativeNoRecovery025 (← inferType proof)
  unless proofType.consumeMData.headBeta.equal expected.consumeMData.headBeta do
    throwError "Native098 incoming point HEq changed actual point TYPE endpoints."
  logInfo m!"Native098 literal incoming POINT compatibility: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}; both actual own point TYPES/maps/Phi retained, exact passed map/object097 seeds."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalIncomingPointHEqOwn098
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_incoming_point098%
      (actualOriginalGlobalPhiNativeOriginalNestedCompositionOwn097 p hp P hP s)
      using_map (actualOriginalGlobalPhiNativeOriginalIncomingMapHEqOwn097 p hp P hP s)
      using_object (actualOriginalGlobalPhiNativeOriginalCommonObjectEqOwn097 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_incoming_point098%
    (actualOriginalGlobalPhiNativeOriginalNestedCompositionOwn097 p hp P hP s)
    using_map (actualOriginalGlobalPhiNativeOriginalIncomingMapHEqOwn097 p hp P hP s)
    using_object (actualOriginalGlobalPhiNativeOriginalCommonObjectEqOwn097 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

/-- Lift only the checked incoming point through unchanged original outer
g and E. This is independent of the generic map_comp proof value. -/
elab "phi_native_original_nested_literal098% " supplied:term " using_point " pointLaw:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let pointLaw ← phiNativeNoRecovery025 (← Term.elabTerm pointLaw none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let v ← phiNativeOriginalNestedPointPair098 source nativeProp
  unless pointLaw.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalIncomingPointHEqOwn098 &&
      pointLaw.getAppArgs.size == 8 do
    throwError "Native098 requires only independently certified literal incoming point HEq098."
  for i in [:8] do
    unless pointLaw.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native098 refuses incoming point lift on different original arguments."
  let pointType ← phiNativeNoRecovery025 (← whnf (← inferType pointLaw))
  let some (_, pointLeft, _, pointRight) := pointType.consumeMData.headBeta.heq?
    | throwError "Native098 requires actual literal incoming point HEq4."
  unless pointLeft.consumeMData.equal v.originalInner.endpoint.consumeMData &&
      pointRight.consumeMData.equal v.canonicalInner.endpoint.consumeMData do
    throwError "Native098 incoming point certificate does not raw join original nested arguments."
  let originalCarrier ← phiNativeNoRecovery025 (← inferType v.originalNested)
  let originalCarrier := originalCarrier.consumeMData.headBeta
  unless originalCarrier.equal v.carrier.consumeMData.headBeta do
    phiNativeJoinPath070 "nested098.original-E-output-to-actual-generic-carrier" originalCarrier v.carrier
    throwError "Native098 original/generic nested points do not have exact original E output carrier."
  let reverseSeed ← phiNativeNoRecovery025 (← mkHEqSymm pointLaw)
  let (certificate, state) ←
    (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.structuralHEq
      v.originalNested v.canonicalNested 96 #[] "full142").run
        { pairs := #[(pointLeft, pointRight, pointLaw), (pointRight, pointLeft, reverseSeed)] }
  let certificate ← phiNativeNoRecovery025 certificate
  let certificateType ← phiNativeNoRecovery025 (← whnf (← inferType certificate))
  let some (_, actualOriginal, _, actualCanonical) := certificateType.consumeMData.headBeta.heq?
    | throwError "Native098 literal nested certificate is not HEq4."
  unless actualOriginal.consumeMData.equal v.originalNested.consumeMData &&
      actualCanonical.consumeMData.equal v.canonicalNested.consumeMData do
    throwError "Native098 literal nested compatibility changed original g/E/point values."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``eq_of_heq [← getLevel v.carrier])
      #[v.carrier, v.originalNested, v.canonicalNested, certificate])
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (actualCarrier, actualOriginal, actualCanonical) := proofType.consumeMData.headBeta.eq?
    | throwError "Native098 literal nested point comparison did not return Eq3."
  unless actualCarrier.consumeMData.equal v.carrier.consumeMData &&
      actualOriginal.consumeMData.equal v.originalNested.consumeMData &&
      actualCanonical.consumeMData.equal v.canonicalNested.consumeMData do
    throwError "Native098 literal nested Eq changed original carrier/g/E/point vectors."
  logInfo m!"Native098 literal original NESTED point compatibility: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}; only checked incoming point lifted, same original g/E and own output carrier, no map_comp aggregation."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalNestedPointEqOwn098
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_nested_literal098%
      (actualOriginalGlobalPhiNativeOriginalNestedCompositionOwn097 p hp P hP s)
      using_point (actualOriginalGlobalPhiNativeOriginalIncomingPointHEqOwn098 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_nested_literal098%
    (actualOriginalGlobalPhiNativeOriginalNestedCompositionOwn097 p hp P hP s)
    using_point (actualOriginalGlobalPhiNativeOriginalIncomingPointHEqOwn098 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

/-- Ordinary equality assembly after both literal compatibility and own
generic composition independently passed, with no endpoint conversions. -/
elab "phi_native_original_nested_composition098% " supplied:term " using_literal " literalLaw:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let literalLaw ← phiNativeNoRecovery025 (← Term.elabTerm literalLaw none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let v ← phiNativeOriginalNestedPointPair098 source nativeProp
  unless literalLaw.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalNestedPointEqOwn098 &&
      literalLaw.getAppArgs.size == 8 do
    throwError "Native098 requires only independently certified literal nested Eq098."
  for i in [:8] do
    unless literalLaw.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native098 refuses literal generic assembly on different original arguments."
  let literalType ← phiNativeNoRecovery025 (← whnf (← inferType literalLaw))
  let some (carrier, originalNested, canonicalNested) := literalType.consumeMData.headBeta.eq?
    | throwError "Native098 literal nested proof is not Eq3."
  unless carrier.consumeMData.equal v.carrier.consumeMData &&
      originalNested.consumeMData.equal v.originalNested.consumeMData &&
      canonicalNested.consumeMData.equal v.canonicalNested.consumeMData do
    throwError "Native098 original literal/generic Eq endpoints and carriers do not exactly raw join."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``Eq.trans [← getLevel carrier])
      #[carrier, originalNested, canonicalNested, v.composite, literalLaw, source])
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (actualCarrier, actualOriginal, actualComposite) := proofType.consumeMData.headBeta.eq?
    | throwError "Native098 actual literal composition assembly is not Eq3."
  unless actualCarrier.consumeMData.equal carrier.consumeMData &&
      actualOriginal.consumeMData.equal v.originalNested.consumeMData &&
      actualComposite.consumeMData.equal v.composite.consumeMData do
    throwError "Native098 ordinary composition assembly changed original literal/composite point vectors."
  logInfo "Native098 ordinary Eq.trans6 from two actual raw-matching carrier/point proofs yields literal original Stage0 NESTED RHS = SAME original f/g/G/Phi/E mapped composite; no original coefficient/formula or public aggregation."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalLiteralNestedCompositionEqOwn098
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_nested_composition098%
      (actualOriginalGlobalPhiNativeOriginalNestedCompositionOwn097 p hp P hP s)
      using_literal (actualOriginalGlobalPhiNativeOriginalNestedPointEqOwn098 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_nested_composition098%
    (actualOriginalGlobalPhiNativeOriginalNestedCompositionOwn097 p hp P hP s)
    using_literal (actualOriginalGlobalPhiNativeOriginalNestedPointEqOwn098 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

/-- Independently apply existing comp_apply to ONLY the real original
producer formula's exact comp21 vector and SAME original Phi. No coefficient
coercion endpoint or native output type is imposed on this own-vector law. -/
elab "phi_native_original_formula_comp088% " supplied:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalProducerFormulaOwn083 &&
      source.getAppArgs.size == 8 do
    throwError "Native088 composition requires only passed exact existing producer formula083."
  let body ← phiNativeCoefficientBody087 nativeProp
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native088 refuses different original composition/section/scalar arguments."
  let some (_, coefficient, _) := body.consumeMData.headBeta.eq?
    | throwError "Native088 requires original stage0 coefficient."
  let coefficient := coefficient.consumeMData.headBeta
  let pa := coefficient.getAppArgs
  unless coefficient.getAppFn.isConstOf ``DFunLike.coe && pa.size == 6 do
    throwError "Native088 composition requires original coefficient coe6/Phi."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (_, producer, composition) := sourceType.consumeMData.headBeta.eq?
    | throwError "Native088 requires actual existing producer formula Eq3."
  unless producer.getAppFn.isConstOf ``actualCubicPositiveTwoChartContractedNativeDifferentialMap &&
      producer.getAppArgs.size == 11 do
    throwError "Native088 refuses a replacement producer."
  let ca := composition.getAppArgs
  let .const compName compLevels := composition.getAppFn
    | throwError "Native088 requires stored composition constant application."
  unless compName == ``LinearMap.comp && ca.size == 21 do
    throwError "Native088 requires exact existing formula composition21."
  let compInfo ← getConstInfo ``LinearMap.comp
  let lawInfo ← getConstInfo ``LinearMap.comp_apply
  unless compInfo.levelParams.length == compLevels.length &&
      lawInfo.levelParams.length == compLevels.length do
    throwError "Native088 comp/comp_apply universe counts differ."
  let mut compType := compInfo.instantiateTypeLevelParams compLevels
  let mut lawType := lawInfo.instantiateTypeLevelParams compLevels
  for i in [:21] do
    let .forallE _ compDomain compBody compBinder := compType
      | throwError "Native088 exact comp prefix ended early."
    let .forallE _ lawDomain lawBody lawBinder := lawType
      | throwError "Native088 exact comp_apply prefix ended early."
    unless compBinder == lawBinder && compDomain.consumeMData.equal lawDomain.consumeMData do
      throwError "Native088 comp_apply changes a stored original composition binder."
    compType := compBody.instantiate1 ca[i]!
    lawType := lawBody.instantiate1 ca[i]!
  let .forallE _ pointDomain _ _ := lawType
    | throwError "Native088 stored comp_apply lacks its final point binder."
  unless pointDomain.consumeMData.equal ca[3]!.consumeMData do
    throwError "Native088 comp_apply point domain is not the stored composition M1 vector."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``LinearMap.comp_apply compLevels) (ca.push pa[5]!))
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (_, actualLeft, _) := proofType.consumeMData.headBeta.eq?
    | throwError "Native088 exact comp_apply did not return Eq3."
  let actualLeft := actualLeft.consumeMData.headBeta
  let la := actualLeft.getAppArgs
  unless actualLeft.getAppFn.isConstOf ``DFunLike.coe && la.size == 6 &&
      la[4]!.consumeMData.equal composition.consumeMData &&
      la[5]!.consumeMData.equal pa[5]!.consumeMData do
    throwError "Native088 actual comp_apply changed stored original composition/Phi values."
  logInfo "Native088 existing comp_apply consumes full original comp21 plus SAME original Phi; universe/prefix/M1/function/input vectors raw guarded. Own output/coercion type remains inferred, not replaced by native coefficient type."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalFormulaCompOwn088
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_formula_comp088%
      (actualOriginalGlobalPhiNativeOriginalProducerFormulaOwn083 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_formula_comp088%
    (actualOriginalGlobalPhiNativeOriginalProducerFormulaOwn083 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

universe nativeScalarR099 nativeScalarS099 nativeModuleM099 nativeModuleN099

/-- Generic evaluation of the SAME semilinear equivalence as its linear map.
The argument order matches the exact structure parameter vector. -/
private theorem phiNativeOriginalEquivLinearPoint099
    {R : Type nativeScalarR099} {S : Type nativeScalarS099}
    [Semiring R] [Semiring S] (σ : R →+* S) {σ' : S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type nativeModuleM099) (N : Type nativeModuleN099)
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
    (e : M ≃ₛₗ[σ] N) (x : M) : e.toLinearMap x = e x := rfl

meta section
open Lean Meta Elab Term

/-- Isolate ONLY the linear-equivalence evaluation projection of the actual
passed comp_apply088 RHS, using its own stored fifteen-argument vector. -/
elab "phi_native_original_formula_equiv099% " supplied:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalFormulaCompOwn088 &&
      source.getAppArgs.size == 8 do
    throwError "Native099 requires only passed original formula comp_apply088."
  let _ ← phiNativeCoefficientBody087 nativeProp
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native099 refuses formula equivalence evaluation on different original arguments."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (carrier, _, formulaRight) := sourceType.consumeMData.headBeta.eq?
    | throwError "Native099 requires actual original comp_apply Eq3."
  let formulaRight := formulaRight.consumeMData.headBeta
  let ea := formulaRight.getAppArgs
  unless formulaRight.getAppFn.isConstOf ``DFunLike.coe && ea.size == 6 do
    throwError "Native099 requires actual formula outer linear evaluation coe6."
  let projection ← phiNativeNoRecovery025
    (← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.projectionAsApplication ea[4]!)
  let .const projectionName projectionLevels := projection.getAppFn
    | throwError "Native099 requires declared original linear-equivalence projection."
  let args := projection.getAppArgs
  unless projectionName == ``LinearEquiv.toLinearMap && args.size == 15 do
    throwError "Native099 refuses a different actual E projection: {projectionName}/{args.size}."
  let resolved ← phiNativeNoRecovery025
    (← mkAppOptM ``phiNativeOriginalEquivLinearPoint099 ((args.push ea[5]!).map some))
  let .const lawName lawLevels := resolved.getAppFn
    | throwError "Native099 cannot recover existing generic evaluation universe vector."
  unless lawName == ``phiNativeOriginalEquivLinearPoint099 do
    throwError "Native099 refuses a replacement equivalence law."
  let projectionInfo ← getConstInfo ``LinearEquiv.toLinearMap
  let lawInfo ← getConstInfo ``phiNativeOriginalEquivLinearPoint099
  unless projectionInfo.levelParams.length == projectionLevels.length &&
      lawInfo.levelParams.length == lawLevels.length do
    throwError "Native099 exact projection/evaluation universe counts differ."
  let mut projectionType := projectionInfo.instantiateTypeLevelParams projectionLevels
  let mut lawType := lawInfo.instantiateTypeLevelParams lawLevels
  for i in [:15] do
    let .forallE _ projectionDomain projectionBody _ := projectionType
      | throwError "Native099 original projection parameter prefix ended early."
    let .forallE _ lawDomain lawBody _ := lawType
      | throwError "Native099 generic evaluation parameter prefix ended early."
    unless projectionDomain.consumeMData.equal lawDomain.consumeMData do
      phiNativeJoinPath070 s!"formula099.projection-law-domain[{i}]" projectionDomain lawDomain
      throwError "Native099 generic evaluation changes an actual stored projection parameter domain."
    projectionType := projectionBody.instantiate1 args[i]!
    lawType := lawBody.instantiate1 args[i]!
  let .forallE _ pointDomain _ _ := lawType
    | throwError "Native099 generic evaluation lacks its final point binder."
  unless pointDomain.consumeMData.equal args[8]!.consumeMData do
    throwError "Native099 exact evaluation point domain is not original E source-module vector."
  let proof ← phiNativeNoRecovery025
    (mkAppN resolved.getAppFn (args.push ea[5]!))
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (actualCarrier, actualLeft, actualRight) := proofType.consumeMData.headBeta.eq?
    | throwError "Native099 own equivalence projection evaluation is not Eq3."
  let actualLeft := actualLeft.consumeMData.headBeta
  let actualRight := actualRight.consumeMData.headBeta
  unless actualLeft.consumeMData.equal formulaRight.consumeMData do
    phiNativeJoinPath070 "formula099.actual-linear-point-to-original-formula-RHS" actualLeft formulaRight
    throwError "Native099 refuses a different original formula linear evaluation endpoint."
  let ra := actualRight.getAppArgs
  unless actualRight.getAppFn.isConstOf ``DFunLike.coe && ra.size == 6 &&
      ra[4]!.consumeMData.equal args[14]!.consumeMData &&
      ra[5]!.consumeMData.equal ea[5]!.consumeMData do
    throwError "Native099 equivalence projection law changed original E or mapped point values."
  unless actualCarrier.consumeMData.headBeta.equal carrier.consumeMData.headBeta do
    phiNativeJoinPath070 "formula099.evaluation-own-output-to-formula-carrier" actualCarrier carrier
    throwError "Native099 equivalence evaluation output is not exact original comp_apply carrier."
  logInfo "Native099 generic rfl evaluation applied with all fifteen original E projection parameters plus SAME original mapped point; exact source endpoint/output/E/input and all parameter domains raw guarded. No mapped-composite compatibility aggregation."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalFormulaEquivPointEqOwn099
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_formula_equiv099%
      (actualOriginalGlobalPhiNativeOriginalFormulaCompOwn088 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_formula_equiv099%
    (actualOriginalGlobalPhiNativeOriginalFormulaCompOwn088 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

/-- Homogeneous map identity uses the source coefficient's OWN stored
DFunLike function type, never a reconstructed native map type or expected goal.
The original/producer values come only from the passed HEq083 certificate. -/
elab "phi_native_original_map_eq087% " supplied:term " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalProducerHEq083 &&
      source.getAppArgs.size == 8 do
    throwError "Native087 requires only passed original producer HEq083/eight-vector."
  let body ← phiNativeCoefficientBody087 nativeProp
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native087 refuses changed original map/section/scalar arguments."
  let some (_, originalPoint, _) := body.consumeMData.headBeta.eq?
    | throwError "Native087 requires exact original coefficient endpoint."
  let originalPoint := originalPoint.consumeMData.headBeta
  let pa := originalPoint.getAppArgs
  unless originalPoint.getAppFn.isConstOf ``DFunLike.coe && pa.size == 6 do
    throwError "Native087 requires exact original coefficient coercion6."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (_, nativeMap, _, producer) := sourceType.consumeMData.headBeta.heq?
    | throwError "Native087 requires actual passed original map HEq4."
  unless nativeMap.consumeMData.equal pa[4]!.consumeMData &&
      nativeMap.getAppFn.isConstOf ``actualOriginalPositiveTwoContractedNativeDifferentialMap &&
      producer.getAppFn.isConstOf ``actualCubicPositiveTwoChartContractedNativeDifferentialMap &&
      producer.getAppArgs.size == 11 do
    throwError "Native087 map certificate does not join exact original coefficient function vector."
  let mapType := pa[0]!
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``eq_of_heq [← getLevel mapType])
      #[mapType, nativeMap, producer, source])
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (actualType, actualNative, actualProducer) := proofType.consumeMData.headBeta.eq?
    | throwError "Native087 own-vector eq_of_heq did not return Eq3."
  unless actualType.consumeMData.equal mapType.consumeMData &&
      actualNative.consumeMData.equal nativeMap.consumeMData &&
      actualProducer.consumeMData.equal producer.consumeMData do
    throwError "Native087 ordinary map Eq changed source coercion type/original map/producer."
  logInfo "Native087 ordinary eq_of_heq consumes full four-vector using exact original coefficient coercion function type and passed map values; no coefficient evaluation or map_comp here."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalMapEqOwn087
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_map_eq087%
      (actualOriginalGlobalPhiNativeOriginalProducerHEq083 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_map_eq087%
    (actualOriginalGlobalPhiNativeOriginalProducerHEq083 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

/-- Only the existing exact producer formula's function TYPE is adapted to
the independently checked original coefficient coercion type. No evaluation. -/
elab "phi_native_original_formula_map088% " supplied:term " with_map " mapLaw:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let mapLaw ← phiNativeNoRecovery025 (← Term.elabTerm mapLaw none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalProducerFormulaOwn083 &&
      source.getAppArgs.size == 8 &&
      mapLaw.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalMapEqOwn087 &&
      mapLaw.getAppArgs.size == 8 do
    throwError "Native088 requires only exact existing formula083 and checked original map Eq087."
  let body ← phiNativeCoefficientBody087 nativeProp
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData &&
        mapLaw.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native088 refuses changed original formula/map/section/scalar arguments."
  let some (_, coefficient, _) := body.consumeMData.headBeta.eq?
    | throwError "Native088 requires exact original stage0 coefficient."
  let coefficient := coefficient.consumeMData.headBeta
  let pa := coefficient.getAppArgs
  unless coefficient.getAppFn.isConstOf ``DFunLike.coe && pa.size == 6 do
    throwError "Native088 requires exact original coefficient coe6."
  let mapType ← phiNativeNoRecovery025 (← whnf (← inferType mapLaw))
  let some (originalFunctionType, nativeMap, producer) := mapType.consumeMData.headBeta.eq?
    | throwError "Native088 requires checked original homogeneous map Eq3."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (formulaFunctionType, formulaLeft, formulaRight) := sourceType.consumeMData.headBeta.eq?
    | throwError "Native088 requires actual existing formula Eq3."
  unless originalFunctionType.consumeMData.equal pa[0]!.consumeMData &&
      nativeMap.consumeMData.equal pa[4]!.consumeMData &&
      producer.consumeMData.equal formulaLeft.consumeMData &&
      formulaRight.getAppFn.isConstOf ``LinearMap.comp && formulaRight.getAppArgs.size == 21 do
    throwError "Native088 formula/map producer values do not raw join the original coefficient vector."
  let expected := mkAppN (mkConst ``Eq [← getLevel originalFunctionType])
    #[originalFunctionType, formulaLeft, formulaRight]
  let proof ← phiNativeNoRecovery025 (mkAppN (mkConst ``id [Level.zero]) #[expected, source])
  let proofType ← phiNativeNoRecovery025 (← inferType proof)
  unless proofType.consumeMData.headBeta.equal expected.consumeMData.headBeta do
    throwError "Native088 ordinary formula type adapter changed exact original producer/composition."
  logInfo m!"Native088 exact formula function-type raw match={formulaFunctionType.consumeMData.equal originalFunctionType.consumeMData}; ordinary id certifies ONLY this existing formula on the original coefficient function type."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalFormulaMapOwn088
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_formula_map088%
      (actualOriginalGlobalPhiNativeOriginalProducerFormulaOwn083 p hp P hP s)
      with_map (actualOriginalGlobalPhiNativeOriginalMapEqOwn087 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_formula_map088%
    (actualOriginalGlobalPhiNativeOriginalProducerFormulaOwn083 p hp P hP s)
    with_map (actualOriginalGlobalPhiNativeOriginalMapEqOwn087 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

/-- Evaluate ONLY the separately certified formula Eq on the SAME original
Phi through all six original coefficient coercion arguments. -/
elab "phi_native_original_formula_point088% " supplied:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalFormulaMapOwn088 &&
      source.getAppArgs.size == 8 do
    throwError "Native088 requires only independently certified original formula map Eq088."
  let body ← phiNativeCoefficientBody087 nativeProp
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native088 refuses changed original formula evaluation arguments."
  let some (_, coefficient, _) := body.consumeMData.headBeta.eq?
    | throwError "Native088 requires exact original coefficient endpoint."
  let coefficient := coefficient.consumeMData.headBeta
  let pa := coefficient.getAppArgs
  unless coefficient.getAppFn.isConstOf ``DFunLike.coe && pa.size == 6 do
    throwError "Native088 requires original coefficient coe6."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (mapType, producer, composition) := sourceType.consumeMData.headBeta.eq?
    | throwError "Native088 requires original formula map Eq3."
  unless mapType.consumeMData.equal pa[0]!.consumeMData &&
      producer.getAppFn.isConstOf ``actualCubicPositiveTwoChartContractedNativeDifferentialMap &&
      producer.getAppArgs.size == 11 &&
      composition.getAppFn.isConstOf ``LinearMap.comp && composition.getAppArgs.size == 21 do
    throwError "Native088 formula source/type/composition is not the original checked vector."
  let outputCarrier ← phiNativeNoRecovery025 (← inferType coefficient)
  let outputCarrier := outputCarrier.consumeMData.headBeta
  let evaluator ← withLocalDeclD `originalFormulaMap mapType fun originalFormulaMap =>
    mkLambdaFVars #[originalFormulaMap]
      (mkAppN coefficient.getAppFn (pa.set! 4 originalFormulaMap))
  let evaluatorType ← phiNativeNoRecovery025 (← inferType evaluator)
  let .forallE _ domain codomain _ := evaluatorType.consumeMData
    | throwError "Native088 original formula evaluator did not retain function domain."
  unless domain.consumeMData.equal mapType.consumeMData &&
      (codomain.instantiate1 producer).consumeMData.headBeta.equal outputCarrier do
    throwError "Native088 formula evaluator changed original input/output carrier."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``congrArg [← getLevel mapType, ← getLevel outputCarrier])
      #[mapType, outputCarrier, producer, composition, evaluator, source])
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (actualCarrier, actualProducerPoint, actualCompositionPoint) := proofType.consumeMData.headBeta.eq?
    | throwError "Native088 exact formula evaluation did not return Eq3."
  let producerPoint := mkAppN coefficient.getAppFn (pa.set! 4 producer)
  let compositionPoint := mkAppN coefficient.getAppFn (pa.set! 4 composition)
  unless actualCarrier.consumeMData.equal outputCarrier.consumeMData &&
      actualProducerPoint.consumeMData.headBeta.equal producerPoint.consumeMData.headBeta &&
      actualCompositionPoint.consumeMData.headBeta.equal compositionPoint.consumeMData.headBeta do
    throwError "Native088 formula evaluation changed original Phi/coercion/map endpoint vectors."
  logInfo "Native088 ordinary full-six-vector congrArg evaluates only the checked original formula using same Phi and all other original coefficient coe6 arguments; no comp_apply or map_comp aggregation."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalFormulaPointOwn088
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_formula_point088%
      (actualOriginalGlobalPhiNativeOriginalFormulaMapOwn088 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_formula_point088%
    (actualOriginalGlobalPhiNativeOriginalFormulaMapOwn088 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

/-- Follow ONLY a diagnosed fixed argument spine using the already frozen
head/projection views. No proof value or geometric producer is unfolded. -/
private def phiNativeOriginalStoredBoundary100 (left0 right0 : Expr)
    (path : Array Nat) : MetaM (Expr × Expr) := do
  let mut left := left0.consumeMData.headBeta
  let mut right := right0.consumeMData.headBeta
  for i in path do
    left ← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.normalizeHead left 8
    right ← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.normalizeHead right 8
    left ← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.projectionAsApplication left
    right ← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.projectionAsApplication right
    let la := left.getAppArgs
    let ra := right.getAppArgs
    unless left.getAppFn.equal right.getAppFn && la.size == ra.size && decide (i < la.size) do
      throwError "Native100 diagnosed spine does not raw join at argument{i}: {left.getAppFn}/{la.size} versus {right.getAppFn}/{ra.size}."
    left := la[i]!.consumeMData.headBeta
    right := ra[i]!.consumeMData.headBeta
  return (left, right)

private def phiNativeOriginalPointBoundary100 (source other nativeProp : Expr)
    (fieldBoundary : Bool) : TermElabM (Expr × Expr) := do
  let expectedSource := if fieldBoundary then
    ``actualOriginalGlobalPhiNativeOriginalFormulaPointOwn088
    else ``actualOriginalGlobalPhiNativeOriginalFormulaEquivPointEqOwn099
  let expectedOther := if fieldBoundary then
    ``actualOriginalGlobalPhiNativeOriginalFormulaCompOwn088
    else ``actualOriginalGlobalPhiNativeOriginalNestedCompositionOwn097
  unless source.getAppFn.isConstOf expectedSource && other.getAppFn.isConstOf expectedOther &&
      source.getAppArgs.size == 8 && other.getAppArgs.size == 8 do
    throwError "Native100 requires only exact passed original formula/own point sources."
  let _ ← phiNativeCoefficientBody087 nativeProp
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData &&
        other.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native100 refuses boundary extraction on different original arguments."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (_, _, sourcePoint) := sourceType.consumeMData.headBeta.eq?
    | throwError "Native100 requires actual original source Eq3."
  let otherType ← phiNativeNoRecovery025 (← whnf (← inferType other))
  let some (_, otherLeft, otherRight) := otherType.consumeMData.headBeta.eq?
    | throwError "Native100 requires actual passed other Eq3."
  let otherPoint := if fieldBoundary then otherLeft else otherRight
  let path := if fieldBoundary then #[0, 6, 6, 4, 3]
    else #[5, 0, 6, 2, 5, 5, 3, 2, 4]
  phiNativeOriginalStoredBoundary100 sourcePoint otherPoint path

end

meta section
open Lean Meta Elab Term

/-- Literal original chart algebra projection at the ACTUAL composite frontier.
Same K/ChartRing/chartBaseMap five-vector checked before ordinary rfl proof. -/
elab "phi_native_original_composite_chart_prop100% " supplied:term " with_composite " compositeLaw:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let other ← phiNativeNoRecovery025 (← Term.elabTerm compositeLaw none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let (left, right) ← phiNativeOriginalPointBoundary100 source other nativeProp false
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless left.getAppFn.isConstOf ``Algebra.algebraMap && la.size == 5 &&
      right.getAppFn.isConstOf ``AllCharacteristics.HomogeneousProjective.chartBaseMap && ra.size == 5 do
    throwError "Native100 requires literal original Algebra.algebraMap5/chartBaseMap5 frontier."
  let chartRing := la[1]!.consumeMData.headBeta
  let chartArgs := chartRing.getAppArgs
  unless chartRing.getAppFn.isConstOf ``AllCharacteristics.HomogeneousProjective.ChartRing &&
      chartArgs.size == 5 && la[0]!.consumeMData.equal ra[0]!.consumeMData do
    throwError "Native100 chart projection is not SAME original K/ChartRing."
  for i in [:5] do
    unless chartArgs[i]!.consumeMData.equal ra[i]!.consumeMData do
      throwError "Native100 refuses different original ChartRing/chartBaseMap argument{i}."
  logInfo m!"Native100 actual composite chart projection SAME original five-vector verified; actual algebra dictionary={la[4]!}. Literal original endpoints retained for ordinary isolated rfl."
  return ← mkHEq left right

end

private lemma actualOriginalGlobalPhiNativeOriginalCompositeChartProjectionHEq100
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    phi_native_original_composite_chart_prop100%
      (actualOriginalGlobalPhiNativeOriginalFormulaEquivPointEqOwn099 p hp P hP s)
      with_composite (actualOriginalGlobalPhiNativeOriginalNestedCompositionOwn097 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0) := by
  rfl

meta section
open Lean Meta Elab Term

/-- Compare actual formula's equiv-view composite to actual own097 composite.
Only real original common-category/object certificates seed the frozen engine. -/
elab "phi_native_original_formula_composite100% " supplied:term " with_composite " compositeLaw:term
    " using_category " categoryLaw:term " using_object " objectLaw:term
    " using_projection " projectionLaw:term " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let compositeLaw ← phiNativeNoRecovery025 (← Term.elabTerm compositeLaw none (catchExPostpone := false))
  let categoryLaw ← phiNativeNoRecovery025 (← Term.elabTerm categoryLaw none (catchExPostpone := false))
  let objectLaw ← phiNativeNoRecovery025 (← Term.elabTerm objectLaw none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalFormulaEquivPointEqOwn099 &&
      compositeLaw.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalNestedCompositionOwn097 &&
      categoryLaw.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalCommonCategoryEqOwn096 &&
      objectLaw.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalCommonObjectEqOwn097 do
    throwError "Native100 requires only actual formula-equiv099/composite097/category096/object097 proofs."
  for proof in #[source, compositeLaw, categoryLaw, objectLaw] do
    unless proof.getAppArgs.size == 8 do
      throwError "Native100 requires complete original eight-argument proof vectors."
    for i in [:8] do
      unless proof.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
        throwError "Native100 refuses composite comparison on different original arguments."
  let original ← phiNativeOriginalNestedPointPair098 compositeLaw nativeProp
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (_, _, formulaComposite) := sourceType.consumeMData.headBeta.eq?
    | throwError "Native100 requires actual formula-equiv Eq3."
  let compositeType ← phiNativeNoRecovery025 (← whnf (← inferType compositeLaw))
  let some (_, _, ownComposite) := compositeType.consumeMData.headBeta.eq?
    | throwError "Native100 requires actual own generic composite Eq3."
  let formulaComposite := formulaComposite.consumeMData.headBeta
  let ownComposite := ownComposite.consumeMData.headBeta
  for endpoint in #[formulaComposite, ownComposite] do
    let ea := endpoint.getAppArgs
    unless endpoint.getAppFn.isConstOf ``DFunLike.coe && ea.size == 6 &&
        ea[4]!.getAppFn.isConstOf ``actualAffineSchemeDifferentialPointFiberEquiv do
      throwError "Native100 refuses replacement original affine E evaluation."
    let v ← phiNativePointVectors033 ea[5]!
    unless v.coeArgs[5]!.consumeMData.getAppFn.isConstOf ``actualOriginalGlobalCanonicalQuadraticPhi &&
        v.coeArgs[5]!.consumeMData.equal original.originalInner.coeArgs[5]!.consumeMData do
      throwError "Native100 refuses different original Phi in composite evaluation."
  let mut pairs : Array (Expr × Expr × Expr) := #[]
  for proof in #[categoryLaw, objectLaw] do
    let ty ← phiNativeNoRecovery025 (← whnf (← inferType proof))
    let some (_, l, r) := ty.consumeMData.headBeta.eq?
      | throwError "Native100 exact original category/object seed is not Eq3."
    let h ← phiNativeNoRecovery025 (← mkHEqOfEq proof)
    let reverse ← phiNativeNoRecovery025 (← mkHEqSymm h)
    pairs := pairs.push (l, r, h) |>.push (r, l, reverse)
  let projectionLaw ← phiNativeNoRecovery025 (← Term.elabTerm projectionLaw none (catchExPostpone := false))
  unless projectionLaw.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalCompositeChartProjectionHEq100 &&
      projectionLaw.getAppArgs.size == 8 do
    throwError "Native100 requires only actual original composite chart projection certificate100."
  for i in [:8] do
    unless projectionLaw.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native100 refuses chart certificate on different original arguments."
  let (projectionLeft, projectionRight) ← phiNativeOriginalPointBoundary100 source compositeLaw nativeProp false
  let projectionType ← phiNativeNoRecovery025 (← whnf (← inferType projectionLaw))
  let some (_, actualProjectionLeft, _, actualProjectionRight) := projectionType.consumeMData.headBeta.heq?
    | throwError "Native100 literal chart projection certificate is not HEq4."
  unless actualProjectionLeft.consumeMData.equal projectionLeft.consumeMData &&
      actualProjectionRight.consumeMData.equal projectionRight.consumeMData do
    throwError "Native100 actual chart projection does not raw join literal composite frontier."
  let projectionReverse ← phiNativeNoRecovery025 (← mkHEqSymm projectionLaw)
  pairs := pairs.push (projectionLeft, projectionRight, projectionLaw)
    |>.push (projectionRight, projectionLeft, projectionReverse)
  let (certificate, state) ←
    (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.structuralHEq
      formulaComposite ownComposite 96 #[] "full142").run {pairs := pairs}
  let certificate ← phiNativeNoRecovery025 certificate
  let certificateType ← phiNativeNoRecovery025 (← whnf (← inferType certificate))
  let some (_, actualFormula, _, actualOwn) := certificateType.consumeMData.headBeta.heq?
    | throwError "Native100 formula/composite compatibility is not HEq4."
  unless actualFormula.consumeMData.equal formulaComposite.consumeMData &&
      actualOwn.consumeMData.equal ownComposite.consumeMData do
    throwError "Native100 formula/composite compatibility changed original evaluated endpoints."
  let formulaPointType ← phiNativeNoRecovery025 (← inferType formulaComposite)
  let ownPointType ← phiNativeNoRecovery025 (← inferType ownComposite)
  let formulaLevel ← getLevel formulaPointType
  unless formulaLevel == (← getLevel ownPointType) do
    throwError "Native100 actual formula/own composite point universes differ."
  let expected := mkAppN (mkConst ``HEq [formulaLevel])
    #[formulaPointType, formulaComposite, ownPointType, ownComposite]
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``id [Level.zero]) #[expected, certificate])
  let proofType ← phiNativeNoRecovery025 (← inferType proof)
  unless proofType.consumeMData.headBeta.equal expected.consumeMData.headBeta do
    throwError "Native100 composite certificate changed literal point TYPE endpoints."
  logInfo m!"Native100 formula equiv-view to actual own097 mapped composite HEq: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}; both actual point TYPES and literal endpoints retained, original category/object certificates only."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalFormulaCompositeHEqOwn100
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_formula_composite100%
      (actualOriginalGlobalPhiNativeOriginalFormulaEquivPointEqOwn099 p hp P hP s)
      with_composite (actualOriginalGlobalPhiNativeOriginalNestedCompositionOwn097 p hp P hP s)
      using_category (actualOriginalGlobalPhiNativeOriginalCommonCategoryEqOwn096 p hp P hP s)
      using_object (actualOriginalGlobalPhiNativeOriginalCommonObjectEqOwn097 p hp P hP s)
      using_projection (actualOriginalGlobalPhiNativeOriginalCompositeChartProjectionHEq100 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_formula_composite100%
    (actualOriginalGlobalPhiNativeOriginalFormulaEquivPointEqOwn099 p hp P hP s)
    with_composite (actualOriginalGlobalPhiNativeOriginalNestedCompositionOwn097 p hp P hP s)
    using_category (actualOriginalGlobalPhiNativeOriginalCommonCategoryEqOwn096 p hp P hP s)
    using_object (actualOriginalGlobalPhiNativeOriginalCommonObjectEqOwn097 p hp P hP s)
    using_projection (actualOriginalGlobalPhiNativeOriginalCompositeChartProjectionHEq100 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

universe nativeFieldProjection100

/-- The two diagnosed CommSemiring projections of ONE unchanged Field. -/
private theorem phiNativeOriginalFieldCommSemiringEq100
    {R : Type nativeFieldProjection100} (c : Field R) :
    @Semifield.toCommSemiring R (@Field.toSemifield R c) =
      @CommRing.toCommSemiring R (@Field.toCommRing R c) := rfl

meta section
open Lean Meta Elab Term

elab "phi_native_original_field_commsemiring100% " supplied:term " with_comp " compLaw:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let other ← phiNativeNoRecovery025 (← Term.elabTerm compLaw none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let (left, right) ← phiNativeOriginalPointBoundary100 source other nativeProp true
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless left.getAppFn.isConstOf ``Semifield.toCommSemiring && la.size == 2 &&
      right.getAppFn.isConstOf ``CommRing.toCommSemiring && ra.size == 2 do
    throwError "Native100 requires only literal diagnosed Semifield/CommRing CommSemiring projections."
  let semifieldParent := la[1]!.consumeMData.headBeta
  let commRingParent := ra[1]!.consumeMData.headBeta
  let fa := semifieldParent.getAppArgs
  let ca := commRingParent.getAppArgs
  unless semifieldParent.getAppFn.isConstOf ``Field.toSemifield && fa.size == 2 &&
      commRingParent.getAppFn.isConstOf ``Field.toCommRing && ca.size == 2 do
    throwError "Native100 requires actual original Field.toSemifield2/Field.toCommRing2 parents."
  unless la[0]!.consumeMData.equal ra[0]!.consumeMData &&
      la[0]!.consumeMData.equal fa[0]!.consumeMData &&
      ra[0]!.consumeMData.equal ca[0]!.consumeMData &&
      fa[1]!.consumeMData.equal ca[1]!.consumeMData do
    phiNativeJoinPath070 "field100.original-carriers" la[0]! ra[0]!
    phiNativeJoinPath070 "field100.original-field-parents" fa[1]! ca[1]!
    throwError "Native100 refuses different actual original field carrier/parent vectors."
  let .const _ levels := semifieldParent.getAppFn
    | throwError "Native100 requires actual original field universe vector."
  unless levels.length == 1 do
    throwError "Native100 refuses a different field projection universe count."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``phiNativeOriginalFieldCommSemiringEq100 levels) fa)
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (_, actualLeft, actualRight) := proofType.consumeMData.headBeta.eq?
    | throwError "Native100 ordinary field projection law is not Eq3."
  unless actualLeft.consumeMData.equal left.consumeMData &&
      actualRight.consumeMData.equal right.consumeMData do
    throwError "Native100 ordinary field law changed exact original CommSemiring projection endpoints."
  logInfo "Native100 ordinary Field CommSemiring diamond consumes SAME original actual carrier/Field vector; literal diagnosed projection endpoints raw guarded. No point/composition conversion aggregation."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalFieldCommSemiringEqOwn100
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_field_commsemiring100%
      (actualOriginalGlobalPhiNativeOriginalFormulaPointOwn088 p hp P hP s)
      with_comp (actualOriginalGlobalPhiNativeOriginalFormulaCompOwn088 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_field_commsemiring100%
    (actualOriginalGlobalPhiNativeOriginalFormulaPointOwn088 p hp P hP s)
    with_comp (actualOriginalGlobalPhiNativeOriginalFormulaCompOwn088 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

/-- Independent original coefficient-coercion composition point versus the
actual own comp_apply088 LHS. Composition/Phi values must exactly raw join. -/
elab "phi_native_original_formula_comp_point100% " supplied:term " with_comp " compLaw:term
    " using_field " fieldLaw:term " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let compLaw ← phiNativeNoRecovery025 (← Term.elabTerm compLaw none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalFormulaPointOwn088 &&
      compLaw.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalFormulaCompOwn088 &&
      source.getAppArgs.size == 8 && compLaw.getAppArgs.size == 8 do
    throwError "Native100 point comparison requires only actual passed formula-point/comp088 proofs."
  let _ ← phiNativeCoefficientBody087 nativeProp
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData &&
        compLaw.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native100 refuses composition point compatibility on different original arguments."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (_, _, originalPoint) := sourceType.consumeMData.headBeta.eq?
    | throwError "Native100 requires actual formula-point Eq3."
  let compType ← phiNativeNoRecovery025 (← whnf (← inferType compLaw))
  let some (_, ownPoint, _) := compType.consumeMData.headBeta.eq?
    | throwError "Native100 requires actual comp_apply Eq3."
  let originalPoint := originalPoint.consumeMData.headBeta
  let ownPoint := ownPoint.consumeMData.headBeta
  let oa := originalPoint.getAppArgs
  let ca := ownPoint.getAppArgs
  unless originalPoint.getAppFn.isConstOf ``DFunLike.coe && oa.size == 6 &&
      ownPoint.getAppFn.isConstOf ``DFunLike.coe && ca.size == 6 &&
      oa[4]!.getAppFn.isConstOf ``LinearMap.comp && oa[4]!.getAppArgs.size == 21 &&
      oa[4]!.consumeMData.equal ca[4]!.consumeMData &&
      oa[5]!.consumeMData.equal ca[5]!.consumeMData do
    throwError "Native100 refuses different original composition21 or Phi point values."
  let originalCarrier ← phiNativeNoRecovery025 (← inferType originalPoint)
  let ownCarrier ← phiNativeNoRecovery025 (← inferType ownPoint)
  let pointLevel ← getLevel originalCarrier
  unless pointLevel == (← getLevel ownCarrier) do
    throwError "Native100 actual coefficient/comp_apply point universes differ."
  let fieldLaw ← phiNativeNoRecovery025 (← Term.elabTerm fieldLaw none (catchExPostpone := false))
  unless fieldLaw.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalFieldCommSemiringEqOwn100 &&
      fieldLaw.getAppArgs.size == 8 do
    throwError "Native100 requires only exact original field CommSemiring certificate100."
  for i in [:8] do
    unless fieldLaw.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native100 refuses field certificate on different original arguments."
  let (fieldLeft, fieldRight) ← phiNativeOriginalPointBoundary100 source compLaw nativeProp true
  let fieldType ← phiNativeNoRecovery025 (← whnf (← inferType fieldLaw))
  let some (_, actualFieldLeft, actualFieldRight) := fieldType.consumeMData.headBeta.eq?
    | throwError "Native100 field projection certificate is not Eq3."
  unless actualFieldLeft.consumeMData.equal fieldLeft.consumeMData &&
      actualFieldRight.consumeMData.equal fieldRight.consumeMData do
    throwError "Native100 actual field certificate does not raw join literal point frontier."
  let fieldHEq ← phiNativeNoRecovery025 (← mkHEqOfEq fieldLaw)
  let fieldReverse ← phiNativeNoRecovery025 (← mkHEqSymm fieldHEq)
  let (certificate, state) ←
    (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.structuralHEq
      originalPoint ownPoint 96 #[] "full142").run
      { pairs := #[(fieldLeft, fieldRight, fieldHEq), (fieldRight, fieldLeft, fieldReverse)] }
  let certificate ← phiNativeNoRecovery025 certificate
  let certificateType ← phiNativeNoRecovery025 (← whnf (← inferType certificate))
  let some (_, actualOriginal, _, actualOwn) := certificateType.consumeMData.headBeta.heq?
    | throwError "Native100 coefficient/comp_apply point compatibility is not HEq4."
  unless actualOriginal.consumeMData.equal originalPoint.consumeMData &&
      actualOwn.consumeMData.equal ownPoint.consumeMData do
    throwError "Native100 composition point certificate changed original composition/Phi endpoints."
  let expected := mkAppN (mkConst ``HEq [pointLevel])
    #[originalCarrier, originalPoint, ownCarrier, ownPoint]
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``id [Level.zero]) #[expected, certificate])
  let proofType ← phiNativeNoRecovery025 (← inferType proof)
  unless proofType.consumeMData.headBeta.equal expected.consumeMData.headBeta do
    throwError "Native100 composition point certificate changed actual endpoint TYPE vectors."
  logInfo m!"Native100 original coefficient composition-coercion point to actual own comp_apply LHS HEq: native leaves={state.wrapperLeaves}, proof leaves={state.proofLeaves}, fallback proofs={state.fallbackProofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}; SAME raw composition21/Phi, both own actual carrier TYPES retained. No coefficient/formula chain aggregation."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalFormulaCompPointHEqOwn100
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_formula_comp_point100%
      (actualOriginalGlobalPhiNativeOriginalFormulaPointOwn088 p hp P hP s)
      with_comp (actualOriginalGlobalPhiNativeOriginalFormulaCompOwn088 p hp P hP s)
      using_field (actualOriginalGlobalPhiNativeOriginalFieldCommSemiringEqOwn100 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_formula_comp_point100%
    (actualOriginalGlobalPhiNativeOriginalFormulaPointOwn088 p hp P hP s)
    with_comp (actualOriginalGlobalPhiNativeOriginalFormulaCompOwn088 p hp P hP s)
    using_field (actualOriginalGlobalPhiNativeOriginalFieldCommSemiringEqOwn100 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)
meta section
open Lean Meta Elab Term

/-- Evaluate the independently checked map identity at the SAME original
Phi with ALL original six coercion arguments and complete congrArg vector. -/
elab "phi_native_original_map_point087% " supplied:term " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalMapEqOwn087 &&
      source.getAppArgs.size == 8 do
    throwError "Native087 requires only exact original map Eq own087/eight-vector."
  let body ← phiNativeCoefficientBody087 nativeProp
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native087 refuses changed original coefficient evaluation arguments."
  let some (_, originalPoint, _) := body.consumeMData.headBeta.eq?
    | throwError "Native087 requires exact original coefficient point."
  let originalPoint := originalPoint.consumeMData.headBeta
  let pa := originalPoint.getAppArgs
  unless originalPoint.getAppFn.isConstOf ``DFunLike.coe && pa.size == 6 do
    throwError "Native087 requires exact original coefficient coe6."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (mapType, nativeMap, producer) := sourceType.consumeMData.headBeta.eq?
    | throwError "Native087 requires exact original map Eq3."
  unless mapType.consumeMData.equal pa[0]!.consumeMData &&
      nativeMap.consumeMData.equal pa[4]!.consumeMData do
    throwError "Native087 map Eq does not join exact original coercion type/function vectors."
  let outputCarrier ← phiNativeNoRecovery025 (← inferType originalPoint)
  let outputCarrier := outputCarrier.consumeMData.headBeta
  let evaluator ← withLocalDeclD `originalMap mapType fun originalMap =>
    mkLambdaFVars #[originalMap]
      (mkAppN originalPoint.getAppFn (pa.set! 4 originalMap))
  let evaluatorType ← phiNativeNoRecovery025 (← inferType evaluator)
  let .forallE _ domain codomain _ := evaluatorType.consumeMData
    | throwError "Native087 original coefficient evaluator did not retain its function type."
  unless domain.consumeMData.equal mapType.consumeMData &&
      (codomain.instantiate1 nativeMap).consumeMData.headBeta.equal outputCarrier do
    throwError "Native087 evaluator changed original coefficient input/output carrier."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``congrArg [← getLevel mapType, ← getLevel outputCarrier])
      #[mapType, outputCarrier, nativeMap, producer, evaluator, source])
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (actualCarrier, actualNative, actualProducer) := proofType.consumeMData.headBeta.eq?
    | throwError "Native087 coefficient evaluation did not return Eq3."
  let expectedProducer := mkAppN originalPoint.getAppFn (pa.set! 4 producer)
  unless actualCarrier.consumeMData.equal outputCarrier.consumeMData &&
      actualNative.consumeMData.headBeta.equal originalPoint &&
      actualProducer.consumeMData.headBeta.equal expectedProducer.consumeMData.headBeta do
    throwError "Native087 ordinary congrArg changed exact original Phi/coercion/map endpoint vectors."
  logInfo "Native087 ordinary six-vector congrArg evaluates original map identity at SAME original Phi, preserving all original coercion/scalar/point arguments; no formula/map_comp aggregation."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalMapPointOwn087
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_map_point087%
      (actualOriginalGlobalPhiNativeOriginalMapEqOwn087 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_map_point087%
    (actualOriginalGlobalPhiNativeOriginalMapEqOwn087 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

universe nativeStagePoint102

/-- Ordinary typed transport through seven independently checked point links.
All eight carrier types are separate; no homogeneous carrier hypothesis. -/
private theorem phiNativeOriginalSevenHEqLinks102
    {A0 A1 A2 A3 A4 A5 A6 A7 : Sort nativeStagePoint102}
    (x0 : A0) (x1 : A1) (x2 : A2) (x3 : A3)
    (x4 : A4) (x5 : A5) (x6 : A6) (x7 : A7)
    (h01 : HEq x0 x1) (h12 : HEq x1 x2) (h23 : HEq x2 x3)
    (h34 : HEq x3 x4) (h45 : HEq x4 x5) (h56 : HEq x5 x6)
    (h67 : HEq x6 x7) : HEq x0 x7 :=
  HEq.trans h01 (HEq.trans h12 (HEq.trans h23
    (HEq.trans h34 (HEq.trans h45 (HEq.trans h56 h67)))))

meta section
open Lean Meta Elab Term

private structure PhiNativeOriginalStageChain102 where
  level : Level
  types : Array Expr
  points : Array Expr
  proofs : Array Expr

/-- Prepare only exact actual stored endpoint vectors. Ordinary id checks
beta views of each link; no geometric map/carrier/instance is unfolded. -/
private def phiNativeOriginalStageChain102 (sources : Array Expr)
    (nativeProp : Expr) : TermElabM PhiNativeOriginalStageChain102 := do
  let expectedNames := #[``actualOriginalGlobalPhiNativeOriginalMapPointOwn087,
    ``actualOriginalGlobalPhiNativeOriginalFormulaPointOwn088,
    ``actualOriginalGlobalPhiNativeOriginalFormulaCompPointHEqOwn100,
    ``actualOriginalGlobalPhiNativeOriginalFormulaCompOwn088,
    ``actualOriginalGlobalPhiNativeOriginalFormulaEquivPointEqOwn099,
    ``actualOriginalGlobalPhiNativeOriginalFormulaCompositeHEqOwn100,
    ``actualOriginalGlobalPhiNativeOriginalLiteralNestedCompositionEqOwn098]
  unless sources.size == 7 do
    throwError "Native102 requires exactly the seven original independently checked link proofs."
  let body ← phiNativeCoefficientBody087 nativeProp
  let some (_, originalCoefficient, originalNested) := body.consumeMData.headBeta.eq?
    | throwError "Native102 requires exact literal original Stage0 body Eq3."
  let mut types : Array Expr := #[]
  let mut points : Array Expr := #[]
  let mut proofs : Array Expr := #[]
  let mut actualLevel : Option Level := none
  for i in [:7] do
    let source ← phiNativeNoRecovery025 sources[i]!
    unless source.getAppFn.isConstOf expectedNames[i]! && source.getAppArgs.size == 8 do
      throwError "Native102 refuses a different original point-link root/eight-vector at stage{i}."
    for j in [:8] do
      unless source.getAppArgs[j]!.consumeMData.equal nativeProp.getAppArgs[j]!.consumeMData do
        throwError "Native102 refuses changed original coefficient/Phi/map/scalar arguments."
    let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
    let link ← match sourceType.consumeMData.headBeta.eq? with
      | some (carrier, left, right) => do
        let h ← if i == 6 then
          phiNativeNoRecovery025 (mkAppN (mkConst ``Eq.symm [← getLevel carrier])
            #[carrier, left, right, source])
          else pure source
        phiNativeNoRecovery025 (← mkHEqOfEq h)
      | none => do
        unless i == 2 || i == 5 do
          throwError "Native102 expected original ordinary Eq link at stage{i}."
        unless sourceType.consumeMData.headBeta.heq?.isSome do
          throwError "Native102 expected actual genuine HEq link at stage{i}."
        pure source
    let linkType ← phiNativeNoRecovery025 (← whnf (← inferType link))
    let some (leftType, left, rightType, right) := linkType.consumeMData.headBeta.heq?
      | throwError "Native102 actual converted link is not HEq4."
    let leftType := leftType.consumeMData.headBeta
    let rightType := rightType.consumeMData.headBeta
    let left := left.consumeMData.headBeta
    let right := right.consumeMData.headBeta
    let level ← getLevel leftType
    unless level == (← getLevel rightType) do
      throwError "Native102 actual original link point universes differ at stage{i}."
    if let some oldLevel := actualLevel then
      unless oldLevel == level do
        throwError "Native102 refuses different original point universes across links."
    else
      actualLevel := some level
    let expected := mkAppN (mkConst ``HEq [level]) #[leftType, left, rightType, right]
    let link ← phiNativeNoRecovery025
      (mkAppN (mkConst ``id [Level.zero]) #[expected, link])
    let actualType ← phiNativeNoRecovery025 (← inferType link)
    unless actualType.consumeMData.headBeta.equal expected.consumeMData.headBeta do
      throwError "Native102 ordinary beta-view adapter changed an actual typed link."
    if i == 0 then
      unless left.consumeMData.equal originalCoefficient.consumeMData.headBeta do
        phiNativeJoinPath070 "stage102.original-coefficient" left originalCoefficient
        throwError "Native102 first point is not literal original Stage0 coefficient."
      types := types.push leftType
      points := points.push left
    else
      let typeJoin := types[i]!.consumeMData.equal leftType.consumeMData
      let pointJoin := points[i]!.consumeMData.equal left.consumeMData
      logInfo m!"Native102 actual stage{i-1}→{i} raw join: TYPE={typeJoin}, point={pointJoin}."
      unless typeJoin && pointJoin do
        phiNativeJoinPath070 s!"stage102.join[{i}].TYPE" types[i]! leftType
        phiNativeJoinPath070 s!"stage102.join[{i}].point" points[i]! left
        throwError "Native102 refuses an uncertified non-raw original typed point-link join."
    types := types.push rightType
    points := points.push right
    proofs := proofs.push link
  unless points[7]!.consumeMData.equal originalNested.consumeMData.headBeta do
    phiNativeJoinPath070 "stage102.original-nested-RHS" points[7]! originalNested
    throwError "Native102 final point is not literal original Stage0 nested RHS."
  let some level := actualLevel
    | throwError "Native102 original point universe vector missing."
  unless types.size == 8 && points.size == 8 && proofs.size == 7 do
    throwError "Native102 ordinary original typed chain has wrong vector lengths."
  return ⟨level, types, points, proofs⟩

elab "phi_native_original_stage0_chain102% " mapLaw:term " using_formula " formulaLaw:term
    " using_comp_point " compPointLaw:term " using_comp " compLaw:term
    " using_equiv " equivLaw:term " using_composite " compositeLaw:term
    " using_literal " literalLaw:term " with_native " nativeProp:term : term => do
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let mut sources : Array Expr := #[]
  for supplied in #[mapLaw, formulaLaw, compPointLaw, compLaw, equivLaw, compositeLaw, literalLaw] do
    sources := sources.push (← phiNativeNoRecovery025
      (← Term.elabTerm supplied none (catchExPostpone := false)))
  let v ← phiNativeOriginalStageChain102 sources nativeProp
  let info ← getConstInfo ``phiNativeOriginalSevenHEqLinks102
  unless info.levelParams.length == 1 do
    throwError "Native102 generic typed seven-link universe count differs."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``phiNativeOriginalSevenHEqLinks102 [v.level])
      (v.types ++ v.points ++ v.proofs))
  let expected := mkAppN (mkConst ``HEq [v.level])
    #[v.types[0]!, v.points[0]!, v.types[7]!, v.points[7]!]
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  unless proofType.consumeMData.headBeta.equal expected.consumeMData.headBeta do
    throwError "Native102 ordinary full23-vector chain changed original typed endpoints."
  logInfo "Native102 ordinary full23-vector seven-HEq chain yields exact literal original coefficient HEq original Stage0 nested RHS; all six adjacent TYPE/value joins raw and each beta view ordinarily certified. No factory/header conversion or geometric checker aggregation."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalStage0HEqOwn102
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_stage0_chain102%
      (actualOriginalGlobalPhiNativeOriginalMapPointOwn087 p hp P hP s)
      using_formula (actualOriginalGlobalPhiNativeOriginalFormulaPointOwn088 p hp P hP s)
      using_comp_point (actualOriginalGlobalPhiNativeOriginalFormulaCompPointHEqOwn100 p hp P hP s)
      using_comp (actualOriginalGlobalPhiNativeOriginalFormulaCompOwn088 p hp P hP s)
      using_equiv (actualOriginalGlobalPhiNativeOriginalFormulaEquivPointEqOwn099 p hp P hP s)
      using_composite (actualOriginalGlobalPhiNativeOriginalFormulaCompositeHEqOwn100 p hp P hP s)
      using_literal (actualOriginalGlobalPhiNativeOriginalLiteralNestedCompositionEqOwn098 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_stage0_chain102%
    (actualOriginalGlobalPhiNativeOriginalMapPointOwn087 p hp P hP s)
    using_formula (actualOriginalGlobalPhiNativeOriginalFormulaPointOwn088 p hp P hP s)
    using_comp_point (actualOriginalGlobalPhiNativeOriginalFormulaCompPointHEqOwn100 p hp P hP s)
    using_comp (actualOriginalGlobalPhiNativeOriginalFormulaCompOwn088 p hp P hP s)
    using_equiv (actualOriginalGlobalPhiNativeOriginalFormulaEquivPointEqOwn099 p hp P hP s)
    using_composite (actualOriginalGlobalPhiNativeOriginalFormulaCompositeHEqOwn100 p hp P hP s)
    using_literal (actualOriginalGlobalPhiNativeOriginalLiteralNestedCompositionEqOwn098 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

/-- Extract only the passed owned HEq's literal actual TYPES and point values.
This uses the original Stage0 source, not an inferred carrier identity premise. -/
private def phiNativeOriginalStage0HEqVectors104 (source nativeProp : Expr) :
    TermElabM (Expr × Expr × Expr × Expr × Expr × Expr) := do
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalStage0HEqOwn102 &&
      source.getAppArgs.size == 8 do
    throwError "Native104 requires only actual passed original Stage0 HEq own102."
  let body ← phiNativeCoefficientBody087 nativeProp
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native104 refuses original type transport on different arguments."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (leftType, left, rightType, right) := sourceType.consumeMData.headBeta.heq?
    | throwError "Native104 actual owned Stage0 is not HEq4."
  let some (_, originalLeft, originalRight) := body.consumeMData.headBeta.eq?
    | throwError "Native104 original Stage0 body is not Eq3."
  unless left.consumeMData.headBeta.equal originalLeft.consumeMData.headBeta &&
      right.consumeMData.headBeta.equal originalRight.consumeMData.headBeta do
    throwError "Native104 refuses changed original literal coefficient/Phi/nested endpoints."
  for carrier in #[leftType, rightType] do
    unless carrier.getAppFn.isConstOf ``TensorProduct && carrier.getAppArgs.size == 8 do
      throwError "Native104 requires exact original tensor8 endpoint TYPES."
  return (sourceType, leftType, left, rightType, right, body)

/-- The exact stored five-vector type_eq_of_heq law certifies both ACTUAL
original tensor carrier TYPES. No alias/instance normalization is needed. -/
elab "phi_native_original_stage0_tensor_type104% " supplied:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let (proposition, leftType, left, rightType, right, _) ←
    phiNativeOriginalStage0HEqVectors104 source nativeProp
  let .const heqName levels := proposition.consumeMData.headBeta.getAppFn
    | throwError "Native104 requires exact original HEq universe head."
  let info ← getConstInfo ``type_eq_of_heq
  unless heqName == ``HEq && levels.length == 1 && info.levelParams.length == 1 do
    throwError "Native104 type_eq_of_heq original universe counts differ."
  let leftSort ← phiNativeNoRecovery025 (← inferType leftType)
  let rightSort ← phiNativeNoRecovery025 (← inferType rightType)
  let args := #[leftType, rightType, left, right, source]
  let expectedDomains := #[leftSort, rightSort, leftType, rightType, proposition]
  let mut lawType := info.instantiateTypeLevelParams levels
  for i in [:5] do
    let .forallE _ domain body _ := lawType
      | throwError "Native104 actual type_eq_of_heq prefix ended early."
    unless domain.consumeMData.equal expectedDomains[i]!.consumeMData do
      phiNativeJoinPath070 s!"stage104.type-law-domain[{i}]" domain expectedDomains[i]!
      throwError "Native104 type_eq_of_heq changes an actual stored original argument domain."
    lawType := body.instantiate1 args[i]!
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``type_eq_of_heq levels) args)
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (actualSort, actualLeftType, actualRightType) := proofType.consumeMData.headBeta.eq?
    | throwError "Native104 actual original tensor TYPE equality is not Eq3."
  unless actualSort.consumeMData.equal leftSort.consumeMData &&
      actualLeftType.consumeMData.equal leftType.consumeMData &&
      actualRightType.consumeMData.equal rightType.consumeMData do
    throwError "Native104 ordinary type equality changed actual original tensor TYPE endpoints."
  logInfo "Native104 ordinary type_eq_of_heq full5 vector certifies EXACT differing original tensor TYPES from passed literal point HEq102; all stored TYPE/value/universe/domain vectors raw guarded, no normalization or inferred identity assumption."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalStage0TensorTypeEq104
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_stage0_tensor_type104%
      (actualOriginalGlobalPhiNativeOriginalStage0HEqOwn102 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_stage0_tensor_type104%
    (actualOriginalGlobalPhiNativeOriginalStage0HEqOwn102 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

/-- Certify factory TYPE → actual owned RIGHT TYPE from the real accepted
TYPE equality, ONLY after the factory/owned LEFT TYPE whole raw join. -/
elab "phi_native_original_stage0_factory_tensor105% " supplied:term " using_type " typeLaw:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let typeLaw ← phiNativeNoRecovery025 (← Term.elabTerm typeLaw none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let (_, leftType, _, rightType, _, body) ← phiNativeOriginalStage0HEqVectors104 source nativeProp
  unless typeLaw.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalStage0TensorTypeEq104 &&
      typeLaw.getAppArgs.size == 8 do
    throwError "Native105 requires only passed exact original tensor TYPE equality104."
  for i in [:8] do
    unless typeLaw.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native105 refuses factory TYPE certificate on different original arguments."
  let typeLawType ← phiNativeNoRecovery025 (← whnf (← inferType typeLaw))
  let some (typeSort, actualLeft, actualRight) := typeLawType.consumeMData.headBeta.eq?
    | throwError "Native105 actual original tensor TYPE certificate is not Eq3."
  unless actualLeft.consumeMData.equal leftType.consumeMData &&
      actualRight.consumeMData.equal rightType.consumeMData do
    throwError "Native105 passed tensor equality does not raw join owned actual TYPES."
  let some (carrier, _, _) := body.consumeMData.headBeta.eq?
    | throwError "Native105 literal original factory body is not Eq3."
  let rawLeft := carrier.consumeMData.headBeta.equal leftType.consumeMData.headBeta
  let rawRight := carrier.consumeMData.headBeta.equal rightType.consumeMData.headBeta
  logInfo m!"Native105 actual original factory TYPE joins: ownedLEFT={rawLeft}, ownedRIGHT={rawRight}."
  unless rawLeft do
    phiNativeJoinPath070 "stage105.factory-carrier-to-actual-left-TYPE" carrier leftType
    throwError "Native105 refuses an uncertified non-raw whole original factory/LEFT TYPE join."
  let expected := mkAppN typeLawType.consumeMData.headBeta.getAppFn #[typeSort, carrier, rightType]
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``id [Level.zero]) #[expected, typeLaw])
  let proofType ← phiNativeNoRecovery025 (← inferType proof)
  unless proofType.consumeMData.headBeta.equal expected.consumeMData.headBeta do
    throwError "Native105 ordinary factory TYPE equality changed literal factory/right vectors."
  logInfo "Native105 exact ordinary accepted tensor equality now certifies ORIGINAL factory TYPE = owned RIGHT TYPE; whole factory/LEFT raw guarded, no alias/dictionary normalization or assumed carrier identity."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalStage0FactoryTensorTypeEq105
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_stage0_factory_tensor105%
      (actualOriginalGlobalPhiNativeOriginalStage0HEqOwn102 p hp P hP s)
      using_type (actualOriginalGlobalPhiNativeOriginalStage0TensorTypeEq104 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_stage0_factory_tensor105%
    (actualOriginalGlobalPhiNativeOriginalStage0HEqOwn102 p hp P hP s)
    using_type (actualOriginalGlobalPhiNativeOriginalStage0TensorTypeEq104 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

/-- Exact original factory/right TYPE join is carried by its separately
checked ordinary equality, with all literal TYPE certificate endpoints guarded. -/
private def phiNativeOriginalStage0HomogeneousProp105 (source typeLaw factoryLaw nativeProp : Expr) :
    TermElabM (Expr × Expr) := do
  let (sourceType, leftType, _, rightType, _, body) ←
    phiNativeOriginalStage0HEqVectors104 source nativeProp
  unless typeLaw.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalStage0TensorTypeEq104 &&
      typeLaw.getAppArgs.size == 8 do
    throwError "Native105 requires independently checked exact original tensor TYPE equality104."
  for i in [:8] do
    unless typeLaw.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native105 refuses actual tensor certificate on different original arguments."
  let typeLawType ← phiNativeNoRecovery025 (← whnf (← inferType typeLaw))
  let some (_, actualLeftType, actualRightType) := typeLawType.consumeMData.headBeta.eq?
    | throwError "Native105 tensor TYPE certificate is not Eq3."
  unless actualLeftType.consumeMData.equal leftType.consumeMData &&
      actualRightType.consumeMData.equal rightType.consumeMData do
    throwError "Native105 real tensor equality does not raw join actual owned TYPES."
  let some (carrier, left, right) := body.consumeMData.headBeta.eq?
    | throwError "Native105 literal original Stage0 body is not Eq3."
  unless factoryLaw.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalStage0FactoryTensorTypeEq105 &&
      factoryLaw.getAppArgs.size == 8 do
    throwError "Native105 requires independently checked exact factory/right TYPE equality105."
  for i in [:8] do
    unless factoryLaw.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native105 refuses factory TYPE proof on different original arguments."
  let factoryType ← phiNativeNoRecovery025 (← whnf (← inferType factoryLaw))
  let some (_, actualFactory, actualFactoryRight) := factoryType.consumeMData.headBeta.eq?
    | throwError "Native105 exact factory/right TYPE certificate is not Eq3."
  unless actualFactory.consumeMData.equal carrier.consumeMData &&
      actualFactoryRight.consumeMData.equal rightType.consumeMData do
    throwError "Native105 exact factory/right TYPE equality does not raw join original whole endpoints."
  let .const _ levels := sourceType.consumeMData.headBeta.getAppFn
    | throwError "Native105 original HEq lacks its exact universe head."
  let expected := mkAppN (mkConst ``HEq levels) #[carrier, left, carrier, right]
  return (sourceType, expected)

elab "phi_native_original_stage0_homogeneous_type105% " supplied:term " using_type " typeLaw:term
    " using_factory " factoryLaw:term " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let typeLaw ← phiNativeNoRecovery025 (← Term.elabTerm typeLaw none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let factoryLaw ← phiNativeNoRecovery025 (← Term.elabTerm factoryLaw none (catchExPostpone := false))
  let (sourceType, expected) ← phiNativeOriginalStage0HomogeneousProp105 source typeLaw factoryLaw nativeProp
  let typeLawType ← phiNativeNoRecovery025 (← whnf (← inferType typeLaw))
  let some (_, leftType, rightType) := typeLawType.consumeMData.headBeta.eq?
    | throwError "Native105 exact tensor certificate is not Eq3."
  let typeHEq ← phiNativeNoRecovery025 (← mkHEqOfEq typeLaw)
  let reverse ← phiNativeNoRecovery025 (← mkHEqSymm typeHEq)
  let factoryType ← phiNativeNoRecovery025 (← whnf (← inferType factoryLaw))
  let some (_, factoryCarrier, factoryRight) := factoryType.consumeMData.headBeta.eq?
    | throwError "Native105 exact factory TYPE certificate is not Eq3."
  let factoryHEq ← phiNativeNoRecovery025 (← mkHEqOfEq factoryLaw)
  let factoryReverse ← phiNativeNoRecovery025 (← mkHEqSymm factoryHEq)
  let (certificate, state) ←
    (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.structuralHEq
      sourceType expected 96 #[] "full142").run
        {pairs := #[(leftType, rightType, typeHEq), (rightType, leftType, reverse),
          (factoryCarrier, factoryRight, factoryHEq), (factoryRight, factoryCarrier, factoryReverse)]}
  let proof ← phiNativeNoRecovery025 (← mkEqOfHEq certificate)
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (sort, actualSource, actualExpected) := proofType.consumeMData.headBeta.eq?
    | throwError "Native105 ordinary homogeneous proposition equality is not Eq3."
  unless sort.consumeMData.equal (mkSort Level.zero) &&
      actualSource.consumeMData.equal sourceType.consumeMData &&
      actualExpected.consumeMData.equal expected.consumeMData do
    throwError "Native105 proposition transport changed actual original homogeneous endpoints/TYPES."
  logInfo m!"Native105 genuine homogeneous original Stage0 proposition TYPE equality: native={state.wrapperLeaves}, proof={state.proofLeaves}, fallback={state.fallbackProofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}; only accepted exact tensor TYPE equality seed, original literal points/factory carrier retained."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalStage0HomogeneousTypeEq105
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_stage0_homogeneous_type105%
      (actualOriginalGlobalPhiNativeOriginalStage0HEqOwn102 p hp P hP s)
      using_type (actualOriginalGlobalPhiNativeOriginalStage0TensorTypeEq104 p hp P hP s)
      using_factory (actualOriginalGlobalPhiNativeOriginalStage0FactoryTensorTypeEq105 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_stage0_homogeneous_type105%
    (actualOriginalGlobalPhiNativeOriginalStage0HEqOwn102 p hp P hP s)
    using_type (actualOriginalGlobalPhiNativeOriginalStage0TensorTypeEq104 p hp P hP s)
    using_factory (actualOriginalGlobalPhiNativeOriginalStage0FactoryTensorTypeEq105 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

elab "phi_native_original_stage0_homogeneous105% " supplied:term " using_type " typeLaw:term
    " using_prop " propLaw:term " using_factory " factoryLaw:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let typeLaw ← phiNativeNoRecovery025 (← Term.elabTerm typeLaw none (catchExPostpone := false))
  let propLaw ← phiNativeNoRecovery025 (← Term.elabTerm propLaw none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let factoryLaw ← phiNativeNoRecovery025 (← Term.elabTerm factoryLaw none (catchExPostpone := false))
  let (sourceType, expected) ← phiNativeOriginalStage0HomogeneousProp105 source typeLaw factoryLaw nativeProp
  unless propLaw.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalStage0HomogeneousTypeEq105 &&
      propLaw.getAppArgs.size == 8 do
    throwError "Native105 requires only checked actual original homogeneous proposition equality104."
  for i in [:8] do
    unless propLaw.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native105 refuses homogeneous proof on different original arguments."
  let propType ← phiNativeNoRecovery025 (← whnf (← inferType propLaw))
  let some (_, actualSource, actualExpected) := propType.consumeMData.headBeta.eq?
    | throwError "Native105 homogeneous proposition certificate is not Eq3."
  unless actualSource.consumeMData.equal sourceType.consumeMData &&
      actualExpected.consumeMData.equal expected.consumeMData do
    throwError "Native105 exact homogeneous proposition certificate does not raw join source/target."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``Eq.mp [Level.zero]) #[sourceType, expected, propLaw, source])
  unless (← inferType proof).consumeMData.equal expected.consumeMData do
    throwError "Native105 exact homogeneous Eq.mp changed literal original Stage0 points/TYPES."
  logInfo "Native105 ordinary Eq.mp4 transports owned HEq to EXACT original homogeneous factory-carrier HEq; all actual proposition endpoints raw guarded."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalStage0HomogeneousHEq105
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_stage0_homogeneous105%
      (actualOriginalGlobalPhiNativeOriginalStage0HEqOwn102 p hp P hP s)
      using_type (actualOriginalGlobalPhiNativeOriginalStage0TensorTypeEq104 p hp P hP s)
      using_prop (actualOriginalGlobalPhiNativeOriginalStage0HomogeneousTypeEq105 p hp P hP s)
      using_factory (actualOriginalGlobalPhiNativeOriginalStage0FactoryTensorTypeEq105 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_stage0_homogeneous105%
    (actualOriginalGlobalPhiNativeOriginalStage0HEqOwn102 p hp P hP s)
    using_type (actualOriginalGlobalPhiNativeOriginalStage0TensorTypeEq104 p hp P hP s)
    using_prop (actualOriginalGlobalPhiNativeOriginalStage0HomogeneousTypeEq105 p hp P hP s)
    using_factory (actualOriginalGlobalPhiNativeOriginalStage0FactoryTensorTypeEq105 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

elab "phi_native_original_stage0_body_eq105% " supplied:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalStage0HomogeneousHEq105 &&
      source.getAppArgs.size == 8 do
    throwError "Native105 requires independently checked exact original homogeneous HEq104."
  let body ← phiNativeCoefficientBody087 nativeProp
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native105 refuses literal original body Eq on different arguments."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let some (leftType, left, rightType, right) := sourceType.consumeMData.headBeta.heq?
    | throwError "Native105 actual homogeneous source is not HEq4."
  let some (carrier, originalLeft, originalRight) := body.consumeMData.headBeta.eq?
    | throwError "Native105 literal original body is not Eq3."
  unless leftType.consumeMData.equal rightType.consumeMData &&
      leftType.consumeMData.equal carrier.consumeMData &&
      left.consumeMData.equal originalLeft.consumeMData &&
      right.consumeMData.equal originalRight.consumeMData do
    throwError "Native105 refuses non-raw original homogeneous TYPE/carrier/point joins."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``eq_of_heq [← getLevel carrier]) #[carrier, left, right, source])
  unless (← inferType proof).consumeMData.equal body.consumeMData do
    throwError "Native105 ordinary Eq conversion changed exact original Stage0 body proposition."
  logInfo "Native105 full4-vector eq_of_heq produces EXACT original Stage0 factory body Eq; all carrier/TYPE/point vectors raw equal, no unchecked tensor conversion. Factory top-let restoration remains separate."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalStage0BodyEq105
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_stage0_body_eq105%
      (actualOriginalGlobalPhiNativeOriginalStage0HomogeneousHEq105 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)) :=
  phi_native_original_stage0_body_eq105%
    (actualOriginalGlobalPhiNativeOriginalStage0HomogeneousHEq105 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

/-- Restore ONLY the unchanged factory's twenty-three top lets and literal
Nat0 case to a proof of its exact original stored body. Ordinary id checks this
boundary alone; all actual geometric proposition compatibility is already cut. -/
elab "phi_native_original_stage0_factory106% " supplied:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeOriginalStage0BodyEq105 &&
      source.getAppArgs.size == 8 do
    throwError "Native106 requires only checked literal original Stage0 body105."
  let body ← phiNativeCoefficientBody087 nativeProp
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native106 refuses factory header restoration on different original arguments."
  let sourceType ← phiNativeNoRecovery025 (← inferType source)
  unless sourceType.consumeMData.equal body.consumeMData do
    throwError "Native106 source TYPE is not exact original twenty-three-let factory body."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``id [Level.zero]) #[nativeProp, source])
  let proofType ← phiNativeNoRecovery025 (← inferType proof)
  unless proofType.consumeMData.equal nativeProp.consumeMData do
    throwError "Native106 ordinary original factory header restoration changed original stage proposition."
  logInfo "Native106 ordinary id restores EXACT unchanged Stage0 factory/23 top lets/Nat0, literal body raw joined; no own carrier/geometric comparison aggregated."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalStage0Factory106
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    phiNativeOriginalCoefficientStageProp082 p hp P hP s 0 :=
  phi_native_original_stage0_factory106%
    (actualOriginalGlobalPhiNativeOriginalStage0BodyEq105 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 0)

meta section
open Lean Meta Elab Term

/-- Read the original fixed1–4 stage BODY only; same guarded23-let pathway
as the accepted stage0 reader, with no geometric subtree unfolding. -/
private def phiNativeOriginalStageBody111 (nativeProp : Expr) (stage : Nat) : TermElabM Expr := do
  unless stage > 0 do
    throwError "Native111 requires only original stages1–4."
  unless stage < 5 do
    throwError "Native111 requires only original stages1–4."
  unless nativeProp.getAppFn.isConstOf ``phiNativeOriginalCoefficientStageProp082 &&
      nativeProp.getAppArgs.size == 9 do
    throwError "Native111 requires exact original StageProp082/nine-vector."
  let storedStage ← phiNativeNoRecovery025 (← whnf nativeProp.getAppArgs[8]!)
  let .lit (.natVal actualStage) := storedStage.consumeMData
    | throwError "Native111 requires literal original fixed-stage Nat."
  unless actualStage == stage do
    throwError "Native111 refuses a different original stage."
  let some unfolded ← delta? nativeProp (fun n => n == ``phiNativeOriginalCoefficientStageProp082)
    | throwError "Native111 could not open exact original stage factory."
  let mut body := unfolded.consumeMData.headBeta
  let mut eliminated : Nat := 0
  for _ in [:23] do
    match body with
    | .letE _ _ value innerBody _ =>
      body := (innerBody.instantiate1 value).consumeMData.headBeta
      eliminated := eliminated + 1
    | _ => pure ()
  unless eliminated == 23 do
    throwError "Native111 requires exactly original23 stage context lets."
  let closedBody ← phiNativeNoRecovery025 (← whnf body)
  unless closedBody.consumeMData.headBeta.eq?.isSome do
    throwError "Native111 exact original fixed stage did not expose Eq3."
  return closedBody

/-- Inspect only598's diagnosed carrier spine and the existing real
field-semiring diamond's RIGHT endpoint; all original proof/type vectors stay
literal. No mathematical projection identity is assumed by this reader. -/
private def phiNativeOriginalStageRingPair111 (source nativeProp : Expr) :
    TermElabM (Expr × Expr) := do
  unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeContractionLiftOwn058 &&
      source.getAppArgs.size == 8 do
    throwError "Native111 requires only passed original contractionLiftOwn058/eight-vector."
  let body ← phiNativeOriginalStageBody111 nativeProp 1
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native111 refuses different original stage section/map/scalar vectors."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  let (leftSemiring, rightSemiring) ← phiNativeOriginalStoredBoundary100 sourceType body #[0, 4, 1]
  let leftSemiring ← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.normalizeHead leftSemiring 8
  let rightSemiring ← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.normalizeHead rightSemiring 8
  let (ordinaryRight, actualRingSide, reversed) ←
    match (← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.fieldSemiringLeaf146?
        leftSemiring rightSemiring) with
    | some (_, _, ordinaryRight) => pure (ordinaryRight, rightSemiring, false)
    | none =>
      let some (_, _, ordinaryRight) ←
          PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.fieldSemiringLeaf146?
            rightSemiring leftSemiring
        | throwError "Native111 refuses a pair not recognized by the existing real field-semiring diamond in either orientation."
      pure (ordinaryRight, leftSemiring, true)
  logInfo m!"Native111 actual closed-stage field-semiring orientation reversed={reversed}; selected source/factory expressions unchanged."
  let (leftRing, rightRing) ← phiNativeOriginalStoredBoundary100 ordinaryRight actualRingSide #[1, 1]
  let leftRing ← phiNativeNoRecovery025 leftRing
  let rightRing ← phiNativeNoRecovery025 rightRing
  unless leftRing.getAppFn.isConstOf ``Field.toCommRing && leftRing.getAppArgs.size == 2 &&
      rightRing.getAppFn.isConstOf ``CommRingCat.instCommRingObjForgetRingHomCarrier &&
      rightRing.getAppArgs.size == 1 do
    throwError "Native111 refuses another diagnosed original ring projection boundary."
  return (leftRing, rightRing)

/-- Exact existing native ring law on its stored S/x vector. Both actual
projection TYPES/VALUES are retained; ordinary id must certify the diagnosed
left-carrier alias compatibility, not a permissive raw guard. -/
private def phiNativeOriginalStageRingLaw111 (leftRing rightRing : Expr) :
    TermElabM Expr := do
  let field := leftRing.getAppArgs[1]!
  let .const fieldName levels := field.getAppFn
    | throwError "Native111 original residue Field is not a constant application."
  let fieldArgs := field.getAppArgs
  unless fieldName == ``AlgebraicGeometry.Scheme.instFieldCarrierResidueField &&
      fieldArgs.size == 2 && levels.length == 1 do
    throwError "Native111 requires exact original native residue Field/S/x/universe vector."
  let nativeLaw ← phiNativeNoRecovery025
    (mkAppN (mkConst ``PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Residue142.native_commRing_eq levels)
      fieldArgs)
  let nativeType ← phiNativeNoRecovery025 (← inferType nativeLaw)
  let some (_, nativeLeft, nativeRight) := nativeType.consumeMData.headBeta.eq?
    | throwError "Native111 existing original native ring law did not return Eq3."
  let nativeLeft ← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.normalizeHead nativeLeft 8
  let nativeRight ← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.normalizeHead nativeRight 8
  logInfo m!"Native111 actual LEFT ring HEAD={phiNativeJoinHead070 leftRing}; actual RIGHT ring HEAD={phiNativeJoinHead070 rightRing}."
  logInfo m!"Native111 actual LEFT carrier={leftRing.getAppArgs[0]!}; HEAD={phiNativeJoinHead070 leftRing.getAppArgs[0]!}."
  logInfo m!"Native111 actual native Field HEAD={phiNativeJoinHead070 field}; stored Scheme={fieldArgs[0]!}; stored point={fieldArgs[1]!}."
  logInfo m!"Native111 actual RIGHT native ring={rightRing.getAppArgs[0]!}; HEAD={phiNativeJoinHead070 rightRing.getAppArgs[0]!}."
  logInfo m!"Native111 canonical LEFT carrier={nativeLeft.getAppArgs[0]!}; HEAD={phiNativeJoinHead070 nativeLeft.getAppArgs[0]!}; canonical RIGHT ring={nativeRight.getAppArgs[0]!}; HEAD={phiNativeJoinHead070 nativeRight.getAppArgs[0]!}."
  logInfo m!"Native111 native LEFT Field raw={nativeLeft.getAppArgs[1]!.consumeMData.equal field.consumeMData}; WHOLE actual native RHS raw={nativeRight.consumeMData.equal rightRing.consumeMData}; LEFT carrier raw={leftRing.getAppArgs[0]!.consumeMData.equal nativeLeft.getAppArgs[0]!.consumeMData}."
  phiNativeJoinPath070 "stage111.pre-guard-left-carrier" leftRing.getAppArgs[0]! nativeLeft.getAppArgs[0]!
  phiNativeJoinPath070 "stage111.pre-guard-native-right" nativeRight rightRing
  unless nativeLeft.getAppFn.equal leftRing.getAppFn && nativeLeft.getAppArgs.size == 2 &&
      nativeLeft.getAppArgs[1]!.consumeMData.equal field.consumeMData &&
      nativeRight.consumeMData.equal rightRing.consumeMData do
    phiNativeJoinPath070 "stage111.native-left-field" nativeLeft leftRing
    phiNativeJoinPath070 "stage111.native-right-ring" nativeRight rightRing
    throwError "Native111 refuses an existing ring law on different original native Field/RHS vectors."
  logInfo m!"Native111 actual LEFT projection={leftRing}; actual RIGHT projection={rightRing}."
  logInfo m!"Native111 canonical native LEFT={nativeLeft}; canonical native RIGHT={nativeRight}."
  logInfo m!"Native111 same stored native Field=true; whole RHS raw=true; LEFT carrier raw={leftRing.getAppArgs[0]!.consumeMData.equal nativeLeft.getAppArgs[0]!.consumeMData}."
  phiNativeJoinPath070 "stage111.exact-left-carrier" leftRing.getAppArgs[0]! nativeLeft.getAppArgs[0]!
  let leftType ← phiNativeNoRecovery025 (← inferType leftRing)
  let rightType ← phiNativeNoRecovery025 (← inferType rightRing)
  let leftLevel ← getLevel leftType
  unless leftLevel == (← getLevel rightType) do
    throwError "Native111 actual original ring projection TYPE universes differ."
  let nativeHEq ← phiNativeNoRecovery025 (← mkHEqOfEq nativeLaw)
  let expected := mkAppN (mkConst ``HEq [leftLevel])
    #[leftType, leftRing, rightType, rightRing]
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``id [Level.zero]) #[expected, nativeHEq])
  unless (← inferType proof).consumeMData.equal expected.consumeMData do
    throwError "Native111 ordinary ring endpoint compatibility changed actual original TYPES/VALUES."
  logInfo "Native111 ordinary id on exact stored native_commRing_eq S/x certifies BOTH actual projection TYPES/VALUES; left carrier alias conversion is kernel checked in this independent declaration. No different native Field/RHS or assumed ring identity permitted."
  return proof

elab "phi_native_original_stage_ring111% " supplied:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let (leftRing, rightRing) ← phiNativeOriginalStageRingPair111 source nativeProp
  phiNativeOriginalStageRingLaw111 leftRing rightRing

elab "phi_native_original_stage_ring_diagnostic111% " supplied:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let (leftRing, rightRing) ← phiNativeOriginalStageRingPair111 source nativeProp
  logInfo m!"Native111 actual LEFT projection={leftRing}; actual TYPE={(← inferType leftRing)}."
  logInfo m!"Native111 actual RIGHT projection={rightRing}; actual TYPE={(← inferType rightRing)}."
  logInfo m!"Native111 LEFT carrier={leftRing.getAppArgs[0]!}; native Field vector={leftRing.getAppArgs[1]!}; actual RIGHT native ring={rightRing.getAppArgs[0]!}."
  return mkConst ``True.intro

end

private lemma actualOriginalGlobalPhiNativeStageResidueRingProjectionHEq111
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_stage_ring111%
      (actualOriginalGlobalPhiNativeContractionLiftOwn058 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 1)) :=
  phi_native_original_stage_ring111%
    (actualOriginalGlobalPhiNativeContractionLiftOwn058 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 1)

meta section
open Lean Meta Elab Term

/-- Compare only the original closed stage BODY against the independently
checked underlying link. This never enters108's different local alias context. -/
private def phiNativeOriginalClosedStagePair112 (stage : Nat) (source nativeProp : Expr) :
    TermElabM (Expr × Expr) := do
  unless stage > 0 do
    throwError "Native112 requires only original stages1–4."
  unless stage < 5 do
    throwError "Native112 requires only original stages1–4."
  let expectedNames := #[``actualOriginalGlobalPhiNativeContractionLiftOwn058,
    ``actualOriginalGlobalPhiNativeMappedReassociationLocalOwn059,
    ``actualOriginalGlobalPhiNativeDifferentialPointLiftOwn061,
    ``actualOriginalGlobalPhiNativeSectionPointEvaluationOwn081]
  unless source.getAppFn.isConstOf expectedNames[stage - 1]! && source.getAppArgs.size == 8 do
    throwError "Native112 requires exactly the checked underlying original named stage/eight-vector."
  let body ← phiNativeOriginalStageBody111 nativeProp stage
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native112 refuses closed-stage comparison on different original arguments."
  let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
  unless sourceType.consumeMData.headBeta.eq?.isSome do
    throwError "Native112 underlying original closed stage does not have Eq3 TYPE."
  return (sourceType, body)

/-- Extract only the real original ring projection values for THIS stage;
checked111 may seed it only after BOTH whole actual instance vectors raw join. -/
private def phiNativeOriginalClosedStageRingPair112 (sourceType body : Expr) :
    TermElabM (Expr × Expr) := do
  let (leftSemiring, rightSemiring) ← phiNativeOriginalStoredBoundary100 sourceType body #[0, 4, 1]
  let leftSemiring ← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.normalizeHead leftSemiring 8
  let rightSemiring ← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.normalizeHead rightSemiring 8
  let (ordinaryRight, actualRingSide) ←
    match (← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.fieldSemiringLeaf146?
        leftSemiring rightSemiring) with
    | some (_, _, ordinaryRight) => pure (ordinaryRight, rightSemiring)
    | none =>
      let some (_, _, ordinaryRight) ←
          PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.fieldSemiringLeaf146?
            rightSemiring leftSemiring
        | throwError "Native112 THIS original stage is not the checked real field-semiring diamond in either orientation."
      pure (ordinaryRight, leftSemiring)
  let (leftRing, rightRing) ← phiNativeOriginalStoredBoundary100 ordinaryRight actualRingSide #[1, 1]
  unless leftRing.getAppFn.isConstOf ``Field.toCommRing && leftRing.getAppArgs.size == 2 &&
      rightRing.getAppFn.isConstOf ``CommRingCat.instCommRingObjForgetRingHomCarrier &&
      rightRing.getAppArgs.size == 1 do
    throwError "Native112 refuses another original stage ring dictionary boundary."
  return (leftRing, rightRing)

end

universe nativeStageSemiring113

/-- Ordinary native residue ring projection and the same Field projection
 diamond, lifted to CommSemiring. No geometric map or coefficient enters it. -/
private theorem phiNativeResidueCommSemiringEq113
    (S : Scheme.{nativeStageSemiring113}) (x : S) :
    @CommRing.toCommSemiring (CommRingCat.carrier (S.residueField x))
      (@CommRingCat.instCommRingObjForgetRingHomCarrier (S.residueField x)) =
    @Semifield.toCommSemiring (CommRingCat.carrier (S.residueField x))
      (@Field.toSemifield (CommRingCat.carrier (S.residueField x))
        (Scheme.instFieldCarrierResidueField S x)) := by
  exact (congrArg
    (fun c : CommRing (CommRingCat.carrier (S.residueField x)) =>
      @CommRing.toCommSemiring (CommRingCat.carrier (S.residueField x)) c)
    (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Residue142.native_commRing_eq S x).symm).trans
      (phiNativeOriginalFieldCommSemiringEq100 (Scheme.instFieldCarrierResidueField S x)).symm

meta section
open Lean Meta Elab Term

/-- Only638's actual closed CommSemiring pair is read. Both projection
parents/own carrier vectors are preserved for the ordinary proof below. -/
private def phiNativeOriginalClosedStageCommSemiringPair113 (sourceType body : Expr) :
    TermElabM (Expr × Expr) := do
  let (left, right) ← phiNativeOriginalStoredBoundary100 sourceType body #[0, 6, 4, 3]
  let left ← phiNativeNoRecovery025
    (← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.normalizeHead left 8)
  let right ← phiNativeNoRecovery025
    (← PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.normalizeHead right 8)
  unless left.getAppFn.isConstOf ``CommRing.toCommSemiring && left.getAppArgs.size == 2 &&
      right.getAppFn.isConstOf ``Semifield.toCommSemiring && right.getAppArgs.size == 2 do
    throwError "Native113 requires only THIS diagnosed original CommRing/Semifield CommSemiring pair."
  return (left, right)

/-- Require the existing ring certificate's exact whole native parents and
all original argument vectors before any CommSemiring projection law is used. -/
private def phiNativeOriginalStageCommSemiringAnchors113
    (left right ringLaw nativeProp : Expr) : TermElabM (Expr × List Level) := do
  unless ringLaw.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeStageResidueRingProjectionHEq111 &&
      ringLaw.getAppArgs.size == 8 do
    throwError "Native113 requires only checked original ring projection111/eight-vector."
  for i in [:8] do
    unless ringLaw.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native113 refuses native ring111 on different original geometric/scalar/section arguments."
  let ringType ← phiNativeNoRecovery025 (← whnf (← inferType ringLaw))
  let some (_, ringField, _, ringNative) := ringType.consumeMData.headBeta.heq?
    | throwError "Native113 checked original ring111 certificate is not HEq4."
  let la := left.getAppArgs
  let ra := right.getAppArgs
  let semifield := ra[1]!.consumeMData.headBeta
  let fa := semifield.getAppArgs
  let .const fieldProjection levels := semifield.getAppFn
    | throwError "Native113 original semifield parent is not a constant application."
  unless fieldProjection == ``Field.toSemifield && fa.size == 2 && levels.length == 1 do
    throwError "Native113 requires exact original Field.toSemifield/carrier/Field/universe vector."
  let originalFieldRing := mkAppN (mkConst ``Field.toCommRing levels) fa
  unless la[1]!.consumeMData.equal ringNative.consumeMData &&
      originalFieldRing.consumeMData.equal ringField.consumeMData do
    phiNativeJoinPath070 "stage113.actual-native-ring-parent" la[1]! ringNative
    phiNativeJoinPath070 "stage113.actual-field-ring-parent" originalFieldRing ringField
    throwError "Native113 refuses a CommSemiring projection whose WHOLE original native/Field parents do not raw join111."
  let carriersRaw := la[0]!.consumeMData.equal ra[0]!.consumeMData &&
    ra[0]!.consumeMData.equal fa[0]!.consumeMData
  logInfo m!"Native113 original CommSemiring carrier joins={carriersRaw}; native/Field WHOLE parent joins=true."
  unless carriersRaw do
    phiNativeJoinPath070 "stage113.original-projection-carriers" la[0]! ra[0]!
    phiNativeJoinPath070 "stage113.original-field-carrier" ra[0]! fa[0]!
    throwError "Native113 refuses assumed equality of different actual native CommSemiring carriers."
  let field := fa[1]!
  let .const fieldName fieldLevels := field.getAppFn
    | throwError "Native113 actual original Field is not native residue Field constant."
  unless fieldName == ``Scheme.instFieldCarrierResidueField && field.getAppArgs.size == 2 &&
      fieldLevels == levels do
    throwError "Native113 requires exact native Scheme/point/Field universe vector."
  return (field, levels)

elab "phi_native_original_stage_commsemiring113% " supplied:term
    " using_ring " ringLaw:term " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let ringLaw ← phiNativeNoRecovery025 (← Term.elabTerm ringLaw none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let (sourceType, body) ← phiNativeOriginalClosedStagePair112 1 source nativeProp
  let (left, right) ← phiNativeOriginalClosedStageCommSemiringPair113 sourceType body
  let (field, levels) ← phiNativeOriginalStageCommSemiringAnchors113 left right ringLaw nativeProp
  let fieldArgs := field.getAppArgs
  logInfo m!"Native113 actual LEFT CommSemiring HEAD={phiNativeJoinHead070 left}; actual RIGHT HEAD={phiNativeJoinHead070 right}; original native Scheme={fieldArgs[0]!}; original point={fieldArgs[1]!}."
  let law ← phiNativeNoRecovery025
    (mkAppN (mkConst ``phiNativeResidueCommSemiringEq113 levels) fieldArgs)
  let lawType ← phiNativeNoRecovery025 (← inferType law)
  let some (_, nativeLeft, nativeRight) := lawType.consumeMData.headBeta.eq?
    | throwError "Native113 ordinary native CommSemiring projection law did not return Eq3."
  unless nativeLeft.consumeMData.equal left.consumeMData &&
      nativeRight.consumeMData.equal right.consumeMData do
    phiNativeJoinPath070 "stage113.actual-left-CommSemiring" nativeLeft left
    phiNativeJoinPath070 "stage113.actual-right-CommSemiring" nativeRight right
    throwError "Native113 native CommSemiring law does not RAW join both WHOLE actual original class endpoints."
  let leftType ← phiNativeNoRecovery025 (← inferType left)
  let rightType ← phiNativeNoRecovery025 (← inferType right)
  let leftLevel ← getLevel leftType
  unless leftLevel == (← getLevel rightType) do
    throwError "Native113 original CommSemiring TYPE universes differ."
  let expected := mkAppN (mkConst ``HEq [leftLevel]) #[leftType, left, rightType, right]
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``id [Level.zero]) #[expected, (← mkHEqOfEq law)])
  unless (← inferType proof).consumeMData.equal expected.consumeMData do
    throwError "Native113 ordinary projection HEq changed actual original own TYPES/VALUES."
  logInfo "Native113 genuine native CommSemiring projection HEq: BOTH whole endpoints and original ring111 parents raw joined; original own TYPES/VALUES retained, only exact stored S/x ordinary law, no carrier/map/scalar replacement."
  return proof

end

private lemma actualOriginalGlobalPhiNativeStageCommSemiringProjectionHEq113
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_stage_commsemiring113%
      (actualOriginalGlobalPhiNativeContractionLiftOwn058 p hp P hP s)
      using_ring (actualOriginalGlobalPhiNativeStageResidueRingProjectionHEq111 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 1)) :=
  phi_native_original_stage_commsemiring113%
    (actualOriginalGlobalPhiNativeContractionLiftOwn058 p hp P hP s)
    using_ring (actualOriginalGlobalPhiNativeStageResidueRingProjectionHEq111 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 1)

meta section
open Lean Meta Elab Term

elab "phi_native_original_closed_stage_type112% " stage:num supplied:term
    " using_ring " ringLaw:term " using_semiring " semiringLaw:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let ringLaw ← phiNativeNoRecovery025 (← Term.elabTerm ringLaw none (catchExPostpone := false))
  let semiringLaw ← phiNativeNoRecovery025 (← Term.elabTerm semiringLaw none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let (sourceType, body) ← phiNativeOriginalClosedStagePair112 stage.getNat source nativeProp
  unless ringLaw.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeStageResidueRingProjectionHEq111 &&
      ringLaw.getAppArgs.size == 8 do
    throwError "Native112 requires only actually checked original native ring projection111."
  for i in [:8] do
    unless ringLaw.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native112 refuses original ring111 on different geometric/scalar/section arguments."
  let ringType ← phiNativeNoRecovery025 (← whnf (← inferType ringLaw))
  let some (_, ringLeft, _, ringRight) := ringType.consumeMData.headBeta.heq?
    | throwError "Native112 actual ring111 certificate is not HEq4."
  let (actualLeft, actualRight) ← phiNativeOriginalClosedStageRingPair112 sourceType body
  unless ringLeft.consumeMData.equal actualLeft.consumeMData &&
      ringRight.consumeMData.equal actualRight.consumeMData do
    phiNativeJoinPath070 "stage112.actual-left-ring" ringLeft actualLeft
    phiNativeJoinPath070 "stage112.actual-right-ring" ringRight actualRight
    throwError "Native112 refuses ring111 seed whose WHOLE actual stage projection vectors do not raw join."
  let ringReverse ← phiNativeNoRecovery025 (← mkHEqSymm ringLaw)
  unless semiringLaw.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeStageCommSemiringProjectionHEq113 &&
      semiringLaw.getAppArgs.size == 8 do
    throwError "Native112 requires only checked actual original CommSemiring113/eight-vector."
  for i in [:8] do
    unless semiringLaw.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native112 refuses CommSemiring113 on different original scalar/point/section arguments."
  let semiringType ← phiNativeNoRecovery025 (← whnf (← inferType semiringLaw))
  let some (_, semiringLeft, _, semiringRight) := semiringType.consumeMData.headBeta.heq?
    | throwError "Native112 actual CommSemiring113 certificate is not HEq4."
  let (actualSemiringLeft, actualSemiringRight) ←
    phiNativeOriginalClosedStageCommSemiringPair113 sourceType body
  unless semiringLeft.consumeMData.equal actualSemiringLeft.consumeMData &&
      semiringRight.consumeMData.equal actualSemiringRight.consumeMData do
    phiNativeJoinPath070 "stage113.actual-left-CommSemiring-seed" semiringLeft actualSemiringLeft
    phiNativeJoinPath070 "stage113.actual-right-CommSemiring-seed" semiringRight actualSemiringRight
    throwError "Native112 refuses CommSemiring113 whose WHOLE actual THISstage class endpoints do not raw join."
  let _ ← phiNativeOriginalStageCommSemiringAnchors113 actualSemiringLeft actualSemiringRight ringLaw nativeProp
  let semiringReverse ← phiNativeNoRecovery025 (← mkHEqSymm semiringLaw)
  let (certificate, state) ←
    (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.structuralHEq
      sourceType body 96 #[] "full142").run
        {pairs := #[(ringLeft, ringRight, ringLaw), (ringRight, ringLeft, ringReverse),
          (semiringLeft, semiringRight, semiringLaw), (semiringRight, semiringLeft, semiringReverse)]}
  let proof ← phiNativeNoRecovery025 (← mkEqOfHEq certificate)
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (propositionSort, actualSource, actualBody) := proofType.consumeMData.headBeta.eq?
    | throwError "Native112 closed stage proposition comparison did not return Eq3."
  unless propositionSort.consumeMData.equal (mkSort Level.zero) &&
      actualSource.consumeMData.equal sourceType.consumeMData &&
      actualBody.consumeMData.equal body.consumeMData do
    throwError "Native112 proposition comparison changed original closed stage TYPE/endpoints."
  logInfo m!"Native112 closed original stage{stage.getNat} proposition Eq: ring111/CommSemiring113 full actual values raw joined; native={state.wrapperLeaves}, proof={state.proofLeaves}, fallback={state.fallbackProofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}. No108 local alias comparison and no changed map/scalar."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalStage1TypeEq112
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_closed_stage_type112% 1
      (actualOriginalGlobalPhiNativeContractionLiftOwn058 p hp P hP s)
      using_ring (actualOriginalGlobalPhiNativeStageResidueRingProjectionHEq111 p hp P hP s)
      using_semiring (actualOriginalGlobalPhiNativeStageCommSemiringProjectionHEq113 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 1)) :=
  phi_native_original_closed_stage_type112% 1
    (actualOriginalGlobalPhiNativeContractionLiftOwn058 p hp P hP s)
    using_ring (actualOriginalGlobalPhiNativeStageResidueRingProjectionHEq111 p hp P hP s)
    using_semiring (actualOriginalGlobalPhiNativeStageCommSemiringProjectionHEq113 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 1)

private lemma actualOriginalGlobalPhiNativeOriginalStage2TypeEq112
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_closed_stage_type112% 2
      (actualOriginalGlobalPhiNativeMappedReassociationLocalOwn059 p hp P hP s)
      using_ring (actualOriginalGlobalPhiNativeStageResidueRingProjectionHEq111 p hp P hP s)
      using_semiring (actualOriginalGlobalPhiNativeStageCommSemiringProjectionHEq113 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 2)) :=
  phi_native_original_closed_stage_type112% 2
    (actualOriginalGlobalPhiNativeMappedReassociationLocalOwn059 p hp P hP s)
    using_ring (actualOriginalGlobalPhiNativeStageResidueRingProjectionHEq111 p hp P hP s)
    using_semiring (actualOriginalGlobalPhiNativeStageCommSemiringProjectionHEq113 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 2)

private lemma actualOriginalGlobalPhiNativeOriginalStage3TypeEq112
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_closed_stage_type112% 3
      (actualOriginalGlobalPhiNativeDifferentialPointLiftOwn061 p hp P hP s)
      using_ring (actualOriginalGlobalPhiNativeStageResidueRingProjectionHEq111 p hp P hP s)
      using_semiring (actualOriginalGlobalPhiNativeStageCommSemiringProjectionHEq113 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 3)) :=
  phi_native_original_closed_stage_type112% 3
    (actualOriginalGlobalPhiNativeDifferentialPointLiftOwn061 p hp P hP s)
    using_ring (actualOriginalGlobalPhiNativeStageResidueRingProjectionHEq111 p hp P hP s)
    using_semiring (actualOriginalGlobalPhiNativeStageCommSemiringProjectionHEq113 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 3)

private lemma actualOriginalGlobalPhiNativeOriginalStage4TypeEq112
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_closed_stage_type112% 4
      (actualOriginalGlobalPhiNativeSectionPointEvaluationOwn081 p hp P hP s)
      using_ring (actualOriginalGlobalPhiNativeStageResidueRingProjectionHEq111 p hp P hP s)
      using_semiring (actualOriginalGlobalPhiNativeStageCommSemiringProjectionHEq113 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 4)) :=
  phi_native_original_closed_stage_type112% 4
    (actualOriginalGlobalPhiNativeSectionPointEvaluationOwn081 p hp P hP s)
    using_ring (actualOriginalGlobalPhiNativeStageResidueRingProjectionHEq111 p hp P hP s)
    using_semiring (actualOriginalGlobalPhiNativeStageCommSemiringProjectionHEq113 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 4)

meta section
open Lean Meta Elab Term

/-- Exact ordinary Eq.mp at the checked closed-stage proposition vectors;
no ring/carrier/map compatibility proof is recomputed here. -/
elab "phi_native_original_closed_stage_body112% " stage:num supplied:term
    " using_type " typeLaw:term " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let typeLaw ← phiNativeNoRecovery025 (← Term.elabTerm typeLaw none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let (sourceType, body) ← phiNativeOriginalClosedStagePair112 stage.getNat source nativeProp
  let expectedNames := #[``actualOriginalGlobalPhiNativeOriginalStage1TypeEq112,
    ``actualOriginalGlobalPhiNativeOriginalStage2TypeEq112,
    ``actualOriginalGlobalPhiNativeOriginalStage3TypeEq112,
    ``actualOriginalGlobalPhiNativeOriginalStage4TypeEq112]
  unless typeLaw.getAppFn.isConstOf expectedNames[stage.getNat - 1]! && typeLaw.getAppArgs.size == 8 do
    throwError "Native112 requires only independently checked THIS exact closed-stage proposition equality."
  for i in [:8] do
    unless typeLaw.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native112 refuses closed-stage Eq.mp on different original arguments."
  let typeLawType ← phiNativeNoRecovery025 (← whnf (← inferType typeLaw))
  let some (propositionSort, actualSource, actualBody) := typeLawType.consumeMData.headBeta.eq?
    | throwError "Native112 actual closed-stage TYPE certificate is not Eq3."
  unless propositionSort.consumeMData.equal (mkSort Level.zero) &&
      actualSource.consumeMData.equal sourceType.consumeMData &&
      actualBody.consumeMData.equal body.consumeMData do
    throwError "Native112 closed-stage Eq.mp requires exact stored source/body propositions."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``Eq.mp [Level.zero]) #[sourceType, body, typeLaw, source])
  unless (← inferType proof).consumeMData.equal body.consumeMData do
    throwError "Native112 ordinary Eq.mp changed literal original closed stage."
  logInfo m!"Native112 original closed stage{stage.getNat}: ordinary Eq.mp4 consumes independently checked TYPE equality; full propositions raw guarded, no repeated ring/map/carrier conversion."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalStage1BodyEq112
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_closed_stage_body112% 1
      (actualOriginalGlobalPhiNativeContractionLiftOwn058 p hp P hP s)
      using_type (actualOriginalGlobalPhiNativeOriginalStage1TypeEq112 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 1)) :=
  phi_native_original_closed_stage_body112% 1
    (actualOriginalGlobalPhiNativeContractionLiftOwn058 p hp P hP s)
    using_type (actualOriginalGlobalPhiNativeOriginalStage1TypeEq112 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 1)

private lemma actualOriginalGlobalPhiNativeOriginalStage2BodyEq112
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_closed_stage_body112% 2
      (actualOriginalGlobalPhiNativeMappedReassociationLocalOwn059 p hp P hP s)
      using_type (actualOriginalGlobalPhiNativeOriginalStage2TypeEq112 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 2)) :=
  phi_native_original_closed_stage_body112% 2
    (actualOriginalGlobalPhiNativeMappedReassociationLocalOwn059 p hp P hP s)
    using_type (actualOriginalGlobalPhiNativeOriginalStage2TypeEq112 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 2)

private lemma actualOriginalGlobalPhiNativeOriginalStage3BodyEq112
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_closed_stage_body112% 3
      (actualOriginalGlobalPhiNativeDifferentialPointLiftOwn061 p hp P hP s)
      using_type (actualOriginalGlobalPhiNativeOriginalStage3TypeEq112 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 3)) :=
  phi_native_original_closed_stage_body112% 3
    (actualOriginalGlobalPhiNativeDifferentialPointLiftOwn061 p hp P hP s)
    using_type (actualOriginalGlobalPhiNativeOriginalStage3TypeEq112 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 3)

private lemma actualOriginalGlobalPhiNativeOriginalStage4BodyEq112
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_original_closed_stage_body112% 4
      (actualOriginalGlobalPhiNativeSectionPointEvaluationOwn081 p hp P hP s)
      using_type (actualOriginalGlobalPhiNativeOriginalStage4TypeEq112 p hp P hP s)
      with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 4)) :=
  phi_native_original_closed_stage_body112% 4
    (actualOriginalGlobalPhiNativeSectionPointEvaluationOwn081 p hp P hP s)
    using_type (actualOriginalGlobalPhiNativeOriginalStage4TypeEq112 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 4)

meta section
open Lean Meta Elab Term

/-- Same ordinary restoration as passed106: only exact original factory,
23 top lets and fixed Nat case are restored from an exact literal BODY. -/
elab "phi_native_original_closed_stage_factory112% " stage:num supplied:term
    " with_native " nativeProp:term : term => do
  let source ← phiNativeNoRecovery025 (← Term.elabTerm supplied none (catchExPostpone := false))
  let nativeProp ← phiNativeNoRecovery025 (← Term.elabTerm nativeProp none (catchExPostpone := false))
  let body ← phiNativeOriginalStageBody111 nativeProp stage.getNat
  let expectedNames := #[``actualOriginalGlobalPhiNativeOriginalStage1BodyEq112,
    ``actualOriginalGlobalPhiNativeOriginalStage2BodyEq112,
    ``actualOriginalGlobalPhiNativeOriginalStage3BodyEq112,
    ``actualOriginalGlobalPhiNativeOriginalStage4BodyEq112]
  unless source.getAppFn.isConstOf expectedNames[stage.getNat - 1]! && source.getAppArgs.size == 8 do
    throwError "Native112 requires only checked THIS exact original literal stage BODY."
  for i in [:8] do
    unless source.getAppArgs[i]!.consumeMData.equal nativeProp.getAppArgs[i]!.consumeMData do
      throwError "Native112 refuses original fixed-stage factory restoration on different arguments."
  let sourceType ← phiNativeNoRecovery025 (← inferType source)
  unless sourceType.consumeMData.equal body.consumeMData do
    throwError "Native112 factory source TYPE is not exact original23-let fixed-stage BODY."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``id [Level.zero]) #[nativeProp, source])
  unless (← inferType proof).consumeMData.equal nativeProp.consumeMData do
    throwError "Native112 ordinary id changed original factory/fixed-stage proposition."
  logInfo m!"Native112 stage{stage.getNat}: ordinary id restores ONLY original23-let factory/fixed Nat from literal raw joined body; original maps/scalars/endpoints unchanged."
  return proof

end

private lemma actualOriginalGlobalPhiNativeOriginalStage1Factory112
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    phiNativeOriginalCoefficientStageProp082 p hp P hP s 1 :=
  phi_native_original_closed_stage_factory112% 1
    (actualOriginalGlobalPhiNativeOriginalStage1BodyEq112 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 1)

private lemma actualOriginalGlobalPhiNativeOriginalStage2Factory112
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    phiNativeOriginalCoefficientStageProp082 p hp P hP s 2 :=
  phi_native_original_closed_stage_factory112% 2
    (actualOriginalGlobalPhiNativeOriginalStage2BodyEq112 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 2)

private lemma actualOriginalGlobalPhiNativeOriginalStage3Factory112
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    phiNativeOriginalCoefficientStageProp082 p hp P hP s 3 :=
  phi_native_original_closed_stage_factory112% 3
    (actualOriginalGlobalPhiNativeOriginalStage3BodyEq112 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 3)

private lemma actualOriginalGlobalPhiNativeOriginalStage4Factory112
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    phiNativeOriginalCoefficientStageProp082 p hp P hP s 4 :=
  phi_native_original_closed_stage_factory112% 4
    (actualOriginalGlobalPhiNativeOriginalStage4BodyEq112 p hp P hP s)
    with_native (phiNativeOriginalCoefficientStageProp082 p hp P hP s 4)

meta section
open Lean Meta Elab Term

/-- Assemble ONLY the five actual owned links at their exact stored vectors.
No endpoint conversion or geometric structural certificate is built here. -/
elab "phi_native_coefficient_assembly112% " suppliedStart:term
    " using_contract " suppliedContract:term " using_reassoc " suppliedReassoc:term
    " using_point " suppliedPoint:term " using_eval " suppliedEval:term : term => do
  let supplied := #[suppliedStart, suppliedContract, suppliedReassoc, suppliedPoint, suppliedEval]
  let expectedNames := #[``actualOriginalGlobalPhiNativeOriginalStage0BodyEq105,
    ``actualOriginalGlobalPhiNativeOriginalStage1BodyEq112,
    ``actualOriginalGlobalPhiNativeOriginalStage2BodyEq112,
    ``actualOriginalGlobalPhiNativeOriginalStage3BodyEq112,
    ``actualOriginalGlobalPhiNativeOriginalStage4BodyEq112]
  let mut proofs : Array Expr := #[]
  let mut parts : Array (Expr × Expr × Expr) := #[]
  for i in [:5] do
    let proof ← phiNativeNoRecovery025
      (← Term.elabTerm supplied[i]! none (catchExPostpone := false))
    unless proof.getAppFn.isConstOf expectedNames[i]! && proof.getAppArgs.size == 8 do
      throwError "Native112 requires only exact actual owned original link proofs/eight-vectors."
    if i > 0 then
      for j in [:8] do
        unless proof.getAppArgs[j]!.consumeMData.equal proofs[0]!.getAppArgs[j]!.consumeMData do
          throwError "Native112 refuses changed original point/section/scalar/hypothesis link vectors."
    let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
    let some part := proofType.consumeMData.headBeta.eq?
      | throwError "Native112 requires actual owned original Eq3 link."
    if i > 0 then
      let (carrier, _, previousRight) := parts[i-1]!
      let (nextCarrier, nextLeft, _) := part
      unless carrier.consumeMData.equal nextCarrier.consumeMData &&
          previousRight.consumeMData.equal nextLeft.consumeMData do
        logInfo m!"Native112 actual raw join stage{i-1}→{i}: carrier={carrier.consumeMData.equal nextCarrier.consumeMData}; point={previousRight.consumeMData.equal nextLeft.consumeMData}."
        phiNativeJoinPath070 "stage112.carrier" carrier nextCarrier
        phiNativeJoinPath070 "stage112.point" previousRight nextLeft
        throwError "Native112 refuses an uncertified non-raw original coefficient link join."
    proofs := proofs.push proof
    parts := parts.push part
  let (carrier, firstPoint, _) := parts[0]!
  let (_, _, lastPoint) := parts[4]!
  let mut points : Array Expr := #[firstPoint]
  for part in parts do
    points := points.push part.2.2
  let info ← getConstInfo ``phiNativeEqFiveLinks082
  unless info.levelParams.length == 1 && points.size == 6 do
    throwError "Native112 unexpected ordinary six-point/five-link telescope."
  let proof ← phiNativeNoRecovery025
    (mkAppN (mkConst ``phiNativeEqFiveLinks082 [← getLevel carrier])
      (#[carrier] ++ points ++ proofs))
  let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
  let some (actualCarrier, actualFirst, actualLast) := proofType.consumeMData.headBeta.eq?
    | throwError "Native112 exact stored-vector chain did not return Eq3."
  unless actualCarrier.consumeMData.equal carrier.consumeMData &&
      actualFirst.consumeMData.equal firstPoint.consumeMData &&
      actualLast.consumeMData.equal lastPoint.consumeMData do
    throwError "Native112 ordinary chain changed literal original coefficient endpoints."
  logInfo "Native112 ordinary twelve-vector equality chain consumes actual five owned links; all four carrier/point joins raw exact, no geometric conversion in this declaration."
  return proof

end

private lemma actualOriginalGlobalPhiNativeCoefficientAssemblyOwn112
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    type_of% (phi_native_coefficient_assembly112%
      (actualOriginalGlobalPhiNativeOriginalStage0BodyEq105 p hp P hP s)
      using_contract (actualOriginalGlobalPhiNativeOriginalStage1BodyEq112 p hp P hP s)
      using_reassoc (actualOriginalGlobalPhiNativeOriginalStage2BodyEq112 p hp P hP s)
      using_point (actualOriginalGlobalPhiNativeOriginalStage3BodyEq112 p hp P hP s)
      using_eval (actualOriginalGlobalPhiNativeOriginalStage4BodyEq112 p hp P hP s)) :=
  phi_native_coefficient_assembly112%
      (actualOriginalGlobalPhiNativeOriginalStage0BodyEq105 p hp P hP s)
      using_contract (actualOriginalGlobalPhiNativeOriginalStage1BodyEq112 p hp P hP s)
      using_reassoc (actualOriginalGlobalPhiNativeOriginalStage2BodyEq112 p hp P hP s)
      using_point (actualOriginalGlobalPhiNativeOriginalStage3BodyEq112 p hp P hP s)
      using_eval (actualOriginalGlobalPhiNativeOriginalStage4BodyEq112 p hp P hP s)


meta section
open Lean Meta Elab Term Tactic

/-- Original local-let header compatibility is its own ordinary proof; the
five large geometric conversions stay in the five independently checked links. -/
elab "phi_native_coefficient_original_header_exact112 " supplied:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let source ← phiNativeNoRecovery025
      (← Term.elabTerm supplied none (catchExPostpone := false))
    unless source.getAppFn.isConstOf ``actualOriginalGlobalPhiNativeCoefficientAssemblyOwn112 &&
        source.getAppArgs.size == 8 do
      throwError "Native112 requires only actual original coefficient own assembly/eight-vector."
    let sourceType ← phiNativeNoRecovery025 (← whnf (← inferType source))
    let target ← phiNativeNoRecovery025 (← goal.getType)
    unless sourceType.consumeMData.headBeta.eq?.isSome && target.consumeMData.headBeta.eq?.isSome do
      throwError "Native112 requires literal original coefficient Eq propositions."
    let (typeHEq, state) ←
      (PhiNativeChartSeedEngineNamespace044.PhiNativeChartSeed044Structural142.structuralHEq
        sourceType target 96 #[] "full142").run {}
    let typeEq ← mkEqOfHEq typeHEq
    let proof ← phiNativeNoRecovery025
      (mkAppN (mkConst ``Eq.mp [Level.zero]) #[sourceType, target, typeEq, source])
    let proofType ← phiNativeNoRecovery025 (← whnf (← inferType proof))
    unless proofType.consumeMData.headBeta.equal target.consumeMData.headBeta do
      throwError "Native112 original header transport changed exact literal public coefficient proposition."
    logInfo m!"Native112 original coefficient local-let header compatibility consumes checked owned chain: native={state.wrapperLeaves}, proof={state.proofLeaves}, congruences={state.congrSteps}, binders={state.binderSteps}, remaining={state.remaining}."
    goal.assign proof
    replaceMainGoal []

end

lemma actualOriginalGlobalCanonicalQuadraticPhi_native_contracted_coefficient
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    actualOriginalPositiveTwoContractedNativeDifferentialMap p hp P hP
      (actualOriginalGlobalCanonicalQuadraticPhi p hp P s) =
    actualResidueDifferentialDerivation (K := K) (R := R) (L := L)
      (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s) := by
  intro C I R L
  phi_native_coefficient_original_header_exact112
    (actualOriginalGlobalPhiNativeCoefficientAssemblyOwn112 p hp P hP s)

end PfaffianDescent
