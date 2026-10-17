import PfaffianDescent.ActualGlobalConormalFactoredOpenKaehlerComparison
import PfaffianDescent.ActualOriginalQuarticCotangentChartChoice
import PfaffianDescent.ActualOriginalIdealChartTransportEquality

/-! SOURCE ONLY, UNVERIFIED. Specialize the whole genuine global conormal
map comparison to the SAME original quartic point. The chart, source/target
Isos and ground-field square are constructed internally. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

meta section
open Lean Meta Elab Tactic

/-- Only metadata/beta and local/embedded let heads are normalized,
with the same fuel8 as the existing structural tactic. -/
private def kaehlerComparisonHead011 (input : Expr) : Term.TermElabM Expr := do
  let mut current ← instantiateMVars input
  for _ in [:8] do
    current := current.consumeMData.headBeta
    if let .letE _ _ value body _ := current then
      current := body.instantiate1 value
    else if let .fvar id := current.getAppFn then
      if let some value := (← id.getDecl).value? then
        current := mkAppN value current.getAppArgs
      else
        return current
    else
      return current
  return current.consumeMData.headBeta

/-- Extract the actual two maps from the generic producer's inferred
proposition; its proof value is never returned into a declaration. -/
private def kaehlerSourceSides011 (supplied : Syntax) : Term.TermElabM (Expr × Expr) := do
  let source ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let source ← instantiateMVars source
  if source.hasMVar || source.hasLevelMVar || source.hasLooseBVars || source.hasSorry then
    throwError "KaehlerSides011 unresolved or recovery source application."
  let proposition ← kaehlerComparisonHead011 (← inferType source)
  let some (_, left, right) := proposition.eq?
    | throwError "KaehlerSides011 expected the actual generic comparison equality; target:{indentExpr proposition}"
  return (left, right)

elab "kaehler_source_left011% " supplied:term : term => do
  return (← kaehlerSourceSides011 supplied).1

elab "kaehler_source_right011% " supplied:term : term => do
  return (← kaehlerSourceSides011 supplied).2

/-- Check one map conversion at a time with the existing bounded
structural tactic and an ordinary HEq reflexivity source. -/
elab "kaehler_map_certificate011" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
    let some (_, left, _, _) := target.heq?
      | throwError "KaehlerMap011 expected the actual map HEq; target:{indentExpr target}"
    let sourceRefl ← mkHEqRefl left
    let supplied ← Term.exprToSyntax sourceRefl
    evalTactic (← `(tactic| basis_chart_exact009 $supplied))

end

meta section
open Lean Meta Elab Tactic

/-- Select an exact original Hom.hom argument without unfolding that
abbreviation into the larger ConcreteCategory dictionary. -/
elab "kaehler_argument012% " index:num supplied:term : term => do
  let expression ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression := (← instantiateMVars expression).consumeMData.headBeta
  let arguments := expression.getAppArgs
  unless expression.getAppFn.isConstOf ``ModuleCat.Hom.hom && arguments.size == 5 do
    throwError "KaehlerArg012 expected original ModuleCat.Hom.hom with5 arguments; head={expression.getAppFn}, arguments={arguments.size}."
  let i := index.getNat
  unless i < arguments.size do
    throwError "KaehlerArg012 argument index out of range."
  return arguments[i]!

syntax "kaehler_left_vector_congr012 " "[" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| kaehler_left_vector_congr012 [$certificates,*]) => do
    let goal ← getMainGoal
    goal.withContext do
      let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
      let some (_, left, _, right) := target.heq?
        | throwError "KaehlerVector012 expected the actual LEFT-map HEq."
      let left := left.consumeMData.headBeta
      let right := right.consumeMData.headBeta
      let head := left.getAppFn
      let la := left.getAppArgs
      let ra := right.getAppArgs
      unless head.isConstOf ``ModuleCat.Hom.hom && head.equal right.getAppFn &&
          la.size == 5 && ra.size == 5 && certificates.getElems.size == 5 do
        throwError "KaehlerVector012 expected the common original Hom.hom head and five exact argument certificates."
      let thm ← mkHCongrWithArity head 5
      let mut arguments := #[]
      for i in [:5] do
        let certificate ← Term.elabTerm certificates.getElems[i]! none (catchExPostpone := false)
        Term.synthesizeSyntheticMVarsNoPostponing
        let certificate ← instantiateMVars certificate
        let certificate ← match thm.argKinds[i]! with
          | .eq => mkEqOfHEq certificate
          | .heq => pure certificate
          | _ => throwError "KaehlerVector012 unexpected abstract congruence argument kind."
        arguments := arguments ++ #[la[i]!, ra[i]!, certificate]
      Term.synthesizeSyntheticMVarsNoPostponing
      let proof ← instantiateMVars (mkAppN thm.proof arguments)
      if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
        throwError "KaehlerVector012 unresolved or recovery assembled proof."
      logInfo "KaehlerVector012 ordinary Hom.hom assembly emitted from5 independent argument certificates."
      goal.assign proof
      replaceMainGoal []

end

meta section
open Lean Meta Elab Tactic

/-- Exact raw argument selection, without unfolding functor or category maps. -/
private def kaehlerVectorArgument015 (supplied : Syntax) (head : Name)
    (arity index : Nat) : Term.TermElabM Expr := do
  let expression ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression := (← instantiateMVars expression).consumeMData.headBeta
  let arguments := expression.getAppArgs
  unless expression.getAppFn.isConstOf head && arguments.size == arity do
    throwError "KaehlerArgument015 expected {head} with{arity} arguments; actual head={expression.getAppFn}, arguments={arguments.size}."
  unless index < arguments.size do
    throwError "KaehlerArgument015 argument index out of range."
  return arguments[index]!

elab "kaehler_functor_argument015% " index:num supplied:term : term => do
  kaehlerVectorArgument015 supplied ``CategoryTheory.Functor.map 8 index.getNat

elab "kaehler_composite_argument015% " index:num supplied:term : term => do
  kaehlerVectorArgument015 supplied ``CategoryTheory.CategoryStruct.comp 7 index.getNat

/-- Assemble only already-checked exact arguments by ordinary congruence. -/
private def kaehlerVectorAssembly015 (expectedHead : Name) (arity : Nat)
    (certificates : Array Syntax) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
    let some (_, left, _, right) := target.heq?
      | throwError "KaehlerVector015 expected the actual map HEq."
    let left := left.consumeMData.headBeta
    let right := right.consumeMData.headBeta
    let head := left.getAppFn
    let la := left.getAppArgs
    let ra := right.getAppArgs
    unless head.isConstOf expectedHead && head.equal right.getAppFn &&
        la.size == arity && ra.size == arity && certificates.size == arity do
      throwError "KaehlerVector015 expected exact common {expectedHead} head/{arity} arguments; actual left head={head}, left arity={la.size}, right head={right.getAppFn}, right arity={ra.size}."
    let thm ← mkHCongrWithArity head arity
    let mut arguments := #[]
    for i in [:arity] do
      let certificate ← Term.elabTerm certificates[i]! none (catchExPostpone := false)
      Term.synthesizeSyntheticMVarsNoPostponing
      let certificate ← instantiateMVars certificate
      let certificate ← match thm.argKinds[i]! with
        | .eq => mkEqOfHEq certificate
        | .heq => pure certificate
        | _ => throwError "KaehlerVector015 unexpected abstract congruence argument kind."
      arguments := arguments ++ #[la[i]!, ra[i]!, certificate]
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars (mkAppN thm.proof arguments)
    if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "KaehlerVector015 unresolved or recovery assembled proof."
    logInfo "KaehlerVector015 ordinary {expectedHead} assembly emitted from{arity} independent argument certificates."
    goal.assign proof
    replaceMainGoal []

syntax "kaehler_functor_vector_congr015 " "[" term,* "]" : tactic
syntax "kaehler_composite_vector_congr015 " "[" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| kaehler_functor_vector_congr015 [$certificates,*]) => do
    kaehlerVectorAssembly015 ``CategoryTheory.Functor.map 8 certificates.getElems
  | `(tactic| kaehler_composite_vector_congr015 [$certificates,*]) => do
    kaehlerVectorAssembly015 ``CategoryTheory.CategoryStruct.comp 7 certificates.getElems

end

universe v w

/-- Heterogeneous application with both domain/result type transports explicit. -/
private theorem kaehlerHeterogeneousApplication021
    {A A' : Sort v} {B B' : Sort w}
    (hA : A = A') (hB : B = B')
    (f : A → B) (f' : A' → B') (hf : HEq f f')
    (x : A) (x' : A') (hx : HEq x x') : HEq (f x) (f' x') := by
  cases hA
  cases hB
  cases hf
  cases hx
  rfl

meta section
open Lean Meta Elab Tactic

/-- Exact partial application of the original categorical composite. -/
elab "kaehler_comp_prefix021% " supplied:term : term => do
  let expression ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression := (← instantiateMVars expression).consumeMData.headBeta
  unless expression.getAppFn.isConstOf ``CategoryTheory.CategoryStruct.comp &&
      expression.getAppArgs.size == 7 do
    throwError "KaehlerPrefix021 expected the exact raw original comp7 application."
  return mkAppN expression.getAppFn (expression.getAppArgs.take 6)

syntax "kaehler_prefix_certificate021 " "[" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| kaehler_prefix_certificate021 [$certificates,*]) => do
    let goal ← getMainGoal
    goal.withContext do
      let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
      let some (_, left, _, right) := target.heq?
        | throwError "KaehlerPrefix021 expected exact partial-function HEq."
      let left := left.consumeMData.headBeta
      let right := right.consumeMData.headBeta
      let head := left.getAppFn
      let la := left.getAppArgs
      let ra := right.getAppArgs
      unless head.isConstOf ``CategoryTheory.CategoryStruct.comp &&
          head.equal right.getAppFn && la.size == 6 && ra.size == 6 &&
          certificates.getElems.size == 6 do
        throwError "KaehlerPrefix021 expected common comp head with six exact prefix certificates."
      let thm ← mkHCongrWithArity head 6
      let mut arguments := #[]
      for i in [:6] do
        let certificate ← Term.elabTerm certificates.getElems[i]! none (catchExPostpone := false)
        Term.synthesizeSyntheticMVarsNoPostponing
        let certificate ← instantiateMVars certificate
        let certificate ← match thm.argKinds[i]! with
          | .eq => mkEqOfHEq certificate
          | .heq => pure certificate
          | _ => throwError "KaehlerPrefix021 unexpected congruence argument kind."
        arguments := arguments ++ #[la[i]!, ra[i]!, certificate]
      let proof ← instantiateMVars (mkAppN thm.proof arguments)
      if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
        throwError "KaehlerPrefix021 unresolved/recovery partial-function proof."
      logInfo "KaehlerPrefix021 ordinary partial-function certificate emitted; inner map is not an argument."
      goal.assign proof
      replaceMainGoal []

syntax "kaehler_apply_transport021 " "[" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| kaehler_apply_transport021 [$certificates,*]) => do
    let goal ← getMainGoal
    goal.withContext do
      let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
      let some (_, left, _, right) := target.heq?
        | throwError "KaehlerApplication021 expected exact original composite HEq."
      let left := left.consumeMData.headBeta
      let right := right.consumeMData.headBeta
      let head := left.getAppFn
      let la := left.getAppArgs
      let ra := right.getAppArgs
      unless head.isConstOf ``CategoryTheory.CategoryStruct.comp &&
          head.equal right.getAppFn && la.size == 7 && ra.size == 7 &&
          certificates.getElems.size == 4 do
        throwError "KaehlerApplication021 expected raw comp7 and four exact transport certificates."
      let mut hs := #[]
      for supplied in certificates.getElems do
        let h ← Term.elabTerm supplied none (catchExPostpone := false)
        Term.synthesizeSyntheticMVarsNoPostponing
        hs := hs.push (← instantiateMVars h)
      -- Preserve each already-proved certificate's own stored endpoints.
      -- Ordinary whnf exposes only its inferred proposition head/let telescope.
      let domainType := (← whnf (← inferType hs[0]!)).consumeMData.headBeta
      let resultType := (← whnf (← inferType hs[1]!)).consumeMData.headBeta
      let functionType := (← whnf (← inferType hs[2]!)).consumeMData.headBeta
      let argumentType := (← whnf (← inferType hs[3]!)).consumeMData.headBeta
      let some (_, A, A') := domainType.eq?
        | throwError "KaehlerApplication021 expected exact stored domain type equality."
      let some (_, B, B') := resultType.eq?
        | throwError "KaehlerApplication021 expected exact stored result type equality."
      let some (_, sourceFunction, _, targetFunction) := functionType.heq?
        | throwError "KaehlerApplication021 expected exact stored partial-function HEq."
      let some (_, sourceInput, _, targetInput) := argumentType.heq?
        | throwError "KaehlerApplication021 expected exact stored inner-map HEq."
      let proof ← mkAppOptM ``kaehlerHeterogeneousApplication021
        #[some A, some A', some B, some B', some hs[0]!, some hs[1]!,
          some sourceFunction, some targetFunction, some hs[2]!,
          some sourceInput, some targetInput, some hs[3]!]
      Term.synthesizeSyntheticMVarsNoPostponing
      let proof ← instantiateMVars proof
      if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
        throwError "KaehlerApplication021 unresolved/recovery heterogeneous application."
      logInfo "KaehlerApplication021 emitted ordinary application with exact source/native domain and result types preserved."
      goal.assign proof
      replaceMainGoal []

end

meta section
open Lean Meta Elab Tactic

/-- Construct the ordinary proof with its inferred type, independent of any native goal. -/
syntax "kaehler_application_source022% " "[" term,* "]" : term
elab_rules : term
  | `(kaehler_application_source022% [$certificates,*]) => do
    unless certificates.getElems.size == 4 do
      throwError "KaehlerSource022 expected four exact previously-proved certificates."
    let mut hs := #[]
    for supplied in certificates.getElems do
      let h ← Term.elabTerm supplied none (catchExPostpone := false)
      Term.synthesizeSyntheticMVarsNoPostponing
      hs := hs.push (← instantiateMVars h)
    let domainType := (← whnf (← inferType hs[0]!)).consumeMData.headBeta
    let resultType := (← whnf (← inferType hs[1]!)).consumeMData.headBeta
    let functionType := (← whnf (← inferType hs[2]!)).consumeMData.headBeta
    let argumentType := (← whnf (← inferType hs[3]!)).consumeMData.headBeta
    let some (_, A, A') := domainType.eq?
      | throwError "KaehlerSource022 expected stored domain type equality."
    let some (_, B, B') := resultType.eq?
      | throwError "KaehlerSource022 expected stored result type equality."
    let some (_, sourceFunction, _, targetFunction) := functionType.heq?
      | throwError "KaehlerSource022 expected stored partial-function HEq."
    let some (_, sourceInput, _, targetInput) := argumentType.heq?
      | throwError "KaehlerSource022 expected stored inner-map HEq."
    let proof ← mkAppOptM ``kaehlerHeterogeneousApplication021
      #[some A, some A', some B, some B', some hs[0]!, some hs[1]!,
        some sourceFunction, some targetFunction, some hs[2]!,
        some sourceInput, some targetInput, some hs[3]!]
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "KaehlerSource022 unresolved/recovery ordinary inferred proof."
    logInfo "KaehlerSource022 ordinary proof inferred independently of goal type or intro substitutions."
    return proof

end

meta section
open Lean Meta Elab Tactic

/-- Select an exact original LinearMap.comp argument without unfolding
the composition or either component map. -/
elab "kaehler_right_argument014% " index:num supplied:term : term => do
  let expression ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression := (← instantiateMVars expression).consumeMData.headBeta
  let arguments := expression.getAppArgs
  unless expression.getAppFn.isConstOf ``LinearMap.comp && arguments.size == 21 do
    throwError "KaehlerRightArg014 expected original LinearMap.comp with21 arguments; head={expression.getAppFn}, arguments={arguments.size}."
  let i := index.getNat
  unless i < arguments.size do
    throwError "KaehlerRightArg014 argument index out of range."
  return arguments[i]!

syntax "kaehler_right_vector_congr014 " "[" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| kaehler_right_vector_congr014 [$certificates,*]) => do
    let goal ← getMainGoal
    goal.withContext do
      let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
      let some (_, left, _, right) := target.heq?
        | throwError "KaehlerRightVector014 expected the actual RIGHT-map HEq."
      let left := left.consumeMData.headBeta
      let right := right.consumeMData.headBeta
      let head := left.getAppFn
      let la := left.getAppArgs
      let ra := right.getAppArgs
      unless head.isConstOf ``LinearMap.comp && head.equal right.getAppFn &&
          la.size == 21 && ra.size == 21 && certificates.getElems.size == 21 do
        throwError "KaehlerRightVector014 expected the common original LinearMap.comp head and twenty-one exact argument certificates."
      let thm ← mkHCongrWithArity head 21
      let mut arguments := #[]
      for i in [:21] do
        let certificate ← Term.elabTerm certificates.getElems[i]! none (catchExPostpone := false)
        Term.synthesizeSyntheticMVarsNoPostponing
        let certificate ← instantiateMVars certificate
        let certificate ← match thm.argKinds[i]! with
          | .eq => mkEqOfHEq certificate
          | .heq => pure certificate
          | _ => throwError "KaehlerRightVector014 unexpected abstract congruence argument kind."
        arguments := arguments ++ #[la[i]!, ra[i]!, certificate]
      Term.synthesizeSyntheticMVarsNoPostponing
      let proof ← instantiateMVars (mkAppN thm.proof arguments)
      if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
        throwError "KaehlerRightVector014 unresolved or recovery assembled proof."
      logInfo "KaehlerRightVector014 ordinary LinearMap.comp assembly emitted from21 independent argument certificates."
      goal.assign proof
      replaceMainGoal []

end

meta section
open Lean Meta Elab Tactic

/-- Exact raw argument selection, without unfolding functor or category maps. -/
private def kaehlerVectorArgument019 (supplied : Syntax) (head : Name)
    (arity index : Nat) : Term.TermElabM Expr := do
  let expression ← Term.elabTerm supplied none (catchExPostpone := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression := (← instantiateMVars expression).consumeMData.headBeta
  let arguments := expression.getAppArgs
  unless expression.getAppFn.isConstOf head && arguments.size == arity do
    throwError "KaehlerArgument019 expected {head} with{arity} arguments; actual head={expression.getAppFn}, arguments={arguments.size}."
  unless index < arguments.size do
    throwError "KaehlerArgument019 argument index out of range."
  return arguments[index]!

elab "kaehler_functor_argument019% " index:num supplied:term : term => do
  kaehlerVectorArgument019 supplied ``CategoryTheory.Functor.map 8 index.getNat

elab "kaehler_hom_argument019% " index:num supplied:term : term => do
  kaehlerVectorArgument019 supplied ``ModuleCat.Hom.hom 5 index.getNat

elab "kaehler_iso_argument019% " index:num supplied:term : term => do
  kaehlerVectorArgument019 supplied ``CategoryTheory.Iso.hom 5 index.getNat

/-- Assemble only already-checked exact arguments by ordinary congruence. -/
private def kaehlerVectorAssembly019 (expectedHead : Name) (arity : Nat)
    (certificates : Array Syntax) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
    let some (_, left, _, right) := target.heq?
      | throwError "KaehlerVector019 expected the actual map HEq."
    let left := left.consumeMData.headBeta
    let right := right.consumeMData.headBeta
    let head := left.getAppFn
    let la := left.getAppArgs
    let ra := right.getAppArgs
    unless head.isConstOf expectedHead && head.equal right.getAppFn &&
        la.size == arity && ra.size == arity && certificates.size == arity do
      throwError "KaehlerVector019 expected exact common {expectedHead} head/{arity} arguments; actual left head={head}, left arity={la.size}, right head={right.getAppFn}, right arity={ra.size}."
    let thm ← mkHCongrWithArity head arity
    let mut arguments := #[]
    for i in [:arity] do
      let certificate ← Term.elabTerm certificates[i]! none (catchExPostpone := false)
      Term.synthesizeSyntheticMVarsNoPostponing
      let certificate ← instantiateMVars certificate
      let certificate ← match thm.argKinds[i]! with
        | .eq => mkEqOfHEq certificate
        | .heq => pure certificate
        | _ => throwError "KaehlerVector019 unexpected abstract congruence argument kind."
      arguments := arguments ++ #[la[i]!, ra[i]!, certificate]
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars (mkAppN thm.proof arguments)
    if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "KaehlerVector019 unresolved or recovery assembled proof."
    logInfo "KaehlerVector019 ordinary {expectedHead} assembly emitted from{arity} independent argument certificates."
    goal.assign proof
    replaceMainGoal []

syntax "kaehler_functor_vector_congr019 " "[" term,* "]" : tactic
syntax "kaehler_hom_vector_congr019 " "[" term,* "]" : tactic
syntax "kaehler_iso_vector_congr019 " "[" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| kaehler_functor_vector_congr019 [$certificates,*]) => do
    kaehlerVectorAssembly019 ``CategoryTheory.Functor.map 8 certificates.getElems
  | `(tactic| kaehler_hom_vector_congr019 [$certificates,*]) => do
    kaehlerVectorAssembly019 ``ModuleCat.Hom.hom 5 certificates.getElems
  | `(tactic| kaehler_iso_vector_congr019 [$certificates,*]) => do
    kaehlerVectorAssembly019 ``CategoryTheory.Iso.hom 5 certificates.getElems

end

meta section
open Lean Meta Elab Tactic

/-- Infer ordinary functor congruence entirely from each passed certificate's own vectors. -/
syntax "kaehler_functor_source024% " "[" term,* "]" : term
elab_rules : term
  | `(kaehler_functor_source024% [$certificates,*]) => do
    unless certificates.getElems.size == 8 do
      throwError "KaehlerFunctor024 expected eight exact component certificates."
    let mut hs := #[]
    let mut la := #[]
    let mut ra := #[]
    for supplied in certificates.getElems do
      let h ← Term.elabTerm supplied none (catchExPostpone := false)
      Term.synthesizeSyntheticMVarsNoPostponing
      let h ← instantiateMVars h
      let proposition := (← whnf (← inferType h)).consumeMData.headBeta
      let some (_, source, _, target) := proposition.heq?
        | throwError "KaehlerFunctor024 expected the actual stored component HEq."
      hs := hs.push h
      la := la.push source
      ra := ra.push target
    -- Resolve only the common head's universe levels from its own source vector.
    let source ← mkAppOptM ``CategoryTheory.Functor.map (la.map fun a => some a)
    Term.synthesizeSyntheticMVarsNoPostponing
    let source ← instantiateMVars source
    let head := source.getAppFn
    unless head.isConstOf ``CategoryTheory.Functor.map && source.getAppArgs.size == 8 do
      throwError "KaehlerFunctor024 expected exact original Functor.map head/arity8."
    let thm ← mkHCongrWithArity head 8
    let mut arguments := #[]
    for i in [:8] do
      let h ← match thm.argKinds[i]! with
        | .eq => mkEqOfHEq hs[i]!
        | .heq => pure hs[i]!
        | _ => throwError "KaehlerFunctor024 unexpected congruence argument kind."
      arguments := arguments ++ #[la[i]!, ra[i]!, h]
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars (mkAppN thm.proof arguments)
    if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "KaehlerFunctor024 unresolved/recovery inferred ordinary functor proof."
    logInfo "KaehlerFunctor024 ordinary map8 proof inferred from exact stored certificate vectors; no native goal or intro substitutions."
    return proof

end

meta section
open Lean Meta Elab Tactic

/-- Infer ordinary Hom projection congruence entirely from each passed certificate's own vectors. -/
syntax "kaehler_hom_source026% " "[" term,* "]" : term
elab_rules : term
  | `(kaehler_hom_source026% [$certificates,*]) => do
    unless certificates.getElems.size == 5 do
      throwError "KaehlerHom026 expected five exact component certificates."
    let mut hs := #[]
    let mut la := #[]
    let mut ra := #[]
    for supplied in certificates.getElems do
      let h ← Term.elabTerm supplied none (catchExPostpone := false)
      Term.synthesizeSyntheticMVarsNoPostponing
      let h ← instantiateMVars h
      let proposition := (← whnf (← inferType h)).consumeMData.headBeta
      let some (_, source, _, target) := proposition.heq?
        | throwError "KaehlerHom026 expected the actual stored component HEq."
      hs := hs.push h
      la := la.push source
      ra := ra.push target
    -- Resolve only the common head's universe levels from its own source vector.
    let source ← mkAppOptM ``ModuleCat.Hom.hom (la.map fun a => some a)
    Term.synthesizeSyntheticMVarsNoPostponing
    let source ← instantiateMVars source
    let head := source.getAppFn
    unless head.isConstOf ``ModuleCat.Hom.hom && source.getAppArgs.size == 5 do
      throwError "KaehlerHom026 expected exact original ModuleCat.Hom.hom head/arity5."
    let thm ← mkHCongrWithArity head 5
    let mut arguments := #[]
    for i in [:5] do
      let h ← match thm.argKinds[i]! with
        | .eq => mkEqOfHEq hs[i]!
        | .heq => pure hs[i]!
        | _ => throwError "KaehlerHom026 unexpected congruence argument kind."
      arguments := arguments ++ #[la[i]!, ra[i]!, h]
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars (mkAppN thm.proof arguments)
    if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "KaehlerHom026 unresolved/recovery inferred ordinary Hom proof."
    logInfo "KaehlerHom026 ordinary Hom5 proof inferred from exact stored certificate vectors; no native goal or intro substitutions."
    return proof

end

meta section
open Lean Meta Elab Tactic

/-- Infer ordinary linear composition congruence entirely from each passed certificate's own vectors. -/
syntax "kaehler_linear_comp_source028% " "[" term,* "]" : term
elab_rules : term
  | `(kaehler_linear_comp_source028% [$certificates,*]) => do
    unless certificates.getElems.size == 21 do
      throwError "KaehlerLinearComp028 expected 21 exact component certificates."
    let mut hs := #[]
    let mut la := #[]
    let mut ra := #[]
    for supplied in certificates.getElems do
      let h ← Term.elabTerm supplied none (catchExPostpone := false)
      Term.synthesizeSyntheticMVarsNoPostponing
      let h ← instantiateMVars h
      let proposition := (← whnf (← inferType h)).consumeMData.headBeta
      let some (_, source, _, target) := proposition.heq?
        | throwError "KaehlerLinearComp028 expected the actual stored component HEq."
      hs := hs.push h
      la := la.push source
      ra := ra.push target
    -- Resolve only the common head's universe levels from its own source vector.
    let source ← mkAppOptM ``LinearMap.comp (la.map fun a => some a)
    Term.synthesizeSyntheticMVarsNoPostponing
    let source ← instantiateMVars source
    let head := source.getAppFn
    unless head.isConstOf ``LinearMap.comp && source.getAppArgs.size == 21 do
      throwError "KaehlerLinearComp028 expected exact original LinearMap.comp head/arity21."
    let thm ← mkHCongrWithArity head 21
    let mut arguments := #[]
    for i in [:21] do
      let h ← match thm.argKinds[i]! with
        | .eq => mkEqOfHEq hs[i]!
        | .heq => pure hs[i]!
        | _ => throwError "KaehlerLinearComp028 unexpected congruence argument kind."
      arguments := arguments ++ #[la[i]!, ra[i]!, h]
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars (mkAppN thm.proof arguments)
    if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "KaehlerLinearComp028 unresolved/recovery inferred ordinary linear comp proof."
    logInfo "KaehlerLinearComp028 ordinary linear comp21 proof inferred from exact stored certificate vectors; no native goal or intro substitutions."
    return proof

end

/-- Equality of the exact source/target comparison propositions follows
from separate heterogeneous equalities of their two actual maps. -/
private theorem actualMapEqualityPropositionTransport011
    {A B : Sort u} (left right : A) (left' right' : B)
    (hleft : HEq left left') (hright : HEq right right') :
    (left = right) = (left' = right') := by
  cases hleft
  cases hright
  rfl

private lemma actualOriginalGlobalConormalKaehlerSourceApplication009
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    type_of% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)) := by
  dsimp only
  letI : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
    (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  exact actualGlobalConormalFactoredOpenKaehlerComparison (toBase (equationIdeal p hp))
    (chartι (equationIdeal p hp) C.index) C.residue C.residue_surjective
    ((hypersurface p hp).fromSpecResidueField P.1) C.factorization
    (chartι_toBase (equationIdeal p hp) C.index)

private lemma actualOriginalGlobalConormalKaehlerLeftArgument0HEq012
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_argument012% 0 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_argument012% 0 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom)) := by
  intro I R L
  unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  rfl

private lemma actualOriginalGlobalConormalKaehlerLeftArgument1HEq012
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_argument012% 1 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_argument012% 1 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom)) := by
  intro I R L
  unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerLeftArgument2HEq012
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_argument012% 2 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_argument012% 2 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom)) := by
  intro I R L
  unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  rfl

private lemma actualOriginalGlobalConormalKaehlerLeftArgument3HEq012
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_argument012% 3 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_argument012% 3 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom)) := by
  intro I R L
  unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerLeftFunctorArgument0HEq015
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_functor_argument015% 0 (kaehler_argument012% 4 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))))
      (kaehler_functor_argument015% 0 (kaehler_argument012% 4 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerLeftFunctorArgument1HEq015
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_functor_argument015% 1 (kaehler_argument012% 4 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))))
      (kaehler_functor_argument015% 1 (kaehler_argument012% 4 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerLeftFunctorArgument2HEq015
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_functor_argument015% 2 (kaehler_argument012% 4 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))))
      (kaehler_functor_argument015% 2 (kaehler_argument012% 4 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerLeftFunctorArgument3HEq015
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_functor_argument015% 3 (kaehler_argument012% 4 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))))
      (kaehler_functor_argument015% 3 (kaehler_argument012% 4 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerLeftFunctorArgument4HEq015
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_functor_argument015% 4 (kaehler_argument012% 4 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))))
      (kaehler_functor_argument015% 4 (kaehler_argument012% 4 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerLeftFunctorArgument5HEq015
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_functor_argument015% 5 (kaehler_argument012% 4 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))))
      (kaehler_functor_argument015% 5 (kaehler_argument012% 4 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerLeftFunctorArgument6HEq015
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_functor_argument015% 6 (kaehler_argument012% 4 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))))
      (kaehler_functor_argument015% 6 (kaehler_argument012% 4 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerLeftCompositeArgument0HEq015
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_composite_argument015% 0 (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))))
      (kaehler_composite_argument015% 0 (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom)))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerLeftCompositeArgument1HEq015
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_composite_argument015% 1 (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))))
      (kaehler_composite_argument015% 1 (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom)))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerLeftCompositeArgument2HEq015
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_composite_argument015% 2 (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))))
      (kaehler_composite_argument015% 2 (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom)))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerLeftCompositeArgument3HEq015
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_composite_argument015% 3 (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))))
      (kaehler_composite_argument015% 3 (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom)))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerLeftCompositeArgument4HEq015
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_composite_argument015% 4 (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))))
      (kaehler_composite_argument015% 4 (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom)))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerLeftCompositeArgument5HEq015
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_composite_argument015% 5 (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))))
      (kaehler_composite_argument015% 5 (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom)))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerLeftCompositeArgument6HEq015
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_composite_argument015% 6 (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))))
      (kaehler_composite_argument015% 6 (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom)))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerLeftPrefixHEq021
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_comp_prefix021% (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))))
      (kaehler_comp_prefix021% (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom)))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  kaehler_prefix_certificate021
    [(actualOriginalGlobalConormalKaehlerLeftCompositeArgument0HEq015 p hp P C),
      (actualOriginalGlobalConormalKaehlerLeftCompositeArgument1HEq015 p hp P C),
      (actualOriginalGlobalConormalKaehlerLeftCompositeArgument2HEq015 p hp P C),
      (actualOriginalGlobalConormalKaehlerLeftCompositeArgument3HEq015 p hp P C),
      (actualOriginalGlobalConormalKaehlerLeftCompositeArgument4HEq015 p hp P C),
      (actualOriginalGlobalConormalKaehlerLeftCompositeArgument5HEq015 p hp P C)]

private lemma actualOriginalGlobalConormalKaehlerLeftInnerDomainTypeEq021
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    (type_of% (kaehler_composite_argument015% 6 (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))))) = (type_of% (kaehler_composite_argument015% 6 (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom))))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  exact type_eq_of_heq
    (actualOriginalGlobalConormalKaehlerLeftCompositeArgument6HEq015 p hp P C)

private lemma actualOriginalGlobalConormalKaehlerLeftCompositeResultTypeHEq021
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (type_of% (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))))) (type_of% (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom)))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerLeftCompositeResultTypeEq021
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    (type_of% (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))))) = (type_of% (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom)))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  exact eq_of_heq
    (actualOriginalGlobalConormalKaehlerLeftCompositeResultTypeHEq021 p hp P C)

private lemma actualOriginalGlobalConormalKaehlerLeftInferredApplication022
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    type_of% (kaehler_application_source022%
      [(actualOriginalGlobalConormalKaehlerLeftInnerDomainTypeEq021 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftCompositeResultTypeEq021 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftPrefixHEq021 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftCompositeArgument6HEq015 p hp P C)]) :=
  kaehler_application_source022%
      [(actualOriginalGlobalConormalKaehlerLeftInnerDomainTypeEq021 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftCompositeResultTypeEq021 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftPrefixHEq021 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftCompositeArgument6HEq015 p hp P C)]

private lemma actualOriginalGlobalConormalKaehlerLeftFunctorArgument7HEq015
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))))
      (kaehler_functor_argument015% 7 (kaehler_argument012% 4 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom))) := by
  exact actualOriginalGlobalConormalKaehlerLeftInferredApplication022 p hp P C

private lemma actualOriginalGlobalConormalKaehlerLeftFunctorInferredApplication025
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    type_of% (kaehler_functor_source024%
      [(actualOriginalGlobalConormalKaehlerLeftFunctorArgument0HEq015 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftFunctorArgument1HEq015 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftFunctorArgument2HEq015 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftFunctorArgument3HEq015 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftFunctorArgument4HEq015 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftFunctorArgument5HEq015 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftFunctorArgument6HEq015 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftFunctorArgument7HEq015 p hp P C)]) :=
  kaehler_functor_source024%
      [(actualOriginalGlobalConormalKaehlerLeftFunctorArgument0HEq015 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftFunctorArgument1HEq015 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftFunctorArgument2HEq015 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftFunctorArgument3HEq015 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftFunctorArgument4HEq015 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftFunctorArgument5HEq015 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftFunctorArgument6HEq015 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftFunctorArgument7HEq015 p hp P C)]

private lemma actualOriginalGlobalConormalKaehlerLeftArgument4HEq012
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_argument012% 4 (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_argument012% 4 (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom)) := by
  exact actualOriginalGlobalConormalKaehlerLeftFunctorInferredApplication025 p hp P C

private lemma actualOriginalGlobalConormalKaehlerLeftHomInferredApplication026
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    type_of% (kaehler_hom_source026%
      [(actualOriginalGlobalConormalKaehlerLeftArgument0HEq012 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftArgument1HEq012 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftArgument2HEq012 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftArgument3HEq012 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftArgument4HEq012 p hp P C)]) :=
  kaehler_hom_source026%
      [(actualOriginalGlobalConormalKaehlerLeftArgument0HEq012 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftArgument1HEq012 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftArgument2HEq012 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftArgument3HEq012 p hp P C),
        (actualOriginalGlobalConormalKaehlerLeftArgument4HEq012 p hp P C)]

private lemma actualOriginalGlobalConormalKaehlerLeftMapHEq011
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_source_left011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))
      (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom) := by
  exact actualOriginalGlobalConormalKaehlerLeftHomInferredApplication026 p hp P C

private lemma actualOriginalGlobalConormalKaehlerRightArgument0HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 0 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 0 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  intro I R L
  unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightArgument1HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 1 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 1 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightArgument2HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 2 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 2 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightArgument3HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 3 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 3 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  intro I R L
  unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightArgument4HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 4 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 4 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightArgument5HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 5 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 5 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightArgument6HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 6 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 6 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  intro I R L
  unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightArgument7HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 7 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 7 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightArgument8HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 8 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 8 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightArgument9HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 9 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 9 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  intro I R L
  unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightArgument10HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 10 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 10 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightArgument11HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 11 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 11 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightArgument12HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 12 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 12 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  intro I R L
  unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightArgument13HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 13 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 13 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightArgument14HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 14 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 14 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightArgument15HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 15 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 15 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightArgument16HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 16 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 16 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightArgument17HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 17 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 17 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightArgument18HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 18 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 18 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightArgument19HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 19 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 19 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightHomArgument0HEq019
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_hom_argument019% 0 (kaehler_right_argument014% 20 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))))
      (kaehler_hom_argument019% 0 (kaehler_right_argument014% 20 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightHomArgument1HEq019
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_hom_argument019% 1 (kaehler_right_argument014% 20 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))))
      (kaehler_hom_argument019% 1 (kaehler_right_argument014% 20 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightHomArgument2HEq019
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_hom_argument019% 2 (kaehler_right_argument014% 20 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))))
      (kaehler_hom_argument019% 2 (kaehler_right_argument014% 20 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightHomArgument3HEq019
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_hom_argument019% 3 (kaehler_right_argument014% 20 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))))
      (kaehler_hom_argument019% 3 (kaehler_right_argument014% 20 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightFunctorArgument0HEq019
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_functor_argument019% 0 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))))
      (kaehler_functor_argument019% 0 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightFunctorArgument1HEq019
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_functor_argument019% 1 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))))
      (kaehler_functor_argument019% 1 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightFunctorArgument2HEq019
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_functor_argument019% 2 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))))
      (kaehler_functor_argument019% 2 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightFunctorArgument3HEq019
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_functor_argument019% 3 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))))
      (kaehler_functor_argument019% 3 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightFunctorArgument4HEq019
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_functor_argument019% 4 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))))
      (kaehler_functor_argument019% 4 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightFunctorArgument5HEq019
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_functor_argument019% 5 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))))
      (kaehler_functor_argument019% 5 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightFunctorArgument6HEq019
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_functor_argument019% 6 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))))
      (kaehler_functor_argument019% 6 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightIsoArgument0HEq019
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_iso_argument019% 0 (kaehler_functor_argument019% 7 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))))))
      (kaehler_iso_argument019% 0 (kaehler_functor_argument019% 7 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom))))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightIsoArgument1HEq019
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_iso_argument019% 1 (kaehler_functor_argument019% 7 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))))))
      (kaehler_iso_argument019% 1 (kaehler_functor_argument019% 7 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom))))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightIsoArgument2HEq019
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_iso_argument019% 2 (kaehler_functor_argument019% 7 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))))))
      (kaehler_iso_argument019% 2 (kaehler_functor_argument019% 7 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom))))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightIsoArgument3HEq019
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_iso_argument019% 3 (kaehler_functor_argument019% 7 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))))))
      (kaehler_iso_argument019% 3 (kaehler_functor_argument019% 7 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom))))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  first
  | rfl
  | letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightIsoArgument4HEq019
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_iso_argument019% 4 (kaehler_functor_argument019% 7 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))))))
      (kaehler_iso_argument019% 4 (kaehler_functor_argument019% 7 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom))))) := by
  intro I R L
  try unfold L
  clear L
  dsimp (config := { zeta := false, instances := true }) only [RingHom.algebraMap_toAlgebra]
  repeat' intro
  letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  kaehler_map_certificate011

private lemma actualOriginalGlobalConormalKaehlerRightFunctorArgument7HEq019
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_functor_argument019% 7 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))))
      (kaehler_functor_argument019% 7 (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)))) := by
  intro I R L
  try unfold L
  clear L
  repeat' intro
  kaehler_iso_vector_congr019
    [(actualOriginalGlobalConormalKaehlerRightIsoArgument0HEq019 p hp P C),
      (actualOriginalGlobalConormalKaehlerRightIsoArgument1HEq019 p hp P C),
      (actualOriginalGlobalConormalKaehlerRightIsoArgument2HEq019 p hp P C),
      (actualOriginalGlobalConormalKaehlerRightIsoArgument3HEq019 p hp P C),
      (actualOriginalGlobalConormalKaehlerRightIsoArgument4HEq019 p hp P C)]

private lemma actualOriginalGlobalConormalKaehlerRightFunctorInferredApplication024
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    type_of% (kaehler_functor_source024%
      [(actualOriginalGlobalConormalKaehlerRightFunctorArgument0HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightFunctorArgument1HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightFunctorArgument2HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightFunctorArgument3HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightFunctorArgument4HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightFunctorArgument5HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightFunctorArgument6HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightFunctorArgument7HEq019 p hp P C)]) :=
  kaehler_functor_source024%
      [(actualOriginalGlobalConormalKaehlerRightFunctorArgument0HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightFunctorArgument1HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightFunctorArgument2HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightFunctorArgument3HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightFunctorArgument4HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightFunctorArgument5HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightFunctorArgument6HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightFunctorArgument7HEq019 p hp P C)]

private lemma actualOriginalGlobalConormalKaehlerRightHomArgument4HEq019
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))))
      (kaehler_hom_argument019% 4 (kaehler_right_argument014% 20 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom))) := by
  exact actualOriginalGlobalConormalKaehlerRightFunctorInferredApplication024 p hp P C

private lemma actualOriginalGlobalConormalKaehlerRightHomInferredApplication027
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    type_of% (kaehler_hom_source026%
      [(actualOriginalGlobalConormalKaehlerRightHomArgument0HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightHomArgument1HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightHomArgument2HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightHomArgument3HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightHomArgument4HEq019 p hp P C)]) :=
  kaehler_hom_source026%
      [(actualOriginalGlobalConormalKaehlerRightHomArgument0HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightHomArgument1HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightHomArgument2HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightHomArgument3HEq019 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightHomArgument4HEq019 p hp P C)]

private lemma actualOriginalGlobalConormalKaehlerRightArgument20HEq014
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_right_argument014% 20 (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))))
      (kaehler_right_argument014% 20 ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom)) := by
  exact actualOriginalGlobalConormalKaehlerRightHomInferredApplication027 p hp P C

private lemma actualOriginalGlobalConormalKaehlerRightCompositeInferredApplication028
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    type_of% (kaehler_linear_comp_source028%
      [(actualOriginalGlobalConormalKaehlerRightArgument0HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument1HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument2HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument3HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument4HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument5HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument6HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument7HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument8HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument9HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument10HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument11HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument12HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument13HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument14HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument15HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument16HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument17HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument18HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument19HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument20HEq014 p hp P C)]) :=
  kaehler_linear_comp_source028%
      [(actualOriginalGlobalConormalKaehlerRightArgument0HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument1HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument2HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument3HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument4HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument5HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument6HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument7HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument8HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument9HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument10HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument11HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument12HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument13HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument14HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument15HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument16HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument17HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument18HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument19HEq014 p hp P C),
        (actualOriginalGlobalConormalKaehlerRightArgument20HEq014 p hp P C)]

private lemma actualOriginalGlobalConormalKaehlerRightMapHEq011
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    HEq (kaehler_source_right011% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index)))
      ((actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom) := by
  exact actualOriginalGlobalConormalKaehlerRightCompositeInferredApplication028 p hp P C

private lemma actualOriginalGlobalConormalKaehlerTypeEquality009
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    (type_of% (actualGlobalConormalFactoredOpenKaehlerComparison (toBase I)
      f C.residue C.residue_surjective q C.factorization
      (chartι_toBase I C.index))) =
    (((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom =
      (actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom) := by
  exact actualMapEqualityPropositionTransport011 _ _ _ _
    (actualOriginalGlobalConormalKaehlerLeftMapHEq011 p hp P C)
    (actualOriginalGlobalConormalKaehlerRightMapHEq011 p hp P C)

private lemma actualOriginalGlobalConormalKaehlerChartComparison009
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    ((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom =
      (actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom := by
  exact Eq.mp (actualOriginalGlobalConormalKaehlerTypeEquality009 p hp P C)
    (actualOriginalGlobalConormalKaehlerSourceApplication009 p hp P C)

lemma actualOriginalGlobalConormalKaehlerComparison
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let R := ChartRing I C.index
    let L := (hypersurface p hp).residueField P.1
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let f := chartι I C.index
    let j := Spec.map (CommRingCat.ofHom C.residue)
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : IsClosedImmersion j :=
      IsClosedImmersion.spec_of_surjective _ C.residue_surjective
    let Es := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (closedImmersionModule q) (closedImmersionModule j)
      (actualFactoredIdealOpenRestrictionIso f j q C.factorization)
    let Et := actualModulePointChartSourceFactorizationIso f j q C.factorization
      (schemeRelativeDifferentials (toBase I)) (schemeRelativeDifferentials (f ≫ toBase I))
      (actualOpenImmersionDifferentialSheafRestrictionIso f (toBase I)).symm
    let Ebase := (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg schemeRelativeDifferentials (chartι_toBase I C.index)))
    ((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (toBase I) q ≫ Et.hom ≫ Ebase.hom)).hom =
      (actualAffineConormalDifferentialFiberMap (k := K) C.residue
        C.residue_surjective).comp
        ((moduleSpecΓFunctor (R := .of L)).map Es.hom).hom := by
  exact actualOriginalGlobalConormalKaehlerChartComparison009 p hp P
    (actualOriginalQuarticCotangentChartChoice p hp P hP)

end PfaffianDescent
