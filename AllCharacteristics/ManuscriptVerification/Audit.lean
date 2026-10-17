import Lean
import Lean.Util.FoldConsts
import Lean.Util.ForEachExpr

/-! Public inspection of theorem types and their transitive type/value dependencies.
This inspects the imported checked environment; it is not fresh kernel replay.
The separate Comparator challenge remains the independent main-theorem target. -/

namespace ManuscriptVerification
open Lean

private def expressionDependencies (e : Expr) : IO NameHashSet := do
  let names ← IO.mkRef ({} : NameHashSet)
  e.forEach fun part => do
    match part with
    | .const n _ | .proj n _ _ => names.modify (·.insert n)
    | _ => pure ()
  names.get

private def dependencies (ci : ConstantInfo) : IO (Array Name) := do
  let mut names := ci.getUsedConstantsAsSet.toArray
  names := names ++ (← expressionDependencies ci.type).toArray
  if let some value := ci.value? (allowOpaque := true) then
    names := names ++ (← expressionDependencies value).toArray
  if let .recInfo info := ci then
    for rule in info.rules do
      names := names ++ (← expressionDependencies rule.rhs).toArray
  if let .inductInfo info := ci then
    names := names ++ info.all.toArray
  return names

/-- Fail on missing roots, non-theorem roots, forbidden dependencies, missing
required dependencies, or any axiom outside the explicit standard-three list.
Structure names in projection expressions and recursor rule bodies are included. -/
def inspect (env : Environment) (roots : Array Name)
    (forbidden : Array Name := #[]) (required : Array Name := #[])
    (allowDefinitions : Bool := false) : IO Unit := do
  let allowed : Array Name := #[`propext, `Quot.sound, `Classical.choice]
  let mut cache : NameMap (Array Name) := {}
  for root in roots do
    match env.checked.get.find? root with
    | some (.thmInfo _) => pure ()
    | some (.defnInfo _) | some (.opaqueInfo _) =>
      unless allowDefinitions do
        throw (IO.userError s!"Expected theorem, found definition: {root}")
    | _ => throw (IO.userError s!"Missing theorem root: {root}")
    let mut queue := #[root]
    let mut seen : NameHashSet := ({} : NameHashSet).insert root
    let mut next := 0
    let mut axioms : NameHashSet := {}
    while next < queue.size do
      let name := queue[next]!
      next := next + 1
      if forbidden.contains name then
        throw (IO.userError s!"Forbidden dependency of {root}: {name}")
      let some ci := env.checked.get.find? name
        | throw (IO.userError s!"Missing dependency of {root}: {name}")
      if let .axiomInfo _ := ci then
        if !allowed.contains name then
          throw (IO.userError s!"Unapproved axiom for {root}: {name}")
        axioms := axioms.insert name
      let children ← match cache.find? name with
        | some ds => pure ds
        | none =>
          let ds ← dependencies ci
          cache := cache.insert name ds
          pure ds
      for child in children do
        if !seen.contains child then
          seen := seen.insert child
          queue := queue.push child
    for name in required do
      if !seen.contains name then
        throw (IO.userError s!"Missing required dependency of {root}: {name}")
    IO.println s!"PASS {root}: declarations={seen.size}; axioms={axioms.toArray}"
  IO.println s!"AUDIT COMPLETE: {roots.size} roots; type/value/projection/recursor traversal"

end ManuscriptVerification
