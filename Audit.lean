import EvenQuinticConic
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Audit every declaration in this project's public namespace, including theorem
types and their recursive proof dependencies. The check rejects any axiom not
in the explicit foundational allowlist. This is a trust-dependency check, not
a check that these lemmas establish the original geometric conjecture.

The official collector visits the union of all project dependency closures
with one shared visited set. This avoids repeating the same library traversal
for every declaration; the allowlist and audited roots are unchanged.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := (env.constants.toList.map Prod.fst).filter
    (fun n => (`EvenQuinticConic).isPrefixOf n)
  if names.isEmpty then
    throwError "No project declarations found; refusing an empty audit."
  let sortedNames := names.toArray.qsort Name.lt
  let collectAll : Lean.CollectAxioms.M Unit :=
    sortedNames.forM Lean.CollectAxioms.collect
  let (_, collected) := (collectAll.run env).run {}
  let axioms := collected.axioms.qsort Name.lt
  let unexpected := axioms.filter (fun a => !allowed.contains a)
  unless unexpected.isEmpty do
    throwError "Project dependency closure: unexpected axioms {unexpected.toList}"
  let mut theoremCount := 0
  for name in sortedNames do
    if let some (.thmInfo _) := env.find? name then
      theoremCount := theoremCount + 1
      logInfo m!"CHECKED: {name}"
  logInfo m!"Project dependency axioms: {axioms.toList}"
  logInfo m!"AUDIT PASSED: {names.length} declarations; {theoremCount} theorem declarations."
  logInfo "Only propext, Classical.choice, and Quot.sound are permitted."
