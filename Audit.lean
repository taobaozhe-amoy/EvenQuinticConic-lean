import EvenQuinticConic
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Audit every declaration in this project's public namespace, including theorem
types and their recursive proof dependencies. The check rejects any axiom not
in the explicit foundational allowlist. This is a trust-dependency check, not
a check that these lemmas establish the original geometric conjecture.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := (env.constants.toList.map Prod.fst).filter
    (fun n => (`EvenQuinticConic).isPrefixOf n)
  if names.isEmpty then
    throwError "No project declarations found; refusing an empty audit."
  let mut theoremCount := 0
  for name in names.toArray.qsort Name.lt do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter (fun a => !allowed.contains a)
    unless unexpected.isEmpty do
      throwError "{name}: unexpected axioms {unexpected.toList}"
    if let some (.thmInfo _) := env.find? name then
      theoremCount := theoremCount + 1
      logInfo m!"{name}: {axioms.qsort Name.lt |>.toList}"
  logInfo m!"AUDIT PASSED: {names.length} declarations; {theoremCount} theorem declarations."
  logInfo "Only propext, Classical.choice, and Quot.sound are permitted."
