import LatticeProbAudit.Support.Statements
import LatticeProbAudit.Kingman.Solution
import LatticeProbAudit.GFF.Solution
import LatticeProbAudit.BinomialLocalCLT.Solution

/-!
# Statement regression for the comparator solutions

For each audited theorem, checks that the type of the solution theorem is
exactly the proposition elaborated in the challenge environment
(`Audit/LatticeProbAudit/Support/Statements.lean`), and that it mentions no
constant of the library namespace `LatticeProb`.  Building this module prints
one line per theorem; any mismatch is an error.  This is a local proxy for the
statement-identity part of `leanprover/comparator`.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (thm, stmt) in [
    (`LatticeProbAudit.kingman, `LatticeProbAudit.Statements.kingman),
    (`LatticeProbAudit.gff, `LatticeProbAudit.Statements.gff),
    (`LatticeProbAudit.binomial_local_clt, `LatticeProbAudit.Statements.binomialLocalCLT)] do
    let some ti := env.find? thm | throwError "missing theorem {thm}"
    let some si := env.find? stmt | throwError "missing statement {stmt}"
    let some v := si.value? | throwError "statement {stmt} has no value"
    -- A `def` abstracts the proofs inside its value into auxiliary lemmas
    -- (`LatticeProbAudit.Statements.*._proof_i`); put their proof terms back
    -- before comparing.
    let v := v.replace fun e => match e with
      | .const n ls =>
        if (`LatticeProbAudit.Statements).isPrefixOf n && n.isInternal then
          (env.find? n).bind fun ci =>
            (ci.value? (allowOpaque := true)).map (·.instantiateLevelParams ci.levelParams ls)
        else none
      | _ => none
    let v ← liftCoreM (Core.betaReduce v)
    let ty ← liftCoreM (Core.betaReduce ti.type)
    unless ty == v do
      throwError "{thm}: the solution statement differs from the challenge statement"
    for c in ti.type.getUsedConstants do
      if (`LatticeProb).isPrefixOf c then
        throwError "{thm} mentions the library constant {c}"
    logInfo m!"{thm}: identical to the challenge statement; no library constant"

#print axioms LatticeProbAudit.kingman
#print axioms LatticeProbAudit.gff
#print axioms LatticeProbAudit.binomial_local_clt
