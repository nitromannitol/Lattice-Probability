/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Assembly.Theorem11 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGDimension.Assembly.Final
import LatticeProb.Bonanno.LQGDimension.LFPP.Lemma51
import LatticeProb.Bonanno.LQGDimension.LFPP.Lemma51Aux5
import LatticeProb.Bonanno.LQGDimension.LFPP.Lemma51Aux6

/-!
# Theorem 1.1

`theorem11 : Theorem11` proves Theorem 1.1 of *Small-parameter asymptotics for the Liouville
quantum gravity dimension*:

* `a_n` is finite and subadditive, and `0 < a* = lim a_n/n = inf a_n/n`;
* (1.5): `λ(ξ)/ξ^{4/3} → a*/log 16`;
* (1.6): `(d_γ − 2)/γ^{4/3} → 2^{−1/3} a*/log 16`.

The statement is in `LQGDimension.Statement.Main`.  Its modelling decisions are recorded in
`STATEMENT_SPEC.md`.
-/

namespace LQGDimension

/-- Lemma 5.1 of the paper (node `L51`). -/
theorem lemma51 : Blueprint.Draft.Lemma51 :=
  L51.lemma51_of_parts @L51.sf_lower @L51.integral_iInf_blockCost_le

/-- Proposition 1.2, lower bound (1.8). -/
theorem prop12Lower : Blueprint.Prop12Lower :=
  prop12Lower_of_lemma51 lemma51

/-- **Theorem 1.1.** -/
theorem theorem11 : Theorem11 :=
  theorem11_of_lemma51 lemma51

/-- Theorem 1.1, equation (1.5). -/
theorem theorem11_lambda : Theorem11_Lambda := theorem11.2.1

end LQGDimension
