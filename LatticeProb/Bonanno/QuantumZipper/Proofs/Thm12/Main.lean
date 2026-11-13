/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm12.Main at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.Semigroup

/-!
# Theorem 1.2

Assembly: `CharFun.theorem1_2_of_phi` reduces Theorem 1.2 to the semigroup identity
`Φ_T = Φ_0`, which is `Semigroup.Phi_const`; the nonnegativity of the energies it needs comes
from the free-boundary GFF `X` of the hypotheses (`Semigroup.Efun_nonneg_of_gff`).
-/

namespace QuantumZipper

/-- **Theorem 1.2** (Sheffield, reverse coupling), unconditionally. -/
theorem theorem1_2_holds : theorem1_2 :=
  CharFun.theorem1_2_of_phi (by
    intro κ T hκ hT Ω _ P _ B X hB hX _ ρ
    exact Semigroup.Phi_const hκ hT ρ.1 hB fun τ hτ f =>
      Semigroup.Efun_nonneg_of_gff hX κ τ hτ ρ f)

end QuantumZipper
