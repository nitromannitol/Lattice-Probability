/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Blueprint.External at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Analysis.Removability
import LatticeProb.Bonanno.QuantumZipper.SLE.Defs
import LatticeProb.Bonanno.QuantumZipper.Loewner.Curves
import Mathlib.Probability.BrownianMotion.Basic

/-!
# External (literature) blueprint items

`Prop`-valued statements of results imported from the literature. Nothing is proved here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper.Blueprint

/-- Riemann mapping theorem plus Carathéodory's boundary extension (e.g. Pommerenke,
*Boundary Behaviour of Conformal Maps*, Thm. 2.6): each complementary component of a simple
chord from `0` to `∞` in `ℍ` has a normalized conformal uniformizer onto `ℍ` fixing `0`
and `∞`.
**Proved**: `CA.Uniformizer.riemannMappingCaratheodory` (`Proofs/Complex/UniformizerRight.lean:142`,
entries L-CA-TOPO (U-nodes) and L-CA-M; standard axioms). -/
def RiemannMappingCaratheodory : Prop :=
  ∀ η : ℝ → ℂ, IsSimpleChord η →
    (∃ φ, IsNormalizedUniformizer (leftComponent η) φ) ∧
      (∃ φ, IsNormalizedUniformizer (rightComponent η) φ)

end QuantumZipper.Blueprint
