/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.BundleSec4.FixedInstance at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop210
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.ProducersCellCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.RecAdmissible
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Theorem14
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Interfaces
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTGraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLrCoord
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCorrelatedBM2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLrCov
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTTwoSidedMin
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.CellularEmbedding
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MesoscopicControlWith
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianLaw
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Recurrent
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTEdge
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCellCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.LocalFiniteness
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Adj
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateMeasurableSpace
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.HitTime
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VertexPath
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dart
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsConnectedSet
import LatticeProb.Bonanno.MatedCRTHarmonic.HarmonicInfinity.Mesoscopic
import LatticeProb.Bonanno.MatedCRTHarmonic.Implementation.MatedCRTGraphConnected
import LatticeProb.Bonanno.MatedCRTHarmonic.Harmonic.Harm
import LatticeProb.Bonanno.MatedCRTHarmonic.Harmonic.Graph
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.MeasureTheory.OuterMeasure.Basic
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.Chain
import LatticeProb.Bonanno.MatedCRTHarmonic.GoodScales.Bound
import LatticeProb.Bonanno.MatedCRTHarmonic.CellularFacts.Basic
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.AnnularEvent
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VerticesMeeting
import LatticeProb.Bonanno.MatedCRTHarmonic.Lemma38Source.Numerics
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.Prop210Source
import LatticeProb.Bonanno.MatedCRTHarmonic.Lemma38Source.OneScale
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FinalAssembly
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop410Rooting
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.SmallRootMass
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Consumers
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.L27Bridge

/-!
# The mated-CRT map conclusion from ONE fixed-parameter instance of [18] Proposition 2.10 (the producer shape)

The uniform Proposition 2.10 producer is instantiated once, as
`GMS4.UniformL27GMSAProp210Producer M S R (3/4) 100 betaG4 A α Cfail` (the one-scale estimate's instance). This file shows that this
single instance is ALL the endgame needs:

* `Prop210At F ρ C` — the per-test conclusion of `GMS4.proposition210_holds` at ambient radius `ρ` and test constant
  `C` (some `betaG4, α > 0`, `A, Cfail ≥ 0`, threshold `2A`, tolerance `mesh k ^ α`), i.e. exactly what one uniform
  producer gives (`prop210At_of_uniformProducer`) and exactly the one-scale estimate's premise at `(3/4, 100)`;
* `annulus38OneScaleBadBound_of_prop210At` — `hAnnulus38` at one coupling from `Prop210At F (3/4) 100` (the one-scale estimate);
* `matedCRTRecurrencePathScaleInput_of_prop210At` — `hREC` from `Prop210At F ρG4 C₀` for ANY `ρG4 ∈ (0, 1)`,
  `16π ≤ C₀` (in particular `(3/4, 100)`), through `RecEventually` (coarse scales absorbed into L27's constant);
* `exists_cellModel_of_matingOfTrees_of_prop210At`, the companion map conclusion — both frozen v3
  conclusions with `Prop210At M.coupled.family (3/4) 100` (MTC's family of every coupling) as the only remaining input.

`Prop210Source` (the source quantifier order) implies `Prop210At` at every admissible `(ρ, C)`
(`prop210At_of_source`), so these theorems are the weakest-input versions of `BundleSec4.Endgame`'s.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Real
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic

/-- **One fixed-parameter instance of [18] Proposition 2.10** for `F` at ambient radius `ρ` and test constant `C`, in
The exact conclusion shape of G4's `GMS4.proposition210_holds` (threshold `2A`, tolerance `mesh k ^ α`). -/
def Prop210At (F : CellFamily.RandomCellFamily) (ρ C : ℝ) : Prop :=
  ∃ β A α Cfail : ℝ, 0 < β ∧ 0 < α ∧ 0 ≤ A ∧ 0 ≤ Cfail ∧
    ∀ (k : ℕ) (V : Set ℂ) (f : ℂ → ℝ), GMS4.Prop210Admissible (CellFamily.mesh k) ρ C β V f →
      F.P (GMS4.Prop210Bad F k V f (2 * A) (CellFamily.mesh k ^ α)) ≤
        ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α)

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

end Coupling

/-! ### The final assembly from the single instance `(3/4, 100)` -/

end MatedCRTHarmonic.BundleSec4
