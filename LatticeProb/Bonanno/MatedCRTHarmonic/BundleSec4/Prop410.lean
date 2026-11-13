/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.BundleSec4.Prop410 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.Density
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.Prop210Source
import LatticeProb.Bonanno.MatedCRTHarmonic.Lemma38Source.OneScale
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FinalAssembly
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop210
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.ProducersCellCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop410Rooting
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.SmallRootMass
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Consumers
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.L27Bridge
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

/-!
# [18] Proposition 2.10 from Proposition 4.10 and (4.20), on MTC's family

[18] : "Proposition 2.10 is an immediate consequence of Proposition 4.10 and
(4.20)." Here, for the bundle model:

* `prop210Source_of_prop410Source`: `Prop410Source P η` (Proposition 4.10 for the bundle's γ-cone curve `η`, geometric
  `u_*^ε`) implies `Prop210Source` for MTC's dyadic family, through the concrete (4.20)
  (`BundleSec4.ae_uDens_le_two_uStar`), G4's deterministic transfer `GMS4.prop210Bound_of_localized_integral_ae`
  (threshold `2A`, tolerance `2ε^α`), and the dyadic absorption `2ε^α ≤ ε^{α/2}` for small meshes (probability `≤ 1`
  otherwise; rate constant `Cfail + 2`);
* `prop410Source_congr_ae`: the statement only depends on the a.e. class of the curve;
* `exists_cellModel_of_matingOfTrees_of_prop410Source`, the companion map conclusion: both
  frozen v3 conclusions with `Prop410Source` (at the cone realization's curve of every coupling) as the only remaining
  input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic

/-- G3's Proposition 2.10 bound is monotone in the tolerance. -/
theorem bundle_prop210Bound_mono_tol {V E : Type*} {G : LFMultigraph V E} {o : V}
    (H : CellularEmbedding G o) {D : Set ℂ} {f : ℂ → ℝ} {A η η' : ℝ} (hη : η ≤ η')
    (h : GMS3.Prop210Bound H D f A η) : GMS3.Prop210Bound H D f A η' :=
  h.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hη))

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

end Coupling

end MatedCRTHarmonic.BundleSec4
