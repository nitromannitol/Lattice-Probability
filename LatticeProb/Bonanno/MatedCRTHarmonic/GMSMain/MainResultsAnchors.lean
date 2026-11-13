/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.MainResultsAnchors at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.MainResultsInputs
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.MesoModelFinal
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.CellularEmbedding
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MesoscopicControlWith
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Recurrent
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTEdge
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTGraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCellCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianLaw
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.LocalFiniteness
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCorrelatedBM2
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
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLrCoord
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLrCov
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTTwoSidedMin

/-!
# Seven main-result statements from three inputs

The seven theorem anchors of the draft surface v5,
stated **verbatim** (with the local names of `MainResultsDraft` for the seven draft definitions; retargeted to the frozen
names by `rfl` for the corresponding declarations), each proved from the fewest named inputs of `MainResultsInputs`:

| anchor | theorem | inputs |
|---|---|---|
| [18] Theorem 3.2 | `matedCRT_energy_le_add_of_matingOfTrees_of_inputs` | `Theorem32Input` |
| [18] Theorem 1.3, repaired | `matedCRT_energy_le_of_matingOfTrees_of_inputs` | `Theorem32Input` |
| [18] Theorem 1.4 | `matedCRT_green_and_recurrent_of_matingOfTrees_of_inputs` | `Theorem14GreenInput` |
| [18] Theorem 1.5, main | `matedCRT_holder_of_matingOfTrees_of_inputs` | `Theorem15Input` |
| [18] Theorem 1.5, literal | `matedCRT_holder_of_matingOfTrees_simplyConnected_of_inputs` | `Theorem15Input` |
| [18] Corollary 1.6, main | `matedCRT_tutte_edge_le_of_matingOfTrees_of_inputs` | `Theorem15Input` |
| [18] Cor. 1.6, literal | `matedCRT_tutte_edge_le_of_matingOfTrees_simplyConnected_of_inputs` | `Theorem15Input` |

Proved here outright (no input):
* `recurrentBody_of_coupling` — the recurrence half of Theorem 1.4, for every real `ε > 0` (  `exists_cellModel_of_matingOfTrees_holds`, REC's transfer `MesoModel.matedCRTRecurrenceInput_of_cellModel` at the
  law `P.map bm`, and a.s. local finiteness).

Statement-level implications between the anchors (independent of how the inputs are proved):
* `theorem13Body_of_theorem32Body` (`MainResultsTheorem13`): Theorem 3.2 ⇒ repaired Theorem 1.3;
* `theorem15SCBody_of_theorem15Body`: main ⇒ literal Theorem 1.5 (`isConnected_compl_of_simplyConnected`);
* `corollary16Body_of_theorem15Body`: Theorem 1.5 ⇒ Corollary 1.6 (`corollary16_tendsto_of_theorem15`:
  `f = Re, Im` and [18] Lemma 2.7 at every real `ε`, T16D's `lemma27_cellAt`);
* `corollary16SCBody_of_corollary16Body`: main ⇒ literal Corollary 1.6 (TOPO).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.MainResults

open MatedCRTHarmonic GMS3

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

end Coupling

/-! ### The seven draft anchors (verbatim statements, local names of `MainResultsDraft`) -/

/-- **[18] Theorem 3.2 on every mating-of-trees coupling**, from named input 1 (Theorem 3.2 at real `ε`). -/
theorem matedCRT_energy_le_add_of_matingOfTrees_of_inputs (h32 : Theorem32Input) :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
        ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ C : ℝ, 1 ≤ C →
          ∃ A : ℝ, 0 < A ∧ ∃ Cr : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
            ∀ D : Set ℂ, ∀ hD : IsOpen D, D ⊆ ball (0 : ℂ) ρ →
            (∀ r ∈ Ioo (0 : ℝ) 1, volume (thickening r (frontier D)) ≤ ENNReal.ofReal (C * r)) →
            HasBoundedConvexity C D →
            ∀ f : ℂ → ℝ, ∀ hf : DifferentiableOn ℝ f D,
              (∀ z ∈ D, ∀ w ∈ D, ‖fderiv ℝ f z - fderiv ℝ f w‖ ≤ ε ^ (-β) * dist z w) →
              (∀ z ∈ D, |f z| ≤ ε ^ (-β)) → (∀ z ∈ D, ‖fderiv ℝ f z‖ ≤ ε ^ (-β)) →
              ContinuousOn f (closure D) →
                P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
                  (∃ g : ℤ → ℝ,
                    IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D f g) ∧
                  ∀ g : ℤ → ℝ,
                    IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D f g →
                    energyOn (MatedCRT.graph ε (bm ω) h) (verticesMeeting (cell ε (η ω)) D) g ≤
                      ENNReal.ofReal A * dirichletEnergy f D hD hf + ENNReal.ofReal (ε ^ α)} ≤
                  ENNReal.ofReal (Cr * ε ^ α) :=
  fun γ hγ0 hγ2 Ω _ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D =>
    theorem32Body_of_raw (h32 γ ⟨hγ0, hγ2⟩ Ω hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D)

end MatedCRTHarmonic.GMSMain.MainResults
