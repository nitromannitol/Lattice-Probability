/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.MainResultsFinal at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.MainResultsAnchors
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T16DSurface
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsALemma27
import LatticeProb.Bonanno.MatedCRTHarmonic.Implementation.MatedCRTGraphConnected
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.TopoMain
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15BWiring
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15CTheorem39
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15AModel
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.MesoModelFinal
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.BPointConnected
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveAdapters
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Consumers
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.Segments
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.AreaDominates
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.LowerTail
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsBFinal
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T13RealRaw
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsBUniform

/-!
# The main [18] theorems from their established inputs

Named inputs 1 and 2 of `MainResultsInputs` are discharged real-mesh theorems (`GMSMain/T13RealRaw.lean`:
`t13_theorem32_real_raw`, `t13_theorem14_green_real_raw`, whose bodies are `Theorem32RawBody`, `Theorem14GreenRawBody`),
and the finer Theorem 1.5 input `Lemma311UniformInput` of `MainResultsWiring` is discharged by
`EpsB.lemma311RealUniform_of_coupling` ([18] (3.35) at every real `ε`, rate chosen before the radius). With
`MainResultsWiring` (Corollary 1.6 with no input) this gives ALL SEVEN draft anchors, statements verbatim, with no input:

| anchor | theorem | remaining input |
|---|---|---|
| [18] Theorem 3.2 | `matedCRT_energy_le_add_of_matingOfTrees_holds` | none |
| [18] Theorem 1.3, repaired | `matedCRT_energy_le_of_matingOfTrees_holds` | none |
| [18] Theorem 1.4 | `matedCRT_green_and_recurrent_of_matingOfTrees_holds` | none |
| [18] Theorem 1.5, main | `matedCRT_holder_of_matingOfTrees_holds` | none |
| [18] Theorem 1.5, literal | `matedCRT_holder_of_matingOfTrees_simplyConnected_holds` | none |
| [18] Corollary 1.6, main | `matedCRT_tutte_edge_le_of_matingOfTrees_holds` (`MainResultsWiring`) | none |
| [18] Corollary 1.6, literal | `matedCRT_tutte_edge_le_of_matingOfTrees_simplyConnected_holds` (`MainResultsWiring`) | none |
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.MainResults

open MatedCRTHarmonic GMS3

/-- **Named input 1 holds**: [18] Theorem 3.2 at every real `ε`, for every coupling. -/
theorem theorem32Input_holds : Theorem32Input :=
  fun _ hγ _ _ hstd _ _ _ _ _ _ _ _ _ _ _ _ _ D => t13_theorem32_real_raw D hstd hγ

/-- **[18] Theorem 3.2 on every mating-of-trees coupling — NO input.** -/
theorem matedCRT_energy_le_add_of_matingOfTrees_holds :
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
  matedCRT_energy_le_add_of_matingOfTrees_of_inputs theorem32Input_holds

end MatedCRTHarmonic.GMSMain.MainResults
