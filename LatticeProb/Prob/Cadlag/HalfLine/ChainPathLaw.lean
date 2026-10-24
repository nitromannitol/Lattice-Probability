import LatticeProb.Prob.Cadlag.HalfLine.Separable
import LatticeProb.Prob.Cadlag.HalfLine.Laws
import LatticeProb.Prob.Cadlag.HalfLine.PathMaps
import LatticeProb.Prob.JumpChain.MarkovProperty
import LatticeProb.Prob.JumpChain.PositionFdd

/-!
# Half-line path laws of jump chains

Regular jump histories define measurable half-line càdlàg paths. Their pushforward laws
have the expected finite-dimensional marginals, and injective state embeddings preserve
raw natural information at each time.
-/

namespace LatticeProb.Cadlag.HalfLine

open MeasureTheory Set TopologicalSpace

noncomputable section

variable {S E : Type*} [MeasurableSpace S] [Countable S]
  [MeasurableSingletonClass S] [MetricSpace E] [SeparableSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- A countable-state jump history gives a measurable half-line path. -/
theorem measurable_halfLinePath (ι : S → E) :
    Measurable (fun h : JumpChain.RegularHistory S => h.halfLinePath ι) := by
  apply measurable_iff_measurable_eval.mpr
  exact JumpChain.RegularHistory.measurable_halfLinePath_eval ι (measurable_of_countable ι)

/-- The probability law of the embedded jump-chain path on the half-line. -/
def pathLaw (rates : JumpChain.BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (ι : S → E) : ProbabilityMeasure (D E) :=
  ProbabilityMeasure.map
    (⟨rates.regularLaw μ, inferInstance⟩ : ProbabilityMeasure (JumpChain.RegularHistory S))
    (measurable_halfLinePath ι).aemeasurable

/-- Finite evaluations of the path law are the embedded position marginals. -/
theorem jointLaw_pathLaw (rates : JumpChain.BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (ι : S → E) {k : ℕ} (ts : Fin k → Time) :
    jointLaw (pathLaw rates μ ι) ts =
      ProbabilityMeasure.map
        (⟨rates.regularLaw μ, inferInstance⟩ :
          ProbabilityMeasure (JumpChain.RegularHistory S))
        (measurable_pi_lambda _ (fun i =>
          (measurable_of_countable ι).comp
            (JumpChain.RegularHistory.measurable_position (ts i)))).aemeasurable := by
  apply Subtype.ext
  exact Measure.map_map (measurable_pi_lambda _ (fun i => measurable_eval (ts i)))
    (measurable_halfLinePath ι)

/-- An injective state embedding preserves the raw natural sigma algebra through time `t`. -/
theorem naturalSigma_halfLinePath_eq (ι : S → E) (hι : Function.Injective ι) (t : Time) :
    naturalSigma (fun h : JumpChain.RegularHistory S => h.halfLinePath ι) t =
      JumpChain.BoundedRates.naturalSigma (S := S) t := by
  have hme : MeasurableEmbedding ι :=
    ⟨hι, measurable_of_countable ι, fun A _ => (A.to_countable.image ι).measurableSet⟩
  unfold naturalSigma JumpChain.BoundedRates.naturalSigma
  congr 1
  funext s
  congr 1
  funext _
  change MeasurableSpace.comap (ι ∘ fun h : JumpChain.RegularHistory S => h.position s)
    ‹MeasurableSpace E› = _
  rw [← MeasurableSpace.comap_comp, hme.comap_eq]

end

end LatticeProb.Cadlag.HalfLine
