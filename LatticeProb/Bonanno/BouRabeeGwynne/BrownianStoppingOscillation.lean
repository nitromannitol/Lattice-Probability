/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianStoppingOscillation at commit fdb5cad; local import paths are changed and a deprecated name is updated. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppingEvent
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExitInterval
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExcursionKernel

/-! A fresh-path range estimate controls oscillation on the original path's
interval from an actual stopping time to its next exit. -/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace BouRabeeGwynne

private def centeredCurveRange {d : ℕ} (η : ℝ) : Set (Euc d × C(unitInterval, Euc d)) :=
  {p | ∀ u : unitInterval, dist (p.2 u) p.1 ≤ η}

private lemma isClosed_centeredCurveRange {d : ℕ} (η : ℝ) :
    IsClosed (centeredCurveRange (d := d) η) := by
  unfold centeredCurveRange
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro u
  exact isClosed_le (((continuous_eval_const u).comp continuous_snd).dist continuous_fst)
    continuous_const

private lemma measurableSet_centeredStoppedRange {d : ℕ} {V : Set (Euc d)}
    (hV : IsOpen V) (η : ℝ) :
    MeasurableSet {p : Euc d × BrownianPath d |
      ∀ u : unitInterval, dist (stoppedBrownianRepresentative V p.1 p.2 u) p.1 ≤ η} := by
  let F : Euc d × BrownianPath d → Euc d × C(unitInterval, Euc d) :=
    fun p => (p.1, stoppedBrownianRepresentative V p.1 p.2)
  have hm : Measurable F :=
    measurable_fst.prodMk (measurable_stoppedBrownianRepresentative_joint hV)
  have heq : {p : Euc d × BrownianPath d |
      ∀ u : unitInterval, dist (stoppedBrownianRepresentative V p.1 p.2 u) p.1 ≤ η} =
      F ⁻¹' centeredCurveRange η := rfl
  rw [heq]
  exact (isClosed_centeredCurveRange η).measurableSet.preimage hm

theorem standardBrownianLaw_stopping_oscillation_le {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {V : Set (Euc d)} (hV : IsOpen V) (z : Euc d)
    {τ : BrownianPath d → ℝ≥0∞}
    (hτ : IsStoppingTime (brownianNaturalFiltration d) τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ∞)
    (hnextfinite : ∀ᵐ ω ∂μ, brownianNextExitTime V z τ ω ≠ ∞)
    (η : ℝ) (ε : ℝ≥0∞)
    (hbound : ∀ᵐ ω ∂μ,
      μ {γ | ¬ ∀ u : unitInterval,
        dist (stoppedBrownianRepresentative V (z + ω (τ ω).toNNReal) γ u)
          (z + ω (τ ω).toNNReal) ≤ η} ≤ ε) :
    μ {ω | ∃ s ∈ Icc (τ ω).toNNReal (brownianNextExitTime V z τ ω).toNNReal,
      ∃ t ∈ Icc (τ ω).toNNReal (brownianNextExitTime V z τ ω).toNNReal,
        2 * η < dist (z + ω s) (z + ω t)} ≤ ε := by
  let A : Set (Euc d × BrownianPath d) :=
    {p | ¬ ∀ u : unitInterval, dist (stoppedBrownianRepresentative V p.1 p.2 u) p.1 ≤ η}
  have hA : MeasurableSet A := (measurableSet_centeredStoppedRange hV η).compl
  have hprob : μ {ω | (z + ω (τ ω).toNNReal,
      shiftedBrownianPath (τ ω).toNNReal ω) ∈ A} ≤ ε :=
    standardBrownianLaw_stopping_event_le hμ hτ hfinite
      (measurable_brownianPosition_stopping hτ z) hA ε hbound
  apply (measure_mono_ae (show
    {ω | ∃ s ∈ Icc (τ ω).toNNReal (brownianNextExitTime V z τ ω).toNNReal,
      ∃ t ∈ Icc (τ ω).toNNReal (brownianNextExitTime V z τ ω).toNNReal,
        2 * η < dist (z + ω s) (z + ω t)} ≤ᵐ[μ]
    {ω | (z + ω (τ ω).toNNReal, shiftedBrownianPath (τ ω).toNNReal ω) ∈ A}
    from ?_)).trans hprob
  filter_upwards [hnextfinite] with ω hω
  rintro ⟨s, hs, t, ht, hdist⟩ hnot
  have hb : ∀ u : unitInterval,
      dist (stoppedBrownianRepresentative V (z + ω (τ ω).toNNReal)
        (shiftedBrownianPath (τ ω).toNNReal ω) u) (z + ω (τ ω).toNNReal) ≤ η :=
    hnot
  exact (not_lt_of_ge
    (dist_le_of_stoppedBrownianNextRepresentative_range V z τ ω hω η hb hs ht)) hdist

end BouRabeeGwynne
