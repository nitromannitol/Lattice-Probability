import Mathlib
import LatticeProb.Prob.LawFieldPairingContinuous

/-!
# Joint continuity of integrals of a continuous family against probability measures

`LatticeProb.continuous_integral_probabilityMeasure_of_continuous` shows that for a uniformly bounded
family `G t` of functions on `E` that is jointly continuous in `(t, x)` and indexed by a *proper* metric
space `T`, the pairing `(P, t) ↦ ∫ G t dP` is jointly continuous on `ProbabilityMeasure E × T`.

Since `ProbabilityMeasure E` is pseudo-metrizable for a separable pseudo-metrizable `E`, continuity of the
pairing is a statement about convergent sequences, and a convergent sequence `t n → t₀` lies in the compact
set `{t₀} ∪ range t`.  This removes the properness assumption on the parameter space (for instance the
parameter space of a random environment, a function space that is not locally compact).

* `LatticeProb.continuous_integral_probabilityMeasure_of_continuous_of_seq`: the pairing is jointly
  continuous for an arbitrary pseudo-metric parameter space `T`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric
open scoped NNReal ENNReal BoundedContinuousFunction

namespace LatticeProb

/-- **Joint continuity of the pairing of a continuous family with probability measures, for an arbitrary
parameter space.**  Let `E` be a separable pseudo-metrizable space with its Borel structure, `T` a
pseudo-metric space and `G : T → E → ℝ` jointly continuous in `(t, x)` with `|G t x| ≤ C`.  Then
`(P, t) ↦ ∫ G t dP` is continuous on `ProbabilityMeasure E × T` (weak topology on the first factor). -/
theorem continuous_integral_probabilityMeasure_of_continuous_of_seq {E T : Type*} [TopologicalSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] [TopologicalSpace.SeparableSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [PseudoMetricSpace T] {G : T → E → ℝ}
    (hG : Continuous fun p : T × E => G p.1 p.2) {C : ℝ} (hC : ∀ t x, |G t x| ≤ C) :
    Continuous fun q : ProbabilityMeasure E × T => ∫ x, G q.2 x ∂(q.1 : Measure E) := by
  rw [continuous_iff_seqContinuous]
  intro q q₀ hq
  have h1 : Tendsto (fun n => (q n).1) atTop (𝓝 q₀.1) := (continuous_fst.tendsto _).comp hq
  have h2 : Tendsto (fun n => (q n).2) atTop (𝓝 q₀.2) := (continuous_snd.tendsto _).comp hq
  have hK : IsCompact (insert q₀.2 (range fun n => (q n).2)) := h2.isCompact_insert_range
  have : CompactSpace ↥(insert q₀.2 (range fun n => (q n).2)) := isCompact_iff_compactSpace.1 hK
  let K : Set T := insert q₀.2 (range fun n => (q n).2)
  have hmem : ∀ n, (q n).2 ∈ K := fun n => Or.inr ⟨n, rfl⟩
  have hmem₀ : q₀.2 ∈ K := Or.inl rfl
  have hG' : Continuous fun p : K × E => G p.1.1 p.2 :=
    hG.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hcont := continuous_integral_probabilityMeasure_of_continuous (T := K)
    (G := fun (t : K) x => G t.1 x) hG' (fun t x => hC t.1 x)
  have hseq : Tendsto (fun n => ((q n).1, (⟨(q n).2, hmem n⟩ : K))) atTop
      (𝓝 (q₀.1, (⟨q₀.2, hmem₀⟩ : K))) :=
    h1.prodMk_nhds (tendsto_subtype_rng.2 h2)
  exact (hcont.tendsto _).comp hseq

end LatticeProb
