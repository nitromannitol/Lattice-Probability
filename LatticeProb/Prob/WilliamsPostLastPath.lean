import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W5Fin3
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W4
import LatticeProb.Topology.ContinuousMapBorel

/-! # Continuous paths after the last zero of a drifted Brownian motion -/

open MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

open QuantumZipper.Williams

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {b : ℝ≥0 → Ω → ℝ}

/-- The post-last-zero path, packaged as a continuous map. -/
def williamsPostLastPath (hb : GoodBM b P) (σ μ : ℝ) (ω : Ω) : C(ℝ≥0, ℝ) :=
  ⟨postLast (dpath σ μ b ω) 0, continuous_postLast_dpath hb σ μ ω⟩

/-- The post-last-zero continuous path is measurable. -/
theorem measurable_williamsPostLastPath (hb : GoodBM b P) (σ μ : ℝ) :
    Measurable (williamsPostLastPath hb σ μ) := by
  refine ContinuousMapBorel.ContinuousMap.measurable_iff_eval.2 fun t => ?_
  exact measurable_postLast_eval hb σ μ t

/-- Positive-drift Brownian motion, viewed from its last zero, starts at zero almost surely. -/
theorem ae_williamsPostLastPath_zero (hb : GoodBM b P) {σ μ : ℝ}
    (hσ : 0 < σ) (hμ : 0 < μ) :
    ∀ᵐ ω ∂P, williamsPostLastPath hb σ μ ω 0 = 0 := by
  filter_upwards [ae_bddAbove_zeros hb hσ hμ] with ω hbounded
  have hzero : dpath σ μ b ω (lastPass (dpath σ μ b ω) 0) = 0 :=
    IsClosed.csSup_mem (isClosed_eq (continuous_dpath hb σ μ ω) continuous_const)
      ⟨0, dpath_zero hb σ μ ω⟩ hbounded
  simpa [williamsPostLastPath, postLast] using hzero

end LatticeProb
