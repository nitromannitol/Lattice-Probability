/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W5Fin4 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W5Fin3

/-!
# W5 (part 12): W5(ii) in measure form

The killed finite-dimensional laws of `Ŷ` (killed at `λ_c(Ŷ)`) and of `revHit X c` (killed at
`T_c`) are equal as finite measures on `ℝⁿ` (`killed_fd_measure_eq`): equality of the integrals of
bounded continuous functions (`killed_fd_eq_postLast_revHit`) determines a finite Borel measure
(mathlib `ext_of_forall_lintegral_eq_of_IsFiniteMeasure`). Input for W5(iii).
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ} {σ μ : ℝ}

/-- **W5(ii), measure form.** -/
theorem killed_fd_measure_eq (hb : GoodBM b P) (hσ : 0 < σ) (hμ : 0 < μ) {c : ℝ}
    (hc : 0 < c) {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) (hu : ∀ i, u i ≤ U) :
    (P.restrict {ω | U < lastPass (postLast (dpath σ μ b ω) 0) c}).map
        (fun ω i => postLast (dpath σ μ b ω) 0 (u i))
      = (P.restrict {ω | U < (revHit (dpath σ (-μ) b ω) c).1}).map
        (fun ω i => (revHit (dpath σ (-μ) b ω) c).2 (u i)) := by
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  have hS₁ : MeasurableSet {ω | U < lastPass (postLast (dpath σ μ b ω) 0) c} :=
    measurableSet_lt measurable_const (measurable_lastPass_postLast hb σ μ c)
  have hS₂ : MeasurableSet {ω | U < (revHit (dpath σ (-μ) b ω) c).1} :=
    measurableSet_lt measurable_const (measurable_hitLevel_dpath hb σ (-μ) (-c))
  have hφ₁ : Measurable fun ω (i : Fin n) => postLast (dpath σ μ b ω) 0 (u i) :=
    measurable_pi_iff.2 fun i => measurable_postLast_eval hb σ μ (u i)
  have hφ₂ : Measurable fun ω (i : Fin n) => (revHit (dpath σ (-μ) b ω) c).2 (u i) :=
    measurable_pi_iff.2 fun i => measurable_revHit_eval hb σ (-μ) c (u i)
  refine ext_of_forall_lintegral_eq_of_IsFiniteMeasure fun f => ?_
  have hfm : Measurable fun x : Fin n → ℝ => (f x : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp f.continuous).measurable
  rw [lintegral_map hfm hφ₁, lintegral_map hfm hφ₂, ← lintegral_indicator hS₁,
    ← lintegral_indicator hS₂]
  exact killed_fd_eq_postLast_revHit hb hσ hμ hc u U hu f.continuous
    (BoundedContinuousFunction.NNReal.upper_bound f)

end QuantumZipper.Williams
