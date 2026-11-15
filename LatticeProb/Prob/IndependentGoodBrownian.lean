import LatticeProb.Prob.BrownianContAll
import LatticeProb.Bonanno.QuantumZipper.Proofs.NonVacuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.Defs

/-! # Independent continuous Brownian paths starting at zero -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
open QuantumZipper QuantumZipper.Williams

namespace LatticeProb

/-- There are independent Brownian motions whose paths are all continuous and
start at zero. -/
theorem exists_independent_goodBrownian :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @Measure Ω mΩ)
      (b b' : ℝ≥0 → Ω → ℝ),
      @GoodBM Ω mΩ b P ∧ @GoodBM Ω mΩ b' P ∧
      @IndepFun Ω (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) mΩ _ _ (pathOf b) (pathOf b') P := by
  obtain ⟨Ω, mΩ, P, C, hCm, hC, hcont⟩ := exists_isBrownianReal_cont
  let : MeasurableSpace Ω := mΩ
  have : IsProbabilityMeasure P := hC.isGaussianProcess.isProbabilityMeasure
  let B : ℝ≥0 → Ω → ℝ := fun t ω => C t ω - C 0 ω
  have hBC : ∀ t, C t =ᵐ[P] B t := by
    intro t
    filter_upwards [hC.eval_zero_ae_eq_zero] with ω hω
    simp only [B, hω, sub_zero]
  have hB : GoodBM B P :=
    ⟨hC.toIsPreBrownianReal.congr hBC,
      fun t => (hCm t).sub (hCm 0),
      fun ω => (hcont ω).sub continuous_const,
      fun ω => sub_self _⟩
  let Q : Measure (Ω × Ω) := P.prod P
  let b : ℝ≥0 → Ω × Ω → ℝ := fun t ω => B t ω.1
  let b' : ℝ≥0 → Ω × Ω → ℝ := fun t ω => B t ω.2
  have hbm : IsBrownianReal B P := ⟨hB.pre, Eventually.of_forall hB.cont⟩
  have hb : GoodBM b Q :=
    ⟨(QuantumZipper.NonVacuity.nv_isBrownianReal measurePreserving_fst hbm).toIsPreBrownianReal,
      fun t => (hB.meas t).comp measurable_fst,
      fun ω => hB.cont ω.1, fun ω => hB.zero ω.1⟩
  have hb' : GoodBM b' Q :=
    ⟨(QuantumZipper.NonVacuity.nv_isBrownianReal measurePreserving_snd hbm).toIsPreBrownianReal,
      fun t => (hB.meas t).comp measurable_snd,
      fun ω => hB.cont ω.2, fun ω => hB.zero ω.2⟩
  exact ⟨Ω × Ω, inferInstance, Q, b, b', hb, hb',
    QuantumZipper.NonVacuity.nv_indepFun_prod (pathOf B) (pathOf B)⟩

end LatticeProb
