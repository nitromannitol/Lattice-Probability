import LatticeProb.Prob.BrownianExit
import LatticeProb.Prob.BrownianPathMap
import LatticeProb.Prob.BrownianPathSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.CompactOpen

/-!
# Exit position of a Brownian motion, read on path space

Let `B` be a process on `ℝ≥0` with values in `Euc d`, let `x` be a point of `Euc d`, and let `C`
be a process with continuous paths that agrees almost surely with the rescaled and recentred
process `√d • (B - x)`. A point `w` lies in the preimage of `U` under `w ↦ x + (√d)⁻¹ • w` exactly
when `x + (√d)⁻¹ • w ∈ U`. So the path of `C` leaves that preimage exactly when `B` leaves `U`,
and the exit time of `B` from `U` agrees almost surely with the continuous exit time of the path
of `C` from the preimage. No homeomorphism argument is needed.

Three statements follow. The first is the almost-sure identity of exit times. The second is the
measurability of the evaluation of a path at a measurable random time. The third transfers the
expectation of a function of the exit position from the process to the law of the sample path
of `C`.

The statements are for `1 ≤ d`, since the scaling `√d` must be invertible.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- The first exit time of the process `B` from `U` agrees almost surely with the continuous exit
time, from `0`, of the sample path of `C` from the preimage of `U` under the map
`w ↦ x + (√d)⁻¹ • w`. The identity holds almost surely and not for every `ω`, because `C` agrees
with `√d • (B - x)` only almost surely. -/
theorem ae_openExitTime_eq_continuousExitTime {d : ℕ} (hd : 1 ≤ d) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {x : Euc d} {B : ℝ≥0 → Ω → Euc d} {U : Set (Euc d)}
    {C : ℝ≥0 → Ω → Euc d} (hC : ∀ ω, Continuous fun t ↦ C t ω)
    (hCW : ∀ᵐ ω ∂P, ∀ t, C t ω = Real.sqrt d • (B t ω - x)) :
    ∀ᵐ ω ∂P, openExitTime B U ω =
      continuousExitTime ((fun w ↦ x + (Real.sqrt d)⁻¹ • w) ⁻¹' U) 0 (pathMap C hC ω) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hsd : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr hdpos).ne'
  -- Two infima over subtypes with the same predicate agree.
  have key : ∀ p q : ℝ≥0 → Prop, (∀ t, p t ↔ q t) →
      (⨅ t : {t // p t}, (t.val : ℝ≥0∞)) = ⨅ t : {t // q t}, (t.val : ℝ≥0∞) := by
    intro p q h
    obtain rfl : p = q := funext fun t ↦ propext (h t)
    rfl
  filter_upwards [hCW] with ω hω
  refine key (fun t ↦ B t ω ∉ U) (fun t ↦ 0 + C t ω ∉ (fun w ↦ x + (Real.sqrt d)⁻¹ • w) ⁻¹' U)
    (fun t ↦ ?_)
  simp [hω t, inv_smul_smul₀ hsd]

/-- Evaluating a Brownian path at a measurable random time gives a measurable random variable. -/
theorem measurable_eval_random_time {d : ℕ} {τ : BrownianPath d → ℝ≥0∞} (hτ : Measurable τ) :
    Measurable fun γ : BrownianPath d ↦ γ (τ γ).toNNReal := by
  have hcont : Continuous fun p : BrownianPath d × ℝ≥0 ↦ p.1 p.2 :=
    ContinuousEval.continuous_eval
  have hpair : Measurable fun γ : BrownianPath d ↦ (γ, (τ γ).toNNReal) :=
    measurable_id.prodMk (ENNReal.measurable_toNNReal.comp hτ)
  exact hcont.measurable.comp hpair

/-- The expectation of `f` at the exit position of the process `B` from an open set `U` equals the
expectation of `f` at the exit position of the sample path of the rescaled process `C`, under the
law of that path. The identity uses only that `f` is measurable. -/
theorem integral_exitPosition_eq_pathMap {d : ℕ} (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {x : Euc d} {B : ℝ≥0 → Ω → Euc d} {U : Set (Euc d)} (hU : IsOpen U)
    {C : ℝ≥0 → Ω → Euc d} (hCm : ∀ t, Measurable (C t)) (hC : ∀ ω, Continuous fun t ↦ C t ω)
    (hCW : ∀ᵐ ω ∂P, ∀ t, C t ω = Real.sqrt d • (B t ω - x))
    {f : Euc d → ℝ} (hf : Measurable f) :
    ∫ ω, f (B (openExitTime B U ω).toNNReal ω) ∂P =
      ∫ γ, f (x + (Real.sqrt d)⁻¹ • γ (continuousExitTime
        ((fun w ↦ x + (Real.sqrt d)⁻¹ • w) ⁻¹' U) 0 γ).toNNReal) ∂(P.map (pathMap C hC)) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hsd : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr hdpos).ne'
  have hVopen : IsOpen ((fun w ↦ x + (Real.sqrt d)⁻¹ • w) ⁻¹' U) :=
    hU.preimage (by fun_prop)
  have hF : Measurable (pathMap C hC) := measurable_pathMap C hCm hC
  have hτ : Measurable (continuousExitTime ((fun w ↦ x + (Real.sqrt d)⁻¹ • w) ⁻¹' U) 0) :=
    measurable_continuousExitTime hVopen 0
  have haff : Measurable fun v : Euc d ↦ x + (Real.sqrt d)⁻¹ • v := by fun_prop
  have hG : Measurable fun γ : BrownianPath d ↦ f (x + (Real.sqrt d)⁻¹ • γ (continuousExitTime
      ((fun w ↦ x + (Real.sqrt d)⁻¹ • w) ⁻¹' U) 0 γ).toNNReal) :=
    hf.comp (haff.comp (measurable_eval_random_time hτ))
  rw [integral_map hF.aemeasurable hG.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [ae_openExitTime_eq_continuousExitTime hd hC hCW, hCW] with ω h1 h2
  rw [h1]
  congr 1
  simp [h2, inv_smul_smul₀ hsd]

namespace BrownianExitPositionExample

/-- For a random time that is the constant `2`, evaluating a Brownian path at that time is
measurable. -/
theorem measurable_eval_constant_time :
    Measurable fun γ : BrownianPath 1 ↦
      γ ((fun _ : BrownianPath 1 ↦ (2 : ℝ≥0∞)) γ).toNNReal :=
  measurable_eval_random_time measurable_const

/-- For the constant process `0` on `Euc 1` and the open unit ball around `0`, which contains the
value of the process, the almost-sure identity holds with `x = 0` and the constant continuous
version `0`. -/
theorem ae_openExitTime_constant :
    ∀ᵐ ω ∂(Measure.dirac ()),
      openExitTime (fun (_ : ℝ≥0) (_ : Unit) ↦ (0 : Euc 1)) (Metric.ball (0 : Euc 1) 1) ω =
        continuousExitTime
          ((fun w ↦ (0 : Euc 1) + (Real.sqrt ((1 : ℕ) : ℝ))⁻¹ • w) ⁻¹' Metric.ball (0 : Euc 1) 1)
          0 (pathMap (fun (_ : ℝ≥0) (_ : Unit) ↦ (0 : Euc 1)) (fun _ ↦ continuous_const) ω) :=
  ae_openExitTime_eq_continuousExitTime (d := 1) le_rfl (fun _ ↦ continuous_const)
    (ae_of_all _ fun _ t ↦ by simp)

end BrownianExitPositionExample

end LatticeProb
