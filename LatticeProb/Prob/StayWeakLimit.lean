import Mathlib
import LatticeProb.Topology.ContinuousMapBorel
import LatticeProb.Prob.ContinuousMappingAECont
import LatticeProb.Prob.UpcrossStay

/-!
# Weak limits of Brownian motion conditioned to stay above `-δ`

Let `W` be a probability measure on the path space `C(ℝ≥0, ℝ)` (the Wiener measure) and `μ` a drift.
Conditioning `W` on the event `{w | ∀ t, -δ < w t + μ t}` and letting `δ → 0⁺` gives, when it exists,
a weak limit `ν`.  Applying the drift map `w ↦ w + μ t` to the conditioned measures gives the law of
the drifted path conditioned on `staySet δ`, and the pushed-forward weak limit is the weak limit of
these.

* `LatticeProb.tendsto_integral_of_ae_continuousAt_of_eventually_isProbabilityMeasure`: weak
  convergence along a filter of measures that are probability measures eventually, tested on
  bounded functions that are continuous almost everywhere for the limit;
* `LatticeProb.cond_map_eq`: the conditional measure of a push-forward is the push-forward of the
  conditional measure on the preimage;
* `LatticeProb.continuous_driftMap`;
* `LatticeProb.tendsto_integral_cond_staySet_driftMap`: the integral of a bounded measurable
  function, continuous almost everywhere for the pushed-forward limit, against the drifted path
  conditioned on `staySet δ` converges to its integral against the pushed-forward limit.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped ENNReal NNReal BoundedContinuousFunction

noncomputable section

namespace LatticeProb

section General

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [PseudoMetrizableSpace E]
  [BorelSpace E]

/-- **Weak convergence of eventually-probability measures.**  If measures `m i`, which are
probability measures eventually along a countably generated filter, converge weakly to a probability
measure `ν` (their integrals of bounded continuous functions converge), then the integrals of a
bounded Borel function that is continuous `ν`-almost everywhere converge to its `ν`-integral. -/
theorem tendsto_integral_of_ae_continuousAt_of_eventually_isProbabilityMeasure
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {m : ι → Measure E}
    (hm : ∀ᶠ i in l, IsProbabilityMeasure (m i)) {ν : Measure E} [IsProbabilityMeasure ν]
    (h : ∀ f : E →ᵇ ℝ, Tendsto (fun i => ∫ x, f x ∂(m i)) l (𝓝 (∫ x, f x ∂ν)))
    {g : E → ℝ} (hg : Measurable g) (hb : ∃ C, ∀ x, |g x| ≤ C)
    (hc : ∀ᵐ x ∂ν, ContinuousAt g x) :
    Tendsto (fun i => ∫ x, g x ∂(m i)) l (𝓝 (∫ x, g x ∂ν)) := by
  classical
  let q : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  let p : ι → ProbabilityMeasure E := fun i =>
    if hi : IsProbabilityMeasure (m i) then ⟨m i, hi⟩ else q
  have hp : ∀ᶠ i in l, ((p i : ProbabilityMeasure E) : Measure E) = m i := by
    filter_upwards [hm] with i hi
    simp [p, hi]
  have hT : Tendsto p l (𝓝 q) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    refine (h f).congr' ?_
    filter_upwards [hp] with i hi
    rw [hi]
  have key := tendsto_integral_of_ae_continuousAt hT hg hb hc
  refine key.congr' ?_
  filter_upwards [hp] with i hi
  rw [hi]

end General

section Cond

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The conditional measure of a push-forward on a measurable set is the push-forward of the
conditional measure on the preimage. -/
theorem cond_map_eq (W : Measure α) {T : α → β} (hT : Measurable T) {S : Set β}
    (hS : MeasurableSet S) : (W.map T)[|S] = (W[|T ⁻¹' S]).map T := by
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul, Measure.restrict_map hT hS, Measure.map_apply hT hS]
  exact hT.aemeasurable

end Cond

theorem continuous_driftMap (mu : ℝ) : Continuous (driftMap mu) := by
  have : driftMap mu = fun w => w + (⟨fun s : ℝ≥0 => mu * (s : ℝ), by fun_prop⟩ : C(ℝ≥0, ℝ)) := by
    ext w s
    simp
  rw [this]
  exact continuous_id.add continuous_const

/-- **Weak limit of the drifted conditioned path.**  Let `W` be a probability measure on
`C(ℝ≥0, ℝ)` and `ν` a probability measure with
`W[| {w | ∀ t, -δ < w t + μ t}] → ν` weakly as `δ → 0⁺`.  Then for every bounded Borel function `g`
on path space that is continuous almost everywhere for the push-forward of `ν` under the drift
map `w ↦ (t ↦ w t + μ t)`, the integral of `g` against the push-forward of `W` conditioned on
`staySet δ` converges to the integral of `g` against that push-forward of `ν`. -/
theorem tendsto_integral_cond_staySet_driftMap (W : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure W]
    (mu : ℝ) {ν : Measure C(ℝ≥0, ℝ)} [IsProbabilityMeasure ν]
    (hν : ∀ f : C(ℝ≥0, ℝ) →ᵇ ℝ, Tendsto
      (fun δ : ℝ => ∫ w, f w ∂(W[|driftMap mu ⁻¹' staySet δ])) (𝓝[>] 0) (𝓝 (∫ w, f w ∂ν)))
    {g : C(ℝ≥0, ℝ) → ℝ} (hg : Measurable g) (hb : ∃ C, ∀ x, |g x| ≤ C)
    (hc : ∀ᵐ y ∂(ν.map (driftMap mu)), ContinuousAt g y) :
    Tendsto (fun δ : ℝ => ∫ y, g y ∂((W.map (driftMap mu))[|staySet δ])) (𝓝[>] 0)
      (𝓝 (∫ y, g y ∂(ν.map (driftMap mu)))) := by
  have hT : Measurable (driftMap mu) := measurable_driftMap mu
  -- the conditioned measures are eventually probability measures
  have hprob : ∀ᶠ δ : ℝ in 𝓝[>] 0, IsProbabilityMeasure (W[|driftMap mu ⁻¹' staySet δ]) := by
    have h1 := hν 1
    simp only [BoundedContinuousFunction.coe_one, Pi.one_apply, integral_const, smul_eq_mul,
      mul_one, probReal_univ] at h1
    filter_upwards [h1.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with δ hδ
    have hne : W (driftMap mu ⁻¹' staySet δ) ≠ 0 := by
      intro h0
      have h00 : W[|driftMap mu ⁻¹' staySet δ] = 0 := by
        simp [ProbabilityTheory.cond, h0]
      rw [h00] at hδ
      simp at hδ
    exact cond_isProbabilityMeasure hne
  have hcT : ∀ᵐ x ∂ν, ContinuousAt (fun x => g (driftMap mu x)) x := by
    filter_upwards [ae_of_ae_map hT.aemeasurable hc] with x hx
    exact hx.comp (continuous_driftMap mu).continuousAt
  have key := tendsto_integral_of_ae_continuousAt_of_eventually_isProbabilityMeasure hprob hν
    (hg.comp hT) (by obtain ⟨C, hC⟩ := hb; exact ⟨C, fun x => hC _⟩) hcT
  have hEq : ∀ δ : ℝ, ∫ y, g y ∂((W.map (driftMap mu))[|staySet δ])
      = ∫ x, g (driftMap mu x) ∂(W[|driftMap mu ⁻¹' staySet δ]) := by
    intro δ
    rw [cond_map_eq W hT (measurableSet_staySet δ),
      integral_map hT.aemeasurable hg.aestronglyMeasurable]
  simp only [hEq]
  rw [integral_map hT.aemeasurable hg.aestronglyMeasurable]
  exact key

end LatticeProb
