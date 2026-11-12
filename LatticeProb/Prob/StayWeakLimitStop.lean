import Mathlib
import LatticeProb.Prob.StayWeakLimit
import LatticeProb.Prob.StopHitAeContinuous

/-!
# Weak limits of the conditioned drifted path stopped at its first hit

Under the hypothesis of weak convergence of the Wiener measure conditioned on `staySet δ` (after
the drift map), the path stopped at its first hit of `c` converges weakly as well, for Lebesgue-almost
every level `c > 0`, and the limsup of the measure of any closed set of stopped paths is at most
its limiting measure.

* `LatticeProb.limsup_measure_closed_le_of_eventually_isProbabilityMeasure`: the closed-set
  portmanteau inequality for measures that are eventually probability measures.
* `LatticeProb.ae_tendsto_integral_cond_staySet_stopAtHit`: weak convergence of the stopped paths,
  for almost every level.
* `LatticeProb.ae_limsup_cond_staySet_stopAtHit_closed_le`: the closed-set bound.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped ENNReal NNReal BoundedContinuousFunction

noncomputable section

namespace LatticeProb

/-- The push-forward of a probability measure by an a.e. measurable map is a probability measure. -/
theorem isProb_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → β} (hf : AEMeasurable f μ) : IsProbabilityMeasure (μ.map f) :=
  (Measure.isProbabilityMeasure_map_iff hf).2 inferInstance

/-- **Portmanteau, closed sets, for measures that are eventually probability measures.** If
`∫ f dP i → ∫ f dν` for every bounded continuous `f` along `L`, and `P i` is eventually a probability
measure, then `limsup P i F ≤ ν F` for every closed `F`. -/
theorem limsup_measure_closed_le_of_eventually_isProbabilityMeasure {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {P : ι → Measure Ω} (hP : ∀ᶠ i in L, IsProbabilityMeasure (P i)) {ν : Measure Ω}
    [IsProbabilityMeasure ν]
    (hlim : ∀ f : Ω →ᵇ ℝ, Tendsto (fun i => ∫ x, f x ∂(P i)) L (𝓝 (∫ x, f x ∂ν)))
    {F : Set Ω} (hF : IsClosed F) :
    L.limsup (fun i => P i F) ≤ ν F := by
  classical
  let q : ProbabilityMeasure Ω := ⟨ν, inferInstance⟩
  let Q : ι → ProbabilityMeasure Ω := fun i =>
    if h : IsProbabilityMeasure (P i) then ⟨P i, h⟩ else q
  have hQ : ∀ᶠ i in L, (Q i : Measure Ω) = P i := by
    filter_upwards [hP] with i hi
    simp [Q, hi]
  have hT : Tendsto Q L (𝓝 q) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    refine Tendsto.congr' ?_ (hlim f)
    filter_upwards [hQ] with i hi
    rw [hi]
  have := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hT hF
  refine le_trans (le_of_eq ?_) this
  exact Filter.limsup_congr (hQ.mono fun i hi => by rw [hi])

section Stop

variable (W : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure W] (mu : ℝ)
  {ν : Measure C(ℝ≥0, ℝ)} [IsProbabilityMeasure ν]

/-- If the conditioned Wiener measures converge weakly, they are eventually probability measures,
also after the drift map. -/
theorem eventually_isProbabilityMeasure_cond_driftMap
    (hν : ∀ f : C(ℝ≥0, ℝ) →ᵇ ℝ, Tendsto
      (fun δ : ℝ => ∫ w, f w ∂(W[|driftMap mu ⁻¹' staySet δ])) (𝓝[>] 0) (𝓝 (∫ w, f w ∂ν))) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, IsProbabilityMeasure ((W.map (driftMap mu))[|staySet δ]) := by
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
  have := cond_isProbabilityMeasure hne
  rw [cond_map_eq W (measurable_driftMap mu) (measurableSet_staySet δ)]
  exact isProb_map (measurable_driftMap mu).aemeasurable

/-- **Weak convergence of the stopped paths.**  For Lebesgue-almost every level `c > 0`, the drifted
path conditioned on `staySet δ` and stopped at its first hit of `c` converges weakly, as `δ → 0⁺`, to
the limit path stopped at its first hit of `c`. -/
theorem ae_tendsto_integral_cond_staySet_stopAtHit
    (hν : ∀ f : C(ℝ≥0, ℝ) →ᵇ ℝ, Tendsto
      (fun δ : ℝ => ∫ w, f w ∂(W[|driftMap mu ⁻¹' staySet δ])) (𝓝[>] 0) (𝓝 (∫ w, f w ∂ν))) :
    ∀ᵐ c ∂(volume.restrict (Ioi (0 : ℝ))), ∀ f : C(ℝ≥0, ℝ) →ᵇ ℝ,
      Tendsto (fun δ : ℝ => ∫ y, f (stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y)
          ∂((W.map (driftMap mu))[|staySet δ])) (𝓝[>] 0)
        (𝓝 (∫ y, f (stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y) ∂(ν.map (driftMap mu)))) := by
  have : IsProbabilityMeasure (ν.map (driftMap mu)) :=
    isProb_map (measurable_driftMap mu).aemeasurable
  filter_upwards [ae_ae_continuousAt_stopAtHit (ν.map (driftMap mu))] with c hc f
  have hSm : Measurable fun y : C(ℝ≥0, ℝ) => stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y :=
    measurable_stopAt_path (measurable_hitFrom (r := fun _ => 0) measurable_const c)
  refine tendsto_integral_cond_staySet_driftMap W mu hν
    (g := fun y => f (stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y)) (f.continuous.measurable.comp hSm)
    ⟨‖f‖, fun x => by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm _⟩ ?_
  filter_upwards [hc] with y hy
  exact f.continuous.continuousAt.comp hy

/-- **Closed-set bound for the stopped paths.**  For Lebesgue-almost every level `c > 0` and every
closed set `F` of paths, the limsup as `δ → 0⁺` of the conditional probability that the drifted path
stopped at its first hit of `c` lies in `F` is at most the same probability for the limit path. -/
theorem ae_limsup_cond_staySet_stopAtHit_closed_le
    (hν : ∀ f : C(ℝ≥0, ℝ) →ᵇ ℝ, Tendsto
      (fun δ : ℝ => ∫ w, f w ∂(W[|driftMap mu ⁻¹' staySet δ])) (𝓝[>] 0) (𝓝 (∫ w, f w ∂ν))) :
    ∀ᵐ c ∂(volume.restrict (Ioi (0 : ℝ))), ∀ F : Set C(ℝ≥0, ℝ), IsClosed F →
      (𝓝[>] (0 : ℝ)).limsup (fun δ : ℝ => ((W.map (driftMap mu))[|staySet δ])
          {y | stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y ∈ F}) ≤
        (ν.map (driftMap mu)) {y | stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y ∈ F} := by
  have : IsProbabilityMeasure (ν.map (driftMap mu)) :=
    isProb_map (measurable_driftMap mu).aemeasurable
  filter_upwards [ae_tendsto_integral_cond_staySet_stopAtHit W mu hν] with c hc F hF
  set S : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ) := fun y => stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y with hS
  have hSm : Measurable S :=
    measurable_stopAt_path (measurable_hitFrom (r := fun _ => 0) measurable_const c)
  have hP : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      IsProbabilityMeasure (((W.map (driftMap mu))[|staySet δ]).map S) := by
    filter_upwards [eventually_isProbabilityMeasure_cond_driftMap W mu hν] with δ hδ
    exact isProb_map hSm.aemeasurable
  have : IsProbabilityMeasure ((ν.map (driftMap mu)).map S) :=
    isProb_map hSm.aemeasurable
  have hlim : ∀ f : C(ℝ≥0, ℝ) →ᵇ ℝ, Tendsto
      (fun δ : ℝ => ∫ x, f x ∂(((W.map (driftMap mu))[|staySet δ]).map S)) (𝓝[>] 0)
      (𝓝 (∫ x, f x ∂((ν.map (driftMap mu)).map S))) := by
    intro f
    have e : ∀ m : Measure C(ℝ≥0, ℝ), ∫ x, f x ∂(m.map S) = ∫ y, f (S y) ∂m := fun m =>
      integral_map hSm.aemeasurable f.continuous.aestronglyMeasurable
    simp only [e]
    exact hc f
  have key := limsup_measure_closed_le_of_eventually_isProbabilityMeasure hP hlim hF
  simp only [Measure.map_apply hSm hF.measurableSet] at key
  exact key

end Stop

end LatticeProb
