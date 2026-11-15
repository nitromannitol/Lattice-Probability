import LatticeProb.Prob.WeakPathExitOscillation
import LatticeProb.Prob.BallClockOscillationEvent
import Mathlib.MeasureTheory.Integral.Indicator

/-! # Probabilities of neighboring ball-exit oscillations -/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace LatticeProb.UnboundedRayIntervalIntegrand

/-- The two exits are finite and the path oscillates by at most `η` between them. -/
def ballExitOscillationGood {d : ℕ} (r₁ r₂ η : ℝ) : Set (Path d) :=
  {f | ballClock f r₁ ≠ ⊤ ∧ ballClock f r₂ ≠ ⊤ ∧
    ∀ s ∈ Icc (ballClock f r₁).toNNReal (ballClock f r₂).toNNReal,
      ∀ t ∈ Icc (ballClock f r₁).toNNReal (ballClock f r₂).toNNReal,
        dist (f s) (f t) ≤ η}

/-- The finite-exit and oscillation event is Borel. -/
theorem measurableSet_ballExitOscillationGood {d : ℕ} (r₁ r₂ η : ℝ) :
    MeasurableSet (ballExitOscillationGood (d := d) r₁ r₂ η) :=
  (measurableSet_ballClock_ne_top r₁).inter
    ((measurableSet_ballClock_ne_top r₂).inter
      (measurableSet_ballClock_oscillation_le r₁ r₂ η))

/-- Weak convergence controls neighboring-exit failure probabilities at a regular radius. -/
theorem tendsto_measure_ballExitOscillationGood_compl
    {d : ℕ} {μ : ProbabilityMeasure (Path d)} {μs : ℕ → ProbabilityMeasure (Path d)}
    (hweak : Tendsto μs atTop (𝓝 μ)) {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) {r η : ℝ} (hη : 0 < η)
    (hregular : ∀ᵐ (f : Path d) ∂(μ : Measure (Path d)),
      ¬ Bornology.IsBounded (Set.range f) ∧
        ContinuousAt (fun s : ℝ => ballClock f s) r) :
    Tendsto (fun n => (μs n : Measure (Path d))
      (ballExitOscillationGood (r - δ n) (r + δ n) η)ᶜ) atTop (𝓝 0) := by
  let : PolishSpace (Path d) := LatticeProb.polishSpace_continuousMap _ _
  let := TopologicalSpace.upgradeIsCompletelyMetrizable (Path d)
  obtain ⟨Ω, mΩ, P, hP, Y, Y₀, hY, hY₀, hmap, hmap₀, hconv⟩ :=
    LatticeProb.Skorokhod.exists_skorokhod_representation hweak
  have hreg : ∀ᵐ ω ∂P, ¬ Bornology.IsBounded (Set.range (Y₀ ω)) ∧
      ContinuousAt (fun s : ℝ => ballClock (Y₀ ω) s) r := by
    have hpull : ∀ᵐ (f : Path d) ∂P.map Y₀,
        ¬ Bornology.IsBounded (Set.range f) ∧
          ContinuousAt (fun s : ℝ => ballClock f s) r := by
      rw [hmap₀]
      exact hregular
    exact ae_of_ae_map hY₀.aemeasurable hpull
  let A : ℕ → Set (Path d) := fun n =>
    (ballExitOscillationGood (r - δ n) (r + δ n) η)ᶜ
  have hmeas : ∀ n, MeasurableSet (A n) := fun n =>
    (measurableSet_ballExitOscillationGood _ _ _).compl
  have ha : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ Y n ⁻¹' A n ↔ ω ∈ (∅ : Set Ω) := by
    filter_upwards [hconv, hreg] with ω hc hr
    have hm : Tendsto (fun n => r - δ n) atTop (𝓝 r) := by
      simpa only [sub_zero] using (tendsto_const_nhds.sub hδ)
    have hp : Tendsto (fun n => r + δ n) atTop (𝓝 r) := by
      simpa only [add_zero] using (tendsto_const_nhds.add hδ)
    have hlim : ballClock (Y₀ ω) r < ⊤ :=
      lt_top_iff_ne_top.mpr (ballClock_ne_top ⟨Y₀ ω, hr.1⟩ r)
    have hf₁ : ∀ᶠ n in atTop, ballClock (Y n ω) (r - δ n) ≠ ⊤ := by
      have h := tendsto_ballClock_of_continuousAt_radius (hc.prodMk_nhds hm) hr.1 hr.2
      filter_upwards [h (Iio_mem_nhds hlim)] with n hn
      exact ne_of_lt hn
    have hf₂ : ∀ᶠ n in atTop, ballClock (Y n ω) (r + δ n) ≠ ⊤ := by
      have h := tendsto_ballClock_of_continuousAt_radius (hc.prodMk_nhds hp) hr.1 hr.2
      filter_upwards [h (Iio_mem_nhds hlim)] with n hn
      exact ne_of_lt hn
    have ho := eventually_ballClock_neighbor_oscillation_lt hc hδ hr.1 hr.2 hη
    filter_upwards [hf₁, hf₂, ho] with n h₁ h₂ hn
    simp only [mem_preimage, mem_empty_iff_false, iff_false, A, mem_compl_iff, not_not]
    exact ⟨h₁, h₂, fun s hs t ht => le_of_lt (hn s hs t ht)⟩
  have ht := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    (μ := P) (A := (∅ : Set Ω)) MeasurableSet.empty
    (fun n => (hmeas n).preimage (hY n)) ha
  simp only [measure_empty] at ht
  have heq (n : ℕ) : (μs n : Measure (Path d)) (A n) = P (Y n ⁻¹' A n) := by
    rw [← hmap n, Measure.map_apply (hY n) (hmeas n)]
  simpa only [← heq, A] using ht

/-- The same conclusion holds for random paths on any probability space with the
specified marginal laws; no joint law with the Skorokhod coupling is required. -/
theorem tendsto_measure_ballExitOscillationGood_compl_of_map_eq
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X : ℕ → Ω → Path d} (hX : ∀ n, AEMeasurable (X n) P)
    {μ : ProbabilityMeasure (Path d)} {μs : ℕ → ProbabilityMeasure (Path d)}
    (hmap : ∀ n, P.map (X n) = (μs n : Measure (Path d)))
    (hweak : Tendsto μs atTop (𝓝 μ)) {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) {r η : ℝ} (hη : 0 < η)
    (hregular : ∀ᵐ (f : Path d) ∂(μ : Measure (Path d)),
      ¬ Bornology.IsBounded (Set.range f) ∧
        ContinuousAt (fun s : ℝ => ballClock f s) r) :
    Tendsto (fun n => P ((X n) ⁻¹'
      (ballExitOscillationGood (r - δ n) (r + δ n) η)ᶜ)) atTop (𝓝 0) := by
  have heq (n : ℕ) : P ((X n) ⁻¹'
      (ballExitOscillationGood (r - δ n) (r + δ n) η)ᶜ) =
      (μs n : Measure (Path d)) (ballExitOscillationGood (r - δ n) (r + δ n) η)ᶜ := by
    rw [← Measure.map_apply_of_aemeasurable (hX n)
      (measurableSet_ballExitOscillationGood _ _ _).compl, hmap n]
  simpa only [heq] using tendsto_measure_ballExitOscillationGood_compl hweak hδ hη hregular

end LatticeProb.UnboundedRayIntervalIntegrand
