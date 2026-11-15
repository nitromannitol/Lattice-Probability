import LatticeProb.Prob.BrownianOpenHarmonicExit

/-! # Integrability of continuous observables at Brownian exit -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- A continuous real observable of the exit position from a bounded open set
is integrable, including when the Brownian motion starts outside the set. -/
theorem integrable_continuous_openExit {d : ℕ} (hd : 1 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {x : Euc d} {B : ℝ≥0 → Ω → Euc d} (hB : IsBrownianSpace d x B P)
    {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {f : Euc d → ℝ} (hf : Continuous f) :
    Integrable (fun ω => f (B (openExitTime B U ω).toNNReal ω)) P := by
  have := hB.isProbabilityMeasure
  obtain ⟨M, hM⟩ := (hUb.isCompact_closure.insert x).bddAbove_image hf.norm.continuousOn
  have hbound : ∀ᵐ ω ∂P, ‖f (B (openExitTime B U ω).toNNReal ω)‖ ≤ M := by
    filter_upwards [hB.start, hB.cont, ae_openExitTime_ne_top hd hB hUb]
      with ω hstart hcont hfin
    apply hM
    refine ⟨_, ?_, rfl⟩
    by_cases hx : x ∈ U
    · right
      exact frontier_subset_closure (openExitTime_mem_frontier hU hcont (by rwa [hstart]) hfin)
    · left
      have hz : openExitTime B U ω = 0 := openExitTime_eq_zero_of_not_mem (by rwa [hstart])
      simp [hz, hstart]
  obtain ⟨C, hCm, hC, -, hCW, -, -⟩ := hB.exists_continuousVersion
  have hsd : Real.sqrt (d : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  have hF : Measurable (pathMap C hC) := measurable_pathMap C hCm hC
  have hVo : IsOpen ((fun w : Euc d => x + (Real.sqrt d)⁻¹ • w) ⁻¹' U) :=
    hU.preimage (by fun_prop)
  have hτ := measurable_continuousExitTime hVo 0
  have hG : Measurable (fun γ : BrownianPath d =>
      f (x + (Real.sqrt d)⁻¹ • γ (continuousExitTime
        ((fun w : Euc d => x + (Real.sqrt d)⁻¹ • w) ⁻¹' U) 0 γ).toNNReal)) := by
    exact hf.measurable.comp ((by fun_prop : Measurable (fun v : Euc d =>
      x + (Real.sqrt d)⁻¹ • v)).comp (measurable_eval_random_time hτ))
  have hmeas : AEStronglyMeasurable
      (fun ω => f (B (openExitTime B U ω).toNNReal ω)) P := by
    apply (hG.comp hF).aestronglyMeasurable.congr
    filter_upwards [ae_openExitTime_eq_continuousExitTime hd hC hCW, hCW] with ω h1 h2
    rw [h1]
    simp only [Function.comp_apply]
    congr 1
    simp [h2, inv_smul_smul₀ hsd]
  exact (integrable_const M).mono' hmeas hbound

end LatticeProb
