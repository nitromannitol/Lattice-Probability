import LatticeProb.LQG.ConePowerWindowCount
import LatticeProb.LQG.ConeWindowParameters

/-! # Localized diameter bounds for power-law windows -/

set_option autoImplicit false
open Filter
open scoped Topology NNReal ENNReal

namespace LatticeProb.LQG

/-- The numerical bound for localized diameter, including separate forward and
backward exit tails, vanishes on power-law windows. -/
theorem tendsto_localized_power_window_bound {k a C p β e s : ℝ} {M : ℕ}
    (hka : 0 < k + a) (hC : 0 < C) (hp : 0 < p) (hβ : 0 < β)
    (ha : 0 < a) (he : 0 < e) (hs : 0 < s) (hM : 0 < M)
    (Cforward Cback Cexit Carea : ℝ) (hf : 0 ≤ Cforward) (hb : 0 ≤ Cback)
    {Cinner : ℝ≥0∞} (hfinite : Cinner ≠ ⊤) :
    Tendsto (fun δ : ℝ =>
      let w := δ ^ k / 4
      let b := w * δ ^ a
      let N := ⌈C * (-Real.log b) + 3⌉₊
      (ENNReal.ofReal (b ^ β) + (N : ℝ≥0∞) *
        (ENNReal.ofReal (Cforward * δ ^ p) + ENNReal.ofReal (Cback * δ ^ p))) +
      ((ENNReal.ofReal (Cexit * δ ^ M) + ENNReal.ofReal (Carea * δ ^ e)) +
        Cinner * ENNReal.ofReal ((b⁻¹ * (w / 2)) ^ (-s))))
      (𝓝[>] 0) (𝓝 0) := by
  have ht : Tendsto (fun δ : ℝ => ((δ ^ k / 4) * δ ^ a) ^ β)
      (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto.comp
      ((tendsto_power_window_inner_scale hka).mono_right nhdsWithin_le_nhds)
    simpa [Function.comp_def, Real.zero_rpow hβ.ne'] using h
  have ht' : Tendsto (fun δ : ℝ => ENNReal.ofReal (((δ ^ k / 4) * δ ^ a) ^ β))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal ht
  have hc : Tendsto (fun δ : ℝ => ENNReal.ofReal
      ((⌈C * (-Real.log ((δ ^ k / 4) * δ ^ a)) + 3⌉₊ : ℝ) * δ ^ p))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_power_window_logarithmic_count hka hC hp)
  have hd : Tendsto (fun δ : ℝ =>
      (⌈C * (-Real.log ((δ ^ k / 4) * δ ^ a)) + 3⌉₊ : ℝ≥0∞) *
        (ENNReal.ofReal (Cforward * δ ^ p) + ENNReal.ofReal (Cback * δ ^ p)))
      (𝓝[>] 0) (𝓝 0) := by
    have hcf := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal Cforward) hc
      (Or.inr ENNReal.ofReal_ne_top)
    have hcb := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal Cback) hc
      (Or.inr ENNReal.ofReal_ne_top)
    have hsum := hcf.add hcb
    simp only [mul_zero, add_zero] at hsum
    apply hsum.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [ENNReal.ofReal_mul hf, ENNReal.ofReal_mul hb,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    ring
  have hw := tendsto_power_window_bound (k := k) ha he hs hM Cexit Carea hfinite
  simpa only [add_zero] using (ht'.add hd).add hw

end LatticeProb.LQG
