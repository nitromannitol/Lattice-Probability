import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic

/-! # Small-scale parameters for window bounds -/

set_option autoImplicit false

open Filter Set
open scoped Topology ENNReal

namespace LatticeProb.LQG

/-- The power-law window and its smaller scale satisfy the numerical
conditions used in the window estimates for all sufficiently small scales. -/
theorem eventually_power_window_parameters {k a q r : ℝ}
    (hq : 0 < q) (hr : r < 1) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0,
      δ ∈ Ioo (0 : ℝ) 1 ∧ δ ^ (1 - r) ≤ q ∧
      0 < δ ^ k / 4 ∧ 2 * (δ ^ k / 4) ≤ δ ^ k ∧
      0 < (δ ^ k / 4) * δ ^ a := by
  have ht : Tendsto (fun δ : ℝ => δ ^ (1 - r)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 (1 - r) (Or.inr (by linarith))).tendsto
    simpa [Real.zero_rpow (by linarith : 1 - r ≠ 0)] using h.mono_left nhdsWithin_le_nhds
  filter_upwards [Ioo_mem_nhdsGT one_pos, ht.eventually (Iio_mem_nhds hq)] with δ hδ hδq
  have hk : 0 < δ ^ k := Real.rpow_pos_of_pos hδ.1 _
  have ha : 0 < δ ^ a := Real.rpow_pos_of_pos hδ.1 _
  exact ⟨hδ, hδq.le, by positivity, by linarith, by positivity⟩

/-- The numerical upper bound in the power-law window choice vanishes when
all three exponents are positive and the inner coefficient is finite. -/
theorem tendsto_power_window_bound {k a e s : ℝ} {N : ℕ}
    (ha : 0 < a) (he : 0 < e) (hs : 0 < s) (hN : 0 < N)
    (Cexit Carea : ℝ) {Cinner : ℝ≥0∞} (hfinite : Cinner ≠ ⊤) :
    Tendsto (fun δ : ℝ =>
      (ENNReal.ofReal (Cexit * δ ^ N) + ENNReal.ofReal (Carea * δ ^ e)) +
        Cinner * ENNReal.ofReal
          (((((δ ^ k / 4) * δ ^ a)⁻¹) * ((δ ^ k / 4) / 2)) ^ (-s)))
      (𝓝[>] 0) (𝓝 0) := by
  have hp (t : ℝ) (ht : 0 < t) :
      Tendsto (fun δ : ℝ => δ ^ t) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 t (Or.inr ht.le)).tendsto
    simpa [Real.zero_rpow ht.ne'] using h.mono_left nhdsWithin_le_nhds
  have h₁ : Tendsto (fun δ : ℝ => ENNReal.ofReal (Cexit * δ ^ N))
      (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal ((hp (N : ℝ) (by exact_mod_cast hN)).const_mul Cexit)
    simpa only [Real.rpow_natCast, mul_zero, ENNReal.ofReal_zero] using h
  have h₂ : Tendsto (fun δ : ℝ => ENNReal.ofReal (Carea * δ ^ e))
      (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal ((hp e he).const_mul Carea)
    simpa only [mul_zero, ENNReal.ofReal_zero] using h
  have h₃ : Tendsto (fun δ : ℝ =>
      ENNReal.ofReal (((((δ ^ k / 4) * δ ^ a)⁻¹) * ((δ ^ k / 4) / 2)) ^ (-s)))
      (𝓝[>] 0) (𝓝 0) := by
    have hbase : Tendsto (fun δ : ℝ => 2 * δ ^ a) (𝓝[>] 0) (𝓝 0) := by
      simpa using (hp a ha).const_mul 2
    have hpow : Tendsto (fun δ : ℝ => (2 * δ ^ a) ^ s) (𝓝[>] 0) (𝓝 0) := by
      have h := (Real.continuousAt_rpow_const 0 s (Or.inr hs.le)).tendsto.comp hbase
      simpa [Function.comp_def, Real.zero_rpow hs.ne'] using h
    have h := ENNReal.tendsto_ofReal hpow
    simp only [ENNReal.ofReal_zero] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hk : δ ^ k ≠ 0 := (Real.rpow_pos_of_pos hδ _).ne'
    have ha' : δ ^ a ≠ 0 := (Real.rpow_pos_of_pos hδ _).ne'
    congr 1
    rw [Real.rpow_neg_eq_inv_rpow]
    congr 1
    field_simp
  have hinner : Tendsto (fun δ : ℝ => Cinner * ENNReal.ofReal
      (((((δ ^ k / 4) * δ ^ a)⁻¹) * ((δ ^ k / 4) / 2)) ^ (-s)))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul h₃ (Or.inr hfinite)
  simpa only [add_zero] using (h₁.add h₂).add hinner

end LatticeProb.LQG
