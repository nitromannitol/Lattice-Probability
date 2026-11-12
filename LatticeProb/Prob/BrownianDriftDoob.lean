/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.BrownianExpMartingale
import LatticeProb.Prob.BrownianDriftSurvival

/-!
# Doob's maximal inequality for drifted Brownian motion on an event of the past

For a pre-Brownian motion `B`, `c > 0`, a time `T` and an event `G` of the natural σ-algebra at
time `T`, the chance that `G` happens and `B s + c s` goes below a level `K` at some time `s ≥ T`
is at most `exp (2 c K) ∫_G exp (-2 c (B_T + c T))`.  This is Doob's maximal inequality for the
nonnegative martingale `1_G exp (-2 c (B_s + c s))`, `s ≥ T`; the continuum version uses path
continuity and a dyadic exhaustion.
-/

open MeasureTheory ProbabilityTheory Filter MeasurableSpace Topology
open scoped ENNReal NNReal

namespace LatticeProb

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A martingale restricted to an event of the initial σ-algebra is a martingale. -/
theorem martingale_indicator_nat [IsFiniteMeasure P] {𝒢 : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (hM : Martingale M 𝒢 P) {G : Set Ω} (hG : MeasurableSet[𝒢 0] G) :
    Martingale (fun k => G.indicator (M k)) 𝒢 P := by
  have hGk : ∀ k, MeasurableSet[𝒢 k] G := fun k => 𝒢.mono (Nat.zero_le k) _ hG
  refine ⟨fun k => (hM.1 k).indicator (hGk k), fun i j hij => ?_⟩
  have h0 := condExp_indicator (hM.integrable j) (hGk i)
  filter_upwards [h0, hM.2 i j hij] with ω h1 h2
  rw [h1]
  by_cases hω : ω ∈ G <;> simp [Set.indicator, hω, h2]

/-- **Doob's maximal inequality for drifted Brownian motion, restricted to an event of the past**
(discrete times).  If `t` is a monotone sequence of times with `t 0 = T` and `G` is measurable for
the natural σ-algebra at time `T`, then the chance that `G` happens and `B (t k) + c t k ≤ K` for
some `k ≤ n` is at most `exp (2 c K) ∫_G exp (-2 c (B_T + c T))`. -/
theorem measure_inter_exists_drift_le (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    {c : ℝ} (hc : 0 < c) {t : ℕ → ℝ≥0} (ht : Monotone t) (T : ℝ≥0) (ht0 : t 0 = T) {G : Set Ω}
    (hG : MeasurableSet[brownianFiltration B hm T] G) (n : ℕ) (K : ℝ) :
    P (G ∩ {ω | ∃ k ≤ n, B (t k) ω + c * t k ≤ K}) ≤
      ENNReal.ofReal (Real.exp (2 * c * K) *
        ∫ ω in G, Real.exp (-(2 * c) * (B T ω + c * T)) ∂P) := by
  subst ht0
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let 𝒢 : Filtration ℕ mΩ := gridFiltration B hm t ht
  let M : ℕ → Ω → ℝ := fun k ω => Real.exp (-(2 * c) * (B (t k) ω + c * t k))
  have hmart : Martingale M 𝒢 P :=
    ⟨fun k => (martingale_exp_drift hB hm c).1 (t k),
      fun i j hij => (martingale_exp_drift hB hm c).2 (t i) (t j) (ht hij)⟩
  have hGm : MeasurableSet[𝒢 0] G := hG
  have hGamb : MeasurableSet G := 𝒢.le 0 _ hGm
  let f : ℕ → Ω → ℝ := fun k => G.indicator (M k)
  have hfm : Martingale f 𝒢 P := martingale_indicator_nat hmart hGm
  have hnn : 0 ≤ f := fun k ω => Set.indicator_nonneg (fun ω _ => (Real.exp_pos _).le) ω
  set ε : ℝ≥0 := (Real.exp (-(2 * c * K))).toNNReal with hε
  have hεpos : (0 : ℝ) < ε := by
    rw [hε, Real.coe_toNNReal _ (Real.exp_pos _).le]
    exact Real.exp_pos _
  have hmax := maximal_ineq hfm.submartingale hnn (ε := ε) n
  set S : Set Ω := {ω | (ε : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    fun k => f k ω} with hS
  have hsub : G ∩ {ω | ∃ k ≤ n, B (t k) ω + c * t k ≤ K} ⊆ S := by
    rintro ω ⟨hωG, k, hk, hX⟩
    have hk' : k ∈ Finset.range (n + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hk)
    refine le_trans ?_ (Finset.le_sup' (fun k => f k ω) hk')
    simp only [f, Set.indicator_of_mem hωG, M]
    rw [hε, Real.coe_toNNReal _ (Real.exp_pos _).le]
    exact Real.exp_le_exp.2 (by nlinarith)
  have hint : ∫ ω in S, f n ω ∂P ≤ ∫ ω in G, Real.exp (-(2 * c) * (B (t 0) ω + c * t 0)) ∂P := by
    calc ∫ ω in S, f n ω ∂P ≤ ∫ ω, f n ω ∂P :=
          setIntegral_le_integral (hfm.integrable n) (Filter.Eventually.of_forall (hnn n))
      _ = ∫ ω in G, M n ω ∂P := integral_indicator hGamb
      _ = ∫ ω in G, M 0 ω ∂P := (hmart.setIntegral_eq (Nat.zero_le n) hGm).symm
  set I : ℝ := ∫ ω in G, Real.exp (-(2 * c) * (B (t 0) ω + c * t 0)) ∂P with hI
  have h1 : (ε : ℝ≥0∞) * P S ≤ ENNReal.ofReal I :=
    hmax.trans (ENNReal.ofReal_le_ofReal hint)
  have hε0 : (ε : ℝ≥0∞) ≠ 0 := by
    have : (ε : ℝ≥0) ≠ 0 := by
      intro h
      rw [h] at hεpos
      simp at hεpos
    exact_mod_cast this
  have h2 : P S ≤ (ε : ℝ≥0∞)⁻¹ * ENNReal.ofReal I :=
    (ENNReal.mul_le_iff_le_inv hε0 ENNReal.coe_ne_top).1 h1
  have hεinv : (ε : ℝ≥0∞)⁻¹ = ENNReal.ofReal (Real.exp (2 * c * K)) := by
    rw [show (ε : ℝ≥0∞) = ENNReal.ofReal (Real.exp (-(2 * c * K))) from rfl,
      ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg, neg_neg]
  calc P (G ∩ {ω | ∃ k ≤ n, B (t k) ω + c * t k ≤ K}) ≤ P S := measure_mono hsub
    _ ≤ (ε : ℝ≥0∞)⁻¹ * ENNReal.ofReal I := h2
    _ = ENNReal.ofReal (Real.exp (2 * c * K) * I) := by
        rw [hεinv, ENNReal.ofReal_mul (Real.exp_pos _).le]

theorem dyadicGrid_succ_two_mul (N k : ℕ) : dyadicGrid (N + 1) (2 * k) = dyadicGrid N k := by
  simp only [dyadicGrid]
  push_cast
  rw [pow_succ]
  field_simp

/-- **Doob's maximal inequality for drifted Brownian motion after time `T`**, for an event of the
past (continuous paths): if `G` is measurable for the natural σ-algebra at time `T`, the chance
that `G` happens and `B s + c s < K` for some `s ≥ T` is at most
`exp (2 c K) ∫_G exp (-2 c (B_T + c T))`. -/
theorem measure_inter_exists_ge_drift_lt_le (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {c : ℝ} (hc : 0 < c)
    (T : ℝ≥0) {G : Set Ω} (hG : MeasurableSet[brownianFiltration B hm T] G) (K : ℝ) :
    P (G ∩ {ω | ∃ s : ℝ≥0, T ≤ s ∧ B s ω + c * s < K}) ≤
      ENNReal.ofReal (Real.exp (2 * c * K) *
        ∫ ω in G, Real.exp (-(2 * c) * (B T ω + c * T)) ∂P) := by
  let g : ℕ → ℕ → ℝ≥0 := fun N k => T + dyadicGrid N k
  have hg : ∀ N, Monotone (g N) := fun N a b h => add_le_add le_rfl (dyadicGrid_mono N h)
  have hg0 : ∀ N, g N 0 = T := fun N => by simp [g, dyadicGrid_zero]
  let A : ℕ → Set Ω := fun N =>
    G ∩ {ω | ∃ k ≤ N * 2 ^ N, B (g N k) ω + c * g N k ≤ K}
  have hAmono : Monotone A := by
    refine monotone_nat_of_le_succ fun N ω hω => ?_
    obtain ⟨hωG, k, hk, hX⟩ := hω
    refine ⟨hωG, 2 * k, ?_, ?_⟩
    · calc 2 * k ≤ 2 * (N * 2 ^ N) := by omega
        _ ≤ (N + 1) * 2 ^ (N + 1) := by rw [pow_succ]; nlinarith [Nat.zero_le (2 ^ N)]
    · have : g (N + 1) (2 * k) = g N k := by
        simp only [g, dyadicGrid_succ_two_mul]
      rw [this]
      exact hX
  have hsub : G ∩ {ω | ∃ s : ℝ≥0, T ≤ s ∧ B s ω + c * s < K} ⊆ ⋃ N, A N := by
    rintro ω ⟨hωG, s, hTs, hlt⟩
    have hcg : Continuous fun u : ℝ≥0 => B (T + u) ω + c * ((T + u : ℝ≥0) : ℝ) := by
      have := hcont ω
      fun_prop
    have hlt' : (fun u : ℝ≥0 => B (T + u) ω + c * ((T + u : ℝ≥0) : ℝ)) (s - T) < K := by
      simp only [add_tsub_cancel_of_le hTs]
      exact hlt
    obtain ⟨N, k, hk, hlt''⟩ := exists_dyadic_lt_of_continuous hcg hlt'
    exact Set.mem_iUnion.2 ⟨N, hωG, k, hk, hlt''.le⟩
  calc P (G ∩ {ω | ∃ s : ℝ≥0, T ≤ s ∧ B s ω + c * s < K}) ≤ P (⋃ N, A N) := measure_mono hsub
    _ = ⨆ N, P (A N) := hAmono.measure_iUnion
    _ ≤ _ := iSup_le fun N =>
        measure_inter_exists_drift_le hB hm hc (hg N) T (hg0 N) hG (N * 2 ^ N) K

end LatticeProb
