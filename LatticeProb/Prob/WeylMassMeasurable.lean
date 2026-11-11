import Mathlib

/-!
# Weighted masses of random measures: measurability and approximation (general measure theory)

Namespace `LatticeProb.Prob`. Only Mathlib is imported, and no Harmonic-balls object occurs in a statement.
Adapted from the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795], where three facts below are used in the derivation of the
almost-everywhere measurability of Weyl-shifted LQG masses:

* `measurable_lintegral_of_caratheodory`: if `h : Ω → ℂ → ℝ` is measurable in `ω` for each `z` and continuous in `z`
  for each `ω`, then `ω ↦ ∫⁻ z, φ z * G (h ω z)` is measurable (Fubini for a Carathéodory integrand).
* `exists_approx_indicator_of_compact`: for a nonempty compact `S ⊆ ℂ` and a continuous weight `w` with `0 ≤ w ≤ 1`,
  continuous compactly supported functions `ψ n` with `0 ≤ ψ n ≤ 1`, vanishing off `cthickening 1 S`, such that
  `ψ n z = S.indicator w z` for all large `n`.
* `tendsto_lintegral_approx_withDensity`: for a locally finite measure `m`, the integrals `∫⁻ ofReal (ψ n) ∂m` tend to
  `(m.withDensity (ofReal ∘ w)) S` (dominated convergence, dominating function `(cthickening 1 S).indicator 1`).
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LatticeProb.Prob

universe u

/-- Measurability of `ω ↦ ∫⁻ z, φ z * G (h ω z)` for a Carathéodory integrand: `h ω z` is measurable in `ω` for each
`z` and continuous in `z` for each `ω`. The joint measurability of `(ω, z) ↦ h ω z` is Mathlib's
`measurable_uncurry_of_continuous_of_measurable`; the integral is then Fubini's `lintegral_prod_right'`. -/
theorem measurable_lintegral_of_caratheodory {Ω : Type u} [MeasurableSpace Ω] (h : Ω → ℂ → ℝ)
    (hm : ∀ z, Measurable fun ω => h ω z) (hc : ∀ ω, Continuous (h ω))
    {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    Measurable fun ω => ∫⁻ z, φ z * G (h ω z) := by
  have hjoint : Measurable fun p : ℂ × Ω => h p.2 p.1 :=
    measurable_uncurry_of_continuous_of_measurable (u := fun z ω => h ω z) hc hm
  have hF : Measurable fun q : Ω × ℂ => φ q.2 * G (h q.1 q.2) :=
    (hφ.comp measurable_snd).mul (hG.comp (hjoint.comp measurable_swap))
  exact hF.lintegral_prod_right'

/-- Continuous compactly supported approximations from above of `S.indicator w`, for a nonempty compact `S ⊆ ℂ` and a
continuous weight `w` with `0 ≤ w ≤ 1`: `ψ n z = max 0 (1 - (n + 1) · dist(z, S)) * w z`. -/
theorem exists_approx_indicator_of_compact {S : Set ℂ} (hSc : IsCompact S) (hSne : S.Nonempty)
    {w : ℂ → ℝ} (hw : Continuous w) (hw0 : ∀ z, 0 ≤ w z) (hw1 : ∀ z, w z ≤ 1) :
    ∃ ψ : ℕ → ℂ → ℝ, (∀ n, Continuous (ψ n)) ∧ (∀ n, HasCompactSupport (ψ n)) ∧
      (∀ n z, 0 ≤ ψ n z) ∧ (∀ n z, ψ n z ≤ 1) ∧ (∀ n z, z ∉ cthickening 1 S → ψ n z = 0) ∧
      (∀ z, ∀ᶠ n in atTop, ψ n z = S.indicator w z) := by
  have hK : IsCompact (cthickening 1 S) := hSc.cthickening
  have hφc : ∀ n : ℕ, Continuous fun z => max 0 (1 - ((n : ℝ) + 1) * infDist z S) := fun n =>
    continuous_const.max (continuous_const.sub (continuous_const.mul (continuous_infDist_pt S)))
  -- a point at distance at least one from `S` lies outside `cthickening 1 S`
  have hfar : ∀ z, z ∉ cthickening 1 S → 1 ≤ infDist z S := by
    intro z hz
    by_contra hlt
    obtain ⟨y, hy, hdy⟩ := (infDist_lt_iff hSne).1 (not_le.1 hlt)
    exact hz (mem_cthickening_of_dist_le z y 1 S hy hdy.le)
  have hzero : ∀ n : ℕ, ∀ z, z ∉ cthickening 1 S → max 0 (1 - ((n : ℝ) + 1) * infDist z S) = 0 := by
    intro n z hz
    have h1 := hfar z hz
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    apply max_eq_left
    nlinarith
  refine ⟨fun n z => max 0 (1 - ((n : ℝ) + 1) * infDist z S) * w z, fun n => (hφc n).mul hw,
    fun n => HasCompactSupport.intro hK fun z hz => by simp only [hzero n z hz, zero_mul],
    fun n z => mul_nonneg (le_max_left _ _) (hw0 z), fun n z => ?_,
    fun n z hz => by simp only [hzero n z hz, zero_mul], fun z => ?_⟩
  · have h1 : max 0 (1 - ((n : ℝ) + 1) * infDist z S) ≤ 1 := by
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) (infDist_nonneg (x := z) (s := S))
      exact max_le zero_le_one (by linarith)
    exact (mul_le_mul_of_nonneg_right h1 (hw0 z)).trans (by simpa using hw1 z)
  · by_cases hz : z ∈ S
    · refine Eventually.of_forall fun n => ?_
      simp [infDist_zero_of_mem hz, Set.indicator_of_mem hz]
    · have hpos : 0 < infDist z S := (hSc.isClosed.notMem_iff_infDist_pos hSne).1 hz
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / infDist z S)
      filter_upwards [eventually_ge_atTop N] with n hn
      have hn' : (1 : ℝ) < (n : ℝ) * infDist z S := by
        have : 1 / infDist z S < n := lt_of_lt_of_le hN (by exact_mod_cast hn)
        exact (div_lt_iff₀ hpos).1 this
      have hle : 1 - ((n : ℝ) + 1) * infDist z S ≤ 0 := by nlinarith
      simp [Set.indicator_of_notMem hz, max_eq_left hle]

/-- Dominated convergence for the approximations of `m.withDensity (ofReal ∘ w)` on a compact set `S`: if `ψ n` are
continuous, `0 ≤ ψ n ≤ 1`, vanish off `cthickening 1 S`, and `ψ n z = S.indicator w z` for large `n`, then
`∫⁻ ofReal (ψ n) ∂m → m.withDensity (ofReal ∘ w) S` for every locally finite measure `m` on `ℂ`. -/
theorem tendsto_lintegral_approx_withDensity {m : Measure ℂ} [IsLocallyFiniteMeasure m]
    {S : Set ℂ} (hSc : IsCompact S) {w : ℂ → ℝ}
    {ψ : ℕ → ℂ → ℝ} (hψc : ∀ n, Continuous (ψ n)) (hψ1 : ∀ n z, ψ n z ≤ 1)
    (hψK : ∀ n z, z ∉ cthickening 1 S → ψ n z = 0) (hψlim : ∀ z, ∀ᶠ n in atTop, ψ n z = S.indicator w z) :
    Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (ψ n z) ∂m) atTop
      (𝓝 ((m.withDensity fun z => ENNReal.ofReal (w z)) S)) := by
  have hS : MeasurableSet S := hSc.isClosed.measurableSet
  have hK : IsCompact (cthickening 1 S) := hSc.cthickening
  have hKm : MeasurableSet (cthickening 1 S) := hK.isClosed.measurableSet
  have hW : (m.withDensity fun z => ENNReal.ofReal (w z)) S
      = ∫⁻ z, S.indicator (fun z => ENNReal.ofReal (w z)) z ∂m := by
    rw [withDensity_apply _ hS, lintegral_indicator hS]
  rw [hW]
  refine tendsto_lintegral_of_dominated_convergence ((cthickening 1 S).indicator fun _ => (1 : ℝ≥0∞))
    (fun n => ENNReal.measurable_ofReal.comp (hψc n).measurable) (fun n => ?_) ?_ ?_
  · refine Eventually.of_forall fun z => ?_
    dsimp only
    by_cases hz : z ∈ cthickening 1 S
    · rw [indicator_of_mem hz]
      exact ENNReal.ofReal_le_one.2 (hψ1 n z)
    · rw [indicator_of_notMem hz, hψK n z hz, ENNReal.ofReal_zero]
  · rw [lintegral_indicator_const hKm, one_mul]
    exact hK.measure_lt_top.ne
  · refine ae_of_all _ fun z => ?_
    by_cases hz : z ∈ S
    · have hev : (fun n => ENNReal.ofReal (ψ n z)) =ᶠ[atTop] fun _ => ENNReal.ofReal (w z) :=
        (hψlim z).mono fun n hn => by dsimp only; rw [hn, indicator_of_mem hz]
      rw [indicator_of_mem hz]
      exact tendsto_const_nhds.congr' hev.symm
    · have hev : (fun n => ENNReal.ofReal (ψ n z)) =ᶠ[atTop] fun _ => (0 : ℝ≥0∞) :=
        (hψlim z).mono fun n hn => by dsimp only; rw [hn, indicator_of_notMem hz, ENNReal.ofReal_zero]
      rw [indicator_of_notMem hz]
      exact tendsto_const_nhds.congr' hev.symm

end LatticeProb.Prob
