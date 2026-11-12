/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17CoreW at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreB
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: swapping `D̂^ε` and `D^ε` on `W̄` (tool for packet P-C)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17:
Step 2 uses the localized metric `D̂^ε` (its locality, T:682), Step 3 the limits of `D^ε` from
Lemma 2.5 (T:1240–1256); Lemma 2.1 (T:648–650, `lem2_1`) says that `D̂^ε_h(·,·;U)` and
`D^ε_h(·,·;U)` differ by a factor tending to `1` uniformly (bounded `U`). Hence along any sequence
`εₙ → 0` along which `𝔞⁻¹ D^εₙ_g(·,·;W̄)` converges uniformly on `W̄ × W̄`, so does
`𝔞⁻¹ D̂^εₙ_g(·,·;W̄)`, to the same limit (deterministic, for a field `g` with the conclusion of
Lemma 2.1). Decision D80, packet P-C (the `D̂^ε`/`D^ε` swap of Step 1).

* `tendsto_locSqC_of_tendsto_lfppSqC` — the swap for a connected finite union of closed squares.
* `tendsto_locSqC_closure_of_tendsto_lfppSqC` — the same for `W̄`, `W` a dyadic domain.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.L217

open Blueprint LFPP

/-- **the swap in norm** (for the closeness in probability): on a connected finite union `K` of
closed squares, if `D̂^ε ≤ c D^ε` and `D^ε ≤ c D̂^ε` on `K`, then
`‖𝔞⁻¹D̂^ε(·,·;K) − 𝔞⁻¹D^ε(·,·;K)‖_∞ ≤ (c − 1) c ‖𝔞⁻¹D^ε(·,·;K)‖_∞`. -/
theorem norm_locSqC_sub_le {ξ : ℝ} {g : DistC} (𝒮 : Finset (Set ℂ))
    (h𝒮 : ∀ S ∈ 𝒮, ∃ a s, 0 < s ∧ S = closedSq a s) (hK : IsPreconnected (⋃ S ∈ 𝒮, S))
    [CompactSpace (⋃ S ∈ 𝒮, S)] {ε : ℝ} (hε : 0 < ε) (hcont : Continuous (heatMollify ε g))
    {c : ℝ} (hc1 : 1 ≤ c)
    (hr : ∀ z w : ℂ, lfppLocOn ξ ε hε g (⋃ S ∈ 𝒮, S) z w ≤
          ENNReal.ofReal c * lfppDOn ξ (heatMollify ε g) (⋃ S ∈ 𝒮, S) z w ∧
        lfppDOn ξ (heatMollify ε g) (⋃ S ∈ 𝒮, S) z w ≤
          ENNReal.ofReal c * lfppLocOn ξ ε hε g (⋃ S ∈ 𝒮, S) z w) :
    ‖locSqC ξ ε hε g (⋃ S ∈ 𝒮, S) - lfppSqC ξ ε g (⋃ S ∈ 𝒮, S)‖ ≤
      (c - 1) * c * ‖lfppSqC ξ ε g (⋃ S ∈ 𝒮, S)‖ := by
  have hc0 : 0 ≤ (c - 1) * c := mul_nonneg (by linarith) (by linarith)
  refine (ContinuousMap.norm_le _ (mul_nonneg hc0 (norm_nonneg _))).2 fun p => ?_
  have hva : lfppSqC ξ ε g (⋃ S ∈ 𝒮, S) p =
      (aEpsDF ξ ε)⁻¹ * (lfppDOn ξ (heatMollify ε g) (⋃ S ∈ 𝒮, S) p.1 p.2).toReal :=
    toCMap_apply_of_continuous (continuous_lfppDOn_union_toReal hcont 𝒮 h𝒮 hK _) p
  have hvb : locSqC ξ ε hε g (⋃ S ∈ 𝒮, S) p =
      (aEpsDF ξ ε)⁻¹ * (lfppLocOn ξ ε hε g (⋃ S ∈ 𝒮, S) p.1 p.2).toReal :=
    toCMap_apply_of_continuous (continuous_lfppDOn_union_toReal
      (continuous_locMollify ε hε g) 𝒮 h𝒮 hK _) p
  have hnorm : |lfppSqC ξ ε g (⋃ S ∈ 𝒮, S) p| ≤ ‖lfppSqC ξ ε g (⋃ S ∈ 𝒮, S)‖ := by
    simpa [Real.norm_eq_abs] using (lfppSqC ξ ε g (⋃ S ∈ 𝒮, S)).norm_coe_le_norm p
  obtain ⟨h1, h2⟩ := hr p.1 p.2
  have fa := lfppDOn_union_ne_top (ξ := ξ) hcont 𝒮 h𝒮 hK p.1 p.1.2 p.2 p.2.2
  have fb := lfppDOn_union_ne_top (ξ := ξ) (continuous_locMollify ε hε g) 𝒮 h𝒮 hK
    p.1 p.1.2 p.2 p.2.2
  set A := (lfppDOn ξ (heatMollify ε g) (⋃ S ∈ 𝒮, S) p.1 p.2).toReal
  set B := (lfppLocOn ξ ε hε g (⋃ S ∈ 𝒮, S) p.1 p.2).toReal
  have hB : B ≤ c * A := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top fa) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
  have hA : A ≤ c * B := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top fb) h2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  set s := (aEpsDF ξ ε)⁻¹
  have hs : 0 ≤ s := inv_nonneg.2 (aEpsDF_nonneg_sq ξ ε)
  have hsA : s * A ≤ ‖lfppSqC ξ ε g (⋃ S ∈ 𝒮, S)‖ := by
    rw [hva] at hnorm; exact (le_abs_self _).trans hnorm
  rw [ContinuousMap.sub_apply, hvb, hva, Real.norm_eq_abs]
  have k1 : s * B - s * A ≤ (c - 1) * (s * A) := by nlinarith
  have k2 : s * A - s * B ≤ (c - 1) * c * (s * A) := by nlinarith
  have k3 : (c - 1) * (s * A) ≤ (c - 1) * c * (s * A) := by
    have : 0 ≤ (c - 1) * (s * A) := mul_nonneg (by linarith) (mul_nonneg hs hA0)
    nlinarith
  have k4 : (c - 1) * c * (s * A) ≤ (c - 1) * c * ‖lfppSqC ξ ε g (⋃ S ∈ 𝒮, S)‖ :=
    mul_le_mul_of_nonneg_left hsA hc0
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

end LQGMetric.DFGPS.L217
