/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Prob.QuantileLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Prob.Quantile
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Quantiles under weak convergence

For probability measures `μs i → μ` weakly on `ℝ` (convergence in `ProbabilityMeasure ℝ`):
* `IsQuantile.of_tendsto`: if `q i` is a `p`-quantile of `μs i` and `q i → q`, then `q` is a
  `p`-quantile of `μ` (DFGPS.S8 / GM.S1.17, used in DFGPS L2.14 and GM §1.4, l. 589–590).
* `eventually_mem_Ioo_of_tendsto`: quantiles of `μs i` eventually lie within `ε` of
  `[lowerQuantile μ p, upperQuantile μ p]`;
* `tendsto_of_tendsto_of_unique`: if the `p`-quantile of `μ` is unique, every choice of
  `p`-quantiles of `μs i` converges to it;
* the same for random variables converging in distribution (`TendstoInDistribution`) or in
  probability (`TendstoInMeasure`).

Source: the Portmanteau theorem (Billingsley, *Convergence of Probability Measures*, 2nd ed.,
Thm 2.1; mathlib `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`) applied to the closed
half-lines `(-∞,y]`, `[y,∞)`; the rest is an own elementary argument.
-/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric

variable {ι : Type*} {L : Filter ι} {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
  {p : ℝ≥0∞}

/-- **Limits of quantiles are quantiles** (Portmanteau on closed half-lines). -/
theorem IsQuantile.of_tendsto [L.NeBot] (hμ : Tendsto μs L (𝓝 μ)) {qs : ι → ℝ} {q : ℝ}
    (hq : Tendsto qs L (𝓝 q)) (hqs : ∀ᶠ i in L, IsQuantile (μs i : Measure ℝ) p (qs i)) :
    IsQuantile (μ : Measure ℝ) p q := by
  refine ⟨le_measure_Iic_of_forall_lt fun y hy => ?_, le_measure_Ici_of_forall_gt fun y hy => ?_⟩
  · have hev : ∀ᶠ i in L, p ≤ (μs i : Measure ℝ) (Iic y) := by
      filter_upwards [hqs, hq.eventually (eventually_lt_nhds hy)] with i hi hlt
      exact hi.1.trans (measure_mono (Iic_subset_Iic.2 hlt.le))
    exact (le_limsup_of_frequently_le hev.frequently).trans
      (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ isClosed_Iic)
  · have hev : ∀ᶠ i in L, 1 - p ≤ (μs i : Measure ℝ) (Ici y) := by
      filter_upwards [hqs, hq.eventually (eventually_gt_nhds hy)] with i hi hlt
      exact hi.2.trans (measure_mono (Ici_subset_Ici.2 hlt.le))
    exact (le_limsup_of_frequently_le hev.frequently).trans
      (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ isClosed_Ici)

/-- Quantiles of `μs i` eventually lie in `(lowerQuantile μ p - ε, upperQuantile μ p + ε)`. -/
theorem eventually_mem_Ioo_of_tendsto (hp0 : 0 < p) (hp1 : p < 1) (hμ : Tendsto μs L (𝓝 μ))
    {qs : ι → ℝ} (hqs : ∀ᶠ i in L, IsQuantile (μs i : Measure ℝ) p (qs i)) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ i in L, qs i ∈ Ioo (lowerQuantile (μ : Measure ℝ) p - ε)
      (upperQuantile (μ : Measure ℝ) p + ε) := by
  have hlo : (μ : Measure ℝ) (Iic (lowerQuantile (μ : Measure ℝ) p - ε)) < p :=
    measure_Iic_lt_of_lt_lowerQuantile hp0 hp1 (by linarith)
  have hhi : (μ : Measure ℝ) (Ici (upperQuantile (μ : Measure ℝ) p + ε)) < 1 - p :=
    measure_Ici_lt_of_upperQuantile_lt hp0 hp1 (by linarith)
  have hlo' := eventually_lt_of_limsup_lt
    ((ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ isClosed_Iic).trans_lt hlo)
  have hhi' := eventually_lt_of_limsup_lt
    ((ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ isClosed_Ici).trans_lt hhi)
  filter_upwards [hqs, hlo', hhi'] with i hi hl hh
  refine ⟨not_le.1 fun hle => ?_, not_le.1 fun hle => ?_⟩
  · exact absurd (hi.1.trans (measure_mono (Iic_subset_Iic.2 hle))) (not_le.2 hl)
  · exact absurd (hi.2.trans (measure_mono (Ici_subset_Ici.2 hle))) (not_le.2 hh)

/-! ### Random variables -/

section rv
variable {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] {P : ∀ i, Measure (Ω i)}
  [∀ i, IsProbabilityMeasure (P i)] {X : ∀ i, Ω i → ℝ}
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}

/-- `X i → Z` in distribution, `q i` a `p`-quantile of `X i`, `q i → q` ⇒ `q` is a
`p`-quantile of `Z` (DFGPS.S8, GM.S1.17). -/
theorem IsQuantile.of_tendstoInDistribution [L.NeBot] (h : TendstoInDistribution X L Z P P')
    {qs : ι → ℝ} {q : ℝ} (hq : Tendsto qs L (𝓝 q))
    (hqs : ∀ᶠ i in L, IsQuantile ((P i).map (X i)) p (qs i)) : IsQuantile (P'.map Z) p q :=
  IsQuantile.of_tendsto (μs := fun i => ⟨(P i).map (X i), inferInstance⟩)
    (μ := ⟨P'.map Z, inferInstance⟩) h.tendsto hq hqs

end rv

section prob
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ι → Ω → ℝ} {Z : Ω → ℝ}

/-- Convergence in probability version of `IsQuantile.of_tendstoInDistribution`. -/
theorem IsQuantile.of_tendstoInMeasure [L.NeBot] [L.IsCountablyGenerated]
    (h : TendstoInMeasure P X L Z) (hX : ∀ i, AEMeasurable (X i) P)
    {qs : ι → ℝ} {q : ℝ} (hq : Tendsto qs L (𝓝 q))
    (hqs : ∀ᶠ i in L, IsQuantile (P.map (X i)) p (qs i)) : IsQuantile (P.map Z) p q :=
  IsQuantile.of_tendstoInDistribution (h.tendstoInDistribution hX) hq hqs

end prob

end LQGMetric
