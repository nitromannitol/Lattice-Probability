import LatticeProb.LQG.ContMetricLSC
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCMetricInstMeasurableSpace
import LatticeProb.Bonanno.SLUMetricAPI

/-!
# Measurability of continuous metrics as lower semicontinuous metrics

A continuous metric `D` on `ℂ` (`LQGMetric.ContMetric`, local uniform topology and its Borel
σ-algebra, Gwynne-Miller) defines the lower semicontinuous extended metric `contToLSCMetric D`
(`LSCMetric`, carrying the topology of Ding-Gwynne Definition 1.2 on lower semicontinuous
functions and its Borel σ-algebra). We show that `contToLSCMetric` is continuous, hence Borel
measurable: local uniform convergence `D n → D` gives, for every `p n → q`, the convergence
`D n (p n) → D q`, which is the convergence criterion `LSCTendsto` of Ding-Gwynne Definition 1.2.
The space of continuous metrics is first countable (the local uniform topology on `C(ℂ × ℂ, ℝ)`
is), so sequential continuity suffices.

## Main results

* `lscTendsto_contToLSCMetric`: local uniform convergence of continuous metrics gives
  convergence of the extended metrics in the sense of Ding-Gwynne Definition 1.2.
* `continuous_contToLSCMetric`: `contToLSCMetric` is continuous.
* `measurable_contToLSCMetric`: `contToLSCMetric` is measurable.
* `Measurable.contToLSCMetric`: `ω ↦ contToLSCMetric (D ω)` is measurable for measurable `D`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace LatticeProb.LQG

open SupercriticalLQGUniqueness

/-- The space of continuous metrics with the local uniform topology is a sequential space. -/
theorem sequentialSpace_contMetric : SequentialSpace LQGMetric.ContMetric :=
  inferInstanceAs (SequentialSpace ↥{d : C(ℂ × ℂ, ℝ) | LQGMetric.IsContinuousMetric d})

/-- The Borel σ-algebra of the local uniform topology on continuous metrics is contained in the
trace σ-algebra of `C(ℂ × ℂ, ℝ)`. -/
theorem opensMeasurableSpace_contMetric : OpensMeasurableSpace LQGMetric.ContMetric :=
  inferInstanceAs (OpensMeasurableSpace ↥{d : C(ℂ × ℂ, ℝ) | LQGMetric.IsContinuousMetric d})

/-- The value of `contToLSCMetric D`, as a lower semicontinuous function, at `p` is `D p`. -/
theorem toLSCFun_contToLSCMetric_apply (D : LQGMetric.ContMetric) (p : ℂ × ℂ) :
    (LSCMetric.toLSCFun (contToLSCMetric D)).1 p = ((ENNReal.ofReal (D.1 p) : ℝ≥0∞) : EReal) :=
  congrArg (fun x : ℝ≥0∞ => (x : EReal)) (contToLSCMetric_apply D p)

/-- Local uniform convergence of continuous metrics `D n → D₀` gives the convergence of the
extended metrics `contToLSCMetric (D n) → contToLSCMetric D₀` in the sense of Ding-Gwynne
Definition 1.2: along every sequence `p n → q`, `D n (p n) → D₀ q`. -/
theorem lscTendsto_contToLSCMetric {D : ℕ → LQGMetric.ContMetric} {D₀ : LQGMetric.ContMetric}
    (hD : Tendsto D atTop (𝓝 D₀)) :
    LSCTendsto (fun n => (LSCMetric.toLSCFun (contToLSCMetric (D n))).1)
      (LSCMetric.toLSCFun (contToLSCMetric D₀)).1 := by
  have hval : Tendsto (fun n => (D n).1) atTop (𝓝 D₀.1) :=
    (continuous_subtype_val.tendsto D₀).comp hD
  have hc : Continuous fun r : ℝ => ((ENNReal.ofReal r : ℝ≥0∞) : EReal) :=
    continuous_coe_ennreal_ereal.comp ENNReal.continuous_ofReal
  have key : ∀ (p : ℕ → ℂ × ℂ) (q : ℂ × ℂ), Tendsto p atTop (𝓝 q) →
      Tendsto (fun n => (LSCMetric.toLSCFun (contToLSCMetric (D n))).1 (p n)) atTop
        (𝓝 ((LSCMetric.toLSCFun (contToLSCMetric D₀)).1 q)) := by
    intro p q hp
    have hev : Tendsto (fun n => (D n).1 (p n)) atTop (𝓝 (D₀.1 q)) :=
      (continuous_eval.tendsto (D₀.1, q)).comp (hval.prodMk_nhds hp)
    simp only [toLSCFun_contToLSCMetric_apply]
    exact (hc.tendsto (D₀.1 q)).comp hev
  exact ⟨fun p q hp => (key p q hp).liminf_eq.ge,
    fun q => ⟨fun _ => q, tendsto_const_nhds, key _ q tendsto_const_nhds⟩⟩

/-- `contToLSCMetric` is continuous from the continuous metrics with the local uniform topology
to the lower semicontinuous metrics with the topology of Ding-Gwynne Definition 1.2. -/
theorem continuous_contToLSCMetric : Continuous contToLSCMetric := by
  have := sequentialSpace_contMetric
  refine continuous_induced_rng.2 (continuous_iff_seqContinuous.2 fun {D D₀} hD => ?_)
  exact LSCFun.tendsto_of_lscTendsto (lscTendsto_contToLSCMetric hD)

/-- `contToLSCMetric` is measurable from the Borel σ-algebra of the local uniform topology on
continuous metrics to the Borel σ-algebra of the topology of Ding-Gwynne Definition 1.2. -/
theorem measurable_contToLSCMetric : Measurable contToLSCMetric := by
  have := opensMeasurableSpace_contMetric
  have : BorelSpace LSCMetric := ⟨rfl⟩
  exact continuous_contToLSCMetric.measurable

/-- A random continuous metric `D` gives the random lower semicontinuous metric
`ω ↦ contToLSCMetric (D ω)`. -/
theorem _root_.Measurable.contToLSCMetric {Ω : Type*} [MeasurableSpace Ω]
    {D : Ω → LQGMetric.ContMetric} (hD : Measurable D) :
    Measurable fun ω => contToLSCMetric (D ω) :=
  measurable_contToLSCMetric.comp hD

end LatticeProb.LQG
