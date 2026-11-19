import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Convergence in measure under a mixture of measures

Let `κ : Z → Measure Ω` be a measurable family of measures and `m` a measure on `Z` such that the mixture
`m.bind κ` (the law `∫ κ z m(dz)`) is finite. If `f i → g` in `κ z`-measure for `m`-almost every `z`, then
`f i → g` in `m.bind κ`-measure: for each `ε > 0`,
`(m.bind κ) {ε ≤ edist (f i) g} = ∫⁻ z, κ z {ε ≤ edist (f i) g} ∂m → 0`
by dominated convergence in `z`, with the integrable bound `z ↦ κ z univ`.

* `tendstoInMeasure_bind_of_ae`: measurable `f i` and `g`, any countably generated filter.
* `tendstoInMeasure_bind_of_ae_of_aemeasurable`: `f i` and `g` only almost everywhere measurable for the
  mixture, countable index type; the null sets of the mixture are null for `m`-almost every `κ z`.

Typical use: `Ω` a path space, `κ z` the law of a process started at `z`, and `m` the restriction of
Lebesgue measure to a bounded set of starting points.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace LatticeProb

variable {Z Ω E ι : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
  [PseudoEMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]

/-- Convergence in measure for almost every component of a finite mixture implies convergence in
measure for the mixture (measurable functions). -/
theorem tendstoInMeasure_bind_of_ae {m : Measure Z} {κ : Z → Measure Ω} (hκ : Measurable κ)
    [IsFiniteMeasure (m.bind κ)] {l : Filter ι} [l.IsCountablyGenerated] {f : ι → Ω → E}
    {g : Ω → E} (hf : ∀ i, Measurable (f i)) (hg : Measurable g)
    (h : ∀ᵐ z ∂m, TendstoInMeasure (κ z) f l g) :
    TendstoInMeasure (m.bind κ) f l g := by
  intro ε hε
  have hS : ∀ i, MeasurableSet {x | ε ≤ edist (f i x) (g x)} := fun i =>
    measurableSet_le measurable_const ((hf i).edist hg)
  simp_rw [Measure.bind_apply (hS _) hκ.aemeasurable]
  have key := tendsto_lintegral_filter_of_dominated_convergence (μ := m) (l := l)
    (F := fun i z => κ z {x | ε ≤ edist (f i x) (g x)}) (f := fun _ => 0) (fun z => κ z univ)
    (Eventually.of_forall fun i => (Measure.measurable_coe (hS i)).comp hκ)
    (Eventually.of_forall fun i => Eventually.of_forall fun z => measure_mono (subset_univ _))
    (by
      rw [← Measure.bind_apply MeasurableSet.univ hκ.aemeasurable]
      exact measure_ne_top _ _)
    (h.mono fun z hz => hz ε hε)
  simpa only [lintegral_zero] using key

/-- Convergence in measure for almost every component of a finite mixture implies convergence in
measure for the mixture (functions almost everywhere measurable for the mixture, countable index). -/
theorem tendstoInMeasure_bind_of_ae_of_aemeasurable [Countable ι] {m : Measure Z}
    {κ : Z → Measure Ω} (hκ : Measurable κ) [IsFiniteMeasure (m.bind κ)] {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → Ω → E} {g : Ω → E} (hf : ∀ i, AEMeasurable (f i) (m.bind κ))
    (hg : AEMeasurable g (m.bind κ)) (h : ∀ᵐ z ∂m, TendstoInMeasure (κ z) f l g) :
    TendstoInMeasure (m.bind κ) f l g := by
  have hf' : ∀ᵐ z ∂m, ∀ i, f i =ᵐ[κ z] (hf i).mk (f i) :=
    ae_all_iff.2 fun i => Measure.ae_ae_of_ae_bind hκ.aemeasurable (hf i).ae_eq_mk
  have hg' : ∀ᵐ z ∂m, g =ᵐ[κ z] hg.mk g := Measure.ae_ae_of_ae_bind hκ.aemeasurable hg.ae_eq_mk
  have hmk := tendstoInMeasure_bind_of_ae hκ (fun i => (hf i).measurable_mk) hg.measurable_mk
    (by
      filter_upwards [h, hf', hg'] with z hz hfz hgz
      exact (hz.congr_left hfz).congr_right hgz)
  exact (hmk.congr_left fun i => (hf i).ae_eq_mk.symm).congr_right hg.ae_eq_mk.symm

end LatticeProb
