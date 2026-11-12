/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7E5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7E2

/-!
# LM Lemma 5.1 and (5.11) under the conditional law `κ_g` (kernel form, packet P-ES)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`): the proof of Theorem 1.7 works "under the conditional law given `h`"
(l. 1011–1026), and the open node `LMT17VarNodeK` (Papers/LM/T1_7L2.lean, decision D111) is stated
for `law(h)`-a.e. `g` under `κ_g := condDistrib D h P g`. This file gives the two bi-Lipschitz
inputs in that form.

* `t17e_copy_kernel` — the hypothesis of LM Theorem 1.7 (l. 308–310, `D̃ ≤ C_h D` for the
  conditionally i.i.d. copy) as: for `law(h)`-a.e. `g`, `κ_g ⊗ κ_g`-a.s. `d' ≤ C(g) d` everywhere
  (`condCopyMeasure_map_triple`, countably many pairs and continuity).
* `t17e_condBded_measure` — LM Lemma 5.1 (l. 904–929) for one probability measure `ν` (`= κ_g`):
  if `ν ⊗ ν`-a.s. `f(d') ≤ c f(d)`, then `ν`-a.s. `∫ f dν ≤ c f(d)` and `f(d) ≤ c ∫ f dν` (Fubini;
  the same argument as `c18_condBded`).
* `t17e_bilip_measure` — **LM (5.11)** (l. 1030–1036) under `ν = κ_g`: for any coupling `π` of two
  random metrics both with law `ν` (e.g. `(D, D^S)`), `π`-a.s. `d₂ ≤ c² d₁` everywhere.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint

/-- **LM Lemma 5.1** for one measure: the essential-bound sandwich from the copy bound. -/
theorem t17e_condBded_measure {β : Type*} [MeasurableSpace β] {ν : Measure β}
    [IsProbabilityMeasure ν] {f : β → ℝ≥0∞} (hf : Measurable f) (c : ℝ≥0∞)
    (hle : ∀ᵐ p ∂ν.prod ν, f p.2 ≤ c * f p.1) :
    ∀ᵐ y ∂ν, (∫⁻ y', f y' ∂ν) ≤ c * f y ∧ f y ≤ c * ∫⁻ y', f y' ∂ν := by
  have hSx : MeasurableSet {p : β × β | f p.2 ≤ c * f p.1} :=
    measurableSet_le (hf.comp measurable_snd) (measurable_const.mul (hf.comp measurable_fst))
  have hA : ∀ᵐ y ∂ν, ∀ᵐ y' ∂ν, f y' ≤ c * f y :=
    Measure.ae_ae_of_ae_prod (p := fun p : β × β => f p.2 ≤ c * f p.1) hle
  have hB : ∀ᵐ y' ∂ν, ∀ᵐ y ∂ν, f y' ≤ c * f y := (Measure.ae_ae_comm hSx).1 hA
  filter_upwards [hA, hB] with y hy hy'
  constructor
  · calc (∫⁻ y', f y' ∂ν) ≤ ∫⁻ _, c * f y ∂ν := lintegral_mono_ae hy
      _ = c * f y := by rw [lintegral_const, measure_univ, mul_one]
  · calc f y = ∫⁻ _, f y ∂ν := by rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ y'', c * f y'' ∂ν := lintegral_mono_ae hy'
      _ = c * ∫⁻ y'', f y'' ∂ν := lintegral_const_mul _ hf

/-- **LM (5.11)** under one law `ν`: if `ν ⊗ ν`-a.s. `d' ≤ c d` everywhere, then for any coupling
`π` with both marginals `ν`, `π`-a.s. `d₂ ≤ c² d₁` everywhere. -/
theorem t17e_bilip_measure {ν : Measure ContMetric} [IsProbabilityMeasure ν] {c : ℝ} (hc : 0 ≤ c)
    (hcopy : ∀ᵐ p ∂ν.prod ν, ∀ z w : ℂ, p.2.1 (z, w) ≤ c * p.1.1 (z, w))
    {π : Measure (ContMetric × ContMetric)} (h1 : π.map Prod.fst = ν) (h2 : π.map Prod.snd = ν) :
    ∀ᵐ p ∂π, ∀ x y : ℂ, p.2.1 (x, y) ≤ c ^ 2 * p.1.1 (x, y) := by
  have hpair : ∀ q : ℂ × ℂ, ∀ᵐ p ∂π, p.2.1 q ≤ c ^ 2 * p.1.1 q := by
    intro q
    set f : ContMetric → ℝ≥0∞ := fun d => ENNReal.ofReal (d.1 q) with hfdef
    have hf : Measurable f := ENNReal.measurable_ofReal.comp (t17e_measurable_apply q)
    have hle : ∀ᵐ p ∂ν.prod ν, f p.2 ≤ ENNReal.ofReal c * f p.1 := by
      filter_upwards [hcopy] with p hp
      rw [hfdef, ← ENNReal.ofReal_mul hc]
      exact ENNReal.ofReal_le_ofReal (hp q.1 q.2)
    have hb := t17e_condBded_measure hf _ hle
    set I := ∫⁻ y', f y' ∂ν
    have hS1 : MeasurableSet {d : ContMetric | I ≤ ENNReal.ofReal c * f d} :=
      measurableSet_le measurable_const (measurable_const.mul hf)
    have hS2 : MeasurableSet {d : ContMetric | f d ≤ ENNReal.ofReal c * I} :=
      measurableSet_le hf measurable_const
    have hb1 : ∀ᵐ p ∂π, I ≤ ENNReal.ofReal c * f p.1 := by
      have : ∀ᵐ d ∂π.map Prod.fst, I ≤ ENNReal.ofReal c * f d := by
        rw [h1]; filter_upwards [hb] with d hd using hd.1
      exact (ae_map_iff measurable_fst.aemeasurable hS1).1 this
    have hb2 : ∀ᵐ p ∂π, f p.2 ≤ ENNReal.ofReal c * I := by
      have : ∀ᵐ d ∂π.map Prod.snd, f d ≤ ENNReal.ofReal c * I := by
        rw [h2]; filter_upwards [hb] with d hd using hd.2
      exact (ae_map_iff measurable_snd.aemeasurable hS2).1 this
    filter_upwards [hb1, hb2] with p hp1 hp2
    have key : f p.2 ≤ ENNReal.ofReal (c ^ 2 * p.1.1 q) := by
      rw [pow_two, ENNReal.ofReal_mul (mul_nonneg hc hc), ENNReal.ofReal_mul hc, mul_assoc]
      exact hp2.trans (by gcongr)
    have hd0 : 0 ≤ p.1.1 q := (dist_nonneg : 0 ≤ dist (p.1.pt q.1) (p.1.pt q.2))
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (pow_two_nonneg _) hd0)).1 key
  have hall : ∀ᵐ p ∂π, ∀ n : ℕ, p.2.1 (TopologicalSpace.denseSeq (ℂ × ℂ) n) ≤
      c ^ 2 * p.1.1 (TopologicalSpace.denseSeq (ℂ × ℂ) n) :=
    ae_all_iff.2 fun n => hpair _
  filter_upwards [hall] with p hp x y
  exact (TopologicalSpace.denseRange_denseSeq (ℂ × ℂ)).induction_on (x, y)
    (isClosed_le p.2.1.continuous (continuous_const.mul p.1.1.continuous)) hp

/-- **The copy bound under `κ_g`**: the hypothesis of LM Theorem 1.7 gives, for `law(h)`-a.e. `g`,
`κ_g ⊗ κ_g`-a.s. `d' ≤ C(g) d` everywhere. -/
theorem t17e_copy_kernel {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} {D : Ω → ContMetric} (hm : Measurable h) (hD : Measurable D)
    {C : DistC → ℝ} (hCm : Measurable C)
    (hcopy : ∀ᵐ q ∂condCopyMeasure D h P hm, ∀ z w : ℂ,
      q.2.1 (z, w) ≤ C (h q.1) * (D q.1).1 (z, w)) :
    ∀ᵐ g ∂P.map h, ∀ᵐ p ∂(condDistrib D h P g).prod (condDistrib D h P g),
      ∀ z w : ℂ, p.2.1 (z, w) ≤ C g * p.1.1 (z, w) := by
  set κ := condDistrib D h P
  set s := TopologicalSpace.denseSeq (ℂ × ℂ)
  set S : Set (DistC × ContMetric × ContMetric) := {t | ∀ n, t.2.2.1 (s n) ≤ C t.1 * t.2.1.1 (s n)}
  have hS : MeasurableSet S := by
    simp only [S, Set.ofPred_forall]
    exact MeasurableSet.iInter fun n => measurableSet_le
      ((t17e_measurable_apply _).comp (measurable_snd.comp measurable_snd))
      ((hCm.comp measurable_fst).mul
        ((t17e_measurable_apply _).comp (measurable_fst.comp measurable_snd)))
  have hm3 : Measurable fun q : Ω × ContMetric => (h q.1, D q.1, q.2) :=
    (hm.comp measurable_fst).prodMk ((hD.comp measurable_fst).prodMk measurable_snd)
  have h1 : ∀ᵐ t ∂(P.map h ⊗ₘ (κ ×ₖ κ)), t ∈ S := by
    rw [← condCopyMeasure_map_triple hm hD]
    refine (ae_map_iff hm3.aemeasurable hS).2 ?_
    filter_upwards [hcopy] with q hq n using hq _ _
  have h2 := (Measure.ae_compProd_iff hS).1 h1
  filter_upwards [h2] with g hg
  rw [Kernel.prod_apply] at hg
  filter_upwards [hg] with p hp z w
  exact (TopologicalSpace.denseRange_denseSeq (ℂ × ℂ)).induction_on (z, w)
    (isClosed_le p.2.1.continuous (continuous_const.mul p.1.1.continuous)) hp

end LQGMetric.LM
