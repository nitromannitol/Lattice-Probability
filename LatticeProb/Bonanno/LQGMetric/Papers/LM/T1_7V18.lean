/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7V18 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V17
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7E5

/-!
# LM Theorem 1.7, limit `ε → 0`: integrability (LM Lemma 5.1) and the square count

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), Lemma 5.1 (`lem-cond-bded`, l. 904–929) under one measure `ν = κ_g`
(`t17e_condBded_measure`): `F_m = D(z,w;B_m)` is `ν`-a.s. bounded (D107 §3(v): "the dominating
function is σ(h)-measurable by L5.1").

* `t17v_F_bdd`: `∃ B, ∀ᵐ d ∂ν, t17F m z w d ≤ ofReal B` with `t17F m z w d ≠ ⊤`; hence
  `t17v_memLp_F` (`MemLp F 2 ν`, the hypothesis of `t17v_es_avg`).
* `t17v_card_box`: `#(t17Box ε R) = (2⌈R/ε⌉ + 3)²` (so `ε³ #𝒮 ≤ ε (2R + 5ε)² → 0` for `R ≥ 0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric.LM

/-- **LM Lemma 5.1 for `F_m` under `ν`**: `F_m` is `ν`-a.s. bounded -/
theorem t17v_F_bdd (ν : Measure ContMetric) [IsProbabilityMeasure ν]
    (hL : ∀ᵐ d ∂ν, d.IsLength) {C : ℝ} (hC : 0 < C)
    (hcopy : ∀ᵐ p ∂ν.prod ν, ∀ z w : ℂ, p.2.1 (z, w) ≤ C * p.1.1 (z, w))
    {m : ℕ} {z w : ℂ} (hz : ‖z‖ < m) (hw : ‖w‖ < m) :
    ∃ B : ℝ, ∀ᵐ d ∂ν, t17F m z w d ≤ ENNReal.ofReal B ∧ t17F m z w d ≠ ⊤ := by
  set f := t17F m z w
  have hf : Measurable f := measurable_t17F m z w
  have hle : ∀ᵐ p ∂ν.prod ν, f p.2 ≤ ENNReal.ofReal C * f p.1 := by
    have hl := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := ν)).ae hL
    filter_upwards [hcopy, hl] with p hp hpl
    exact t17_chainInf_le hpl hC hp Metric.isOpen_ball z w
  have hb := t17e_condBded_measure hf (ENNReal.ofReal C) hle
  have hfin : ∀ᵐ d ∂ν, f d ≠ ⊤ := by
    filter_upwards [hL] with d hd
    rw [show f d = d.internal (Metric.ball 0 (m : ℝ)) z w from
      (d.internal_eq_chainInf hd Metric.isOpen_ball z w).symm]
    exact DFGPS.T12.internal_ne_top d hd Metric.isOpen_ball (convex_ball _ _).isPreconnected
      (mem_ball_zero_iff.2 hz) (mem_ball_zero_iff.2 hw)
  obtain ⟨y₀, hy₀b, hy₀f⟩ := (hb.and hfin).exists
  have hI : ∫⁻ y, f y ∂ν ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hy₀f) hy₀b.1
  refine ⟨(ENNReal.ofReal C * ∫⁻ y, f y ∂ν).toReal, ?_⟩
  filter_upwards [hb, hfin] with d hd hdf
  refine ⟨?_, hdf⟩
  rw [ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI)]
  exact hd.2

/-- `F_m ∈ L²(ν)` -/
theorem t17v_memLp_F (ν : Measure ContMetric) [IsProbabilityMeasure ν]
    (hL : ∀ᵐ d ∂ν, d.IsLength) {C : ℝ} (hC : 0 < C)
    (hcopy : ∀ᵐ p ∂ν.prod ν, ∀ z w : ℂ, p.2.1 (z, w) ≤ C * p.1.1 (z, w))
    {m : ℕ} {z w : ℂ} (hz : ‖z‖ < m) (hw : ‖w‖ < m) :
    MemLp (fun d => (t17F m z w d).toReal) 2 ν := by
  obtain ⟨B, hB⟩ := t17v_F_bdd ν hL hC hcopy hz hw
  refine MemLp.of_bound (measurable_t17F m z w).ennreal_toReal.aestronglyMeasurable
    (ENNReal.ofReal B).toReal ?_
  filter_upwards [hB] with d hd
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hd.1

/-- the number of squares -/
theorem t17v_card_box (ε R : ℝ) :
    ((t17Box ε R).card : ℝ) = ((2 * ⌈R / ε⌉ + 3).toNat : ℝ) ^ 2 := by
  unfold t17Box
  rw [Finset.card_product, Int.card_Icc]
  push_cast
  ring_nf

end LQGMetric.LM
