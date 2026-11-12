/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L13Limit at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Monoid
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# DDDF Lemma 13: positive association passes to pointwise limits (task P2-DDDFL913)

DDDF = arXiv:1904.08021, `tightness.tex` l. 771–780 (Lemma 13 = `Lem:FKG`): positive association
of `{L^{(n)}(R_i) > x_i}` "comes essentially from [Pitt82] together with an approximation
argument", i.e. DF (arXiv:1809.02607) §2.3, DF:226–252: the piecewise-constant approximations
`L^{(n)}(R, k) → L^{(n)}(R)` a.s., then a limit in the product inequality. DF passes to the limit
with the Portmanteau theorem and a positive density of the lengths; following DEV D-DDDF-7
(blueprint/DDDF.md, row L13) we use instead an own atom-free argument:
for `a < a + δ < a + 2δ`, on the event where `|Z_m − Z| < δ` (whose complement has small
probability for `m` large),
`P(⋂{Z_i > a_i}) ≥ P(⋂{Z_{m,i} > a_i + δ}) − e_m ≥ ∏ P(Z_{m,i} > a_i + δ) − e_m
≥ ∏ (P(Z_i > a_i + 2δ) − e_m)⁺ − e_m`, then `m → ∞` and `δ ↓ 0` (continuity from below).

`assoc_of_tendsto`: if `∏ P(Z_{k,i} > a_i) ≤ P(⋂ {Z_{k,i} > a_i})` for all `k`, `a` and
`Z_{k,i} → Z_i` pointwise, then the same holds for `Z`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace LQGMetric
namespace DDDF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : Type*} [Fintype κ]

/-- Step A of the limit: the inequality with thresholds shifted by `2δ` on the left. -/
theorem assoc_of_tendsto_shift {Z : ℕ → κ → Ω → ℝ} {Zl : κ → Ω → ℝ}
    (hZm : ∀ k i, Measurable (Z k i)) (hZlm : ∀ i, Measurable (Zl i))
    (hlim : ∀ i ω, Tendsto (fun k => Z k i ω) atTop (𝓝 (Zl i ω)))
    (hass : ∀ k (a : κ → ℝ), ∏ i, P.real {ω | a i < Z k i ω} ≤ P.real (⋂ i, {ω | a i < Z k i ω}))
    (a : κ → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∏ i, P.real {ω | a i + 2 * δ < Zl i ω} ≤ P.real (⋂ i, {ω | a i < Zl i ω}) := by
  set E : ℕ → Set Ω := fun m => ⋃ k, ⋃ (_ : m ≤ k), ⋃ i, {ω | δ ≤ |Z k i ω - Zl i ω|} with hEdef
  have hEm : ∀ m, MeasurableSet (E m) := fun m =>
    MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun i =>
      measurableSet_le measurable_const (continuous_abs.measurable.comp ((hZm k i).sub (hZlm i)))
  have hEanti : Antitone E := fun m m' hmm ω hω => by
    simp only [hEdef, mem_iUnion] at hω ⊢
    obtain ⟨k, hk, i, hi⟩ := hω
    exact ⟨k, hmm.trans hk, i, hi⟩
  have hEinter : ⋂ m, E m = ∅ := by
    ext ω
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    have hev : ∀ᶠ k in atTop, ∀ i, |Z k i ω - Zl i ω| < δ := by
      rw [eventually_all]
      intro i
      have := (hlim i ω).sub_const (Zl i ω)
      rw [sub_self] at this
      have h2 := (this.abs).eventually (gt_mem_nhds (by simpa using hδ))
      simpa using h2
    obtain ⟨m, hm⟩ := eventually_atTop.1 hev
    refine ⟨m, ?_⟩
    simp only [hEdef, mem_iUnion, not_exists]
    intro k hk i hi
    exact absurd (hm k hk i) (not_lt.2 hi)
  have he : Tendsto (fun m => P.real (E m)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := P) (fun m => (hEm m).nullMeasurableSet) hEanti
      ⟨0, measure_ne_top _ _⟩
    rw [hEinter, measure_empty] at h
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    simpa [Function.comp_def, measureReal_def] using this
  set p : κ → ℝ := fun i => P.real {ω | a i + 2 * δ < Zl i ω}
  have hbound : ∀ m, (∏ i, max (p i - P.real (E m)) 0) - P.real (E m) ≤
      P.real (⋂ i, {ω | a i < Zl i ω}) := fun m => by
    have h1 : P.real (⋂ i, {ω | a i + δ < Z m i ω}) ≤
        P.real (⋂ i, {ω | a i < Zl i ω}) + P.real (E m) := by
      refine (measureReal_mono ?_).trans (measureReal_union_le _ _)
      intro ω hω
      by_cases hωE : ω ∈ E m
      · exact Or.inr hωE
      · left
        simp only [mem_iInter, mem_ofPred_eq] at hω ⊢
        intro i
        have : |Z m i ω - Zl i ω| < δ := by
          by_contra hc
          exact hωE (mem_iUnion.2 ⟨m, mem_iUnion.2 ⟨le_rfl, mem_iUnion.2 ⟨i, not_lt.1 hc⟩⟩⟩)
        have := (abs_lt.1 this).2
        linarith [hω i]
    have h2 : ∀ i, max (p i - P.real (E m)) 0 ≤ P.real {ω | a i + δ < Z m i ω} := fun i => by
      refine max_le ?_ measureReal_nonneg
      rw [sub_le_iff_le_add]
      refine (measureReal_mono ?_).trans (measureReal_union_le _ _)
      intro ω hω
      by_cases hωE : ω ∈ E m
      · exact Or.inr hωE
      · left
        simp only [mem_ofPred_eq] at hω ⊢
        have : |Z m i ω - Zl i ω| < δ := by
          by_contra hc
          exact hωE (mem_iUnion.2 ⟨m, mem_iUnion.2 ⟨le_rfl, mem_iUnion.2 ⟨i, not_lt.1 hc⟩⟩⟩)
        have := (abs_lt.1 this).1
        linarith
    have h3 : ∏ i, max (p i - P.real (E m)) 0 ≤ ∏ i, P.real {ω | a i + δ < Z m i ω} :=
      Finset.prod_le_prod₀ (fun i _ => le_max_right _ _) fun i _ => h2 i
    have h4 := hass m (fun i => a i + δ)
    linarith
  have hlimit : Tendsto (fun m => (∏ i, max (p i - P.real (E m)) 0) - P.real (E m)) atTop
      (𝓝 ((∏ i, max (p i - 0) 0) - 0)) :=
    (tendsto_finsetProd _ fun i _ => (tendsto_const_nhds.sub he).max tendsto_const_nhds).sub he
  have hp : (∏ i, max (p i - 0) 0) - 0 = ∏ i, p i := by
    simp only [sub_zero]
    exact Finset.prod_congr rfl fun i _ => max_eq_left measureReal_nonneg
  rw [hp] at hlimit
  exact le_of_tendsto' hlimit hbound

/-- **Positive association passes to pointwise limits** (DEV D-DDDF-7; DF §2.3 approximation). -/
theorem assoc_of_tendsto {Z : ℕ → κ → Ω → ℝ} {Zl : κ → Ω → ℝ}
    (hZm : ∀ k i, Measurable (Z k i)) (hZlm : ∀ i, Measurable (Zl i))
    (hlim : ∀ i ω, Tendsto (fun k => Z k i ω) atTop (𝓝 (Zl i ω)))
    (hass : ∀ k (a : κ → ℝ), ∏ i, P.real {ω | a i < Z k i ω} ≤ P.real (⋂ i, {ω | a i < Z k i ω}))
    (a : κ → ℝ) :
    ∏ i, P.real {ω | a i < Zl i ω} ≤ P.real (⋂ i, {ω | a i < Zl i ω}) := by
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδ : ∀ n, 0 < δ n := fun n => by positivity
  have htend : ∀ i, Tendsto (fun n => P.real {ω | a i + 2 * δ n < Zl i ω}) atTop
      (𝓝 (P.real {ω | a i < Zl i ω})) := fun i => by
    have hmono : Monotone fun n => {ω | a i + 2 * δ n < Zl i ω} := fun n n' hnn ω hω => by
      simp only [mem_ofPred_eq] at hω ⊢
      have : δ n' ≤ δ n := by
        simp only [δ]
        exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnn 1)
      linarith
    have hU : (⋃ n, {ω | a i + 2 * δ n < Zl i ω}) = {ω | a i < Zl i ω} := by
      ext ω
      simp only [mem_iUnion, mem_ofPred_eq]
      constructor
      · rintro ⟨n, hn⟩; linarith [hδ n]
      · intro h
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < (Zl i ω - a i) / 2 by linarith)
        refine ⟨n, ?_⟩
        simp only [δ]
        linarith
    have h := tendsto_measure_iUnion_atTop (μ := P) hmono
    rw [hU] at h
    have := (ENNReal.tendsto_toReal (measure_ne_top P _)).comp h
    simpa [Function.comp_def, measureReal_def] using this
  have hprod := tendsto_finsetProd (Finset.univ : Finset κ) fun i _ => htend i
  exact le_of_tendsto' hprod fun n =>
    assoc_of_tendsto_shift hZm hZlm hlim hass a (hδ n)

end DDDF
end LQGMetric
