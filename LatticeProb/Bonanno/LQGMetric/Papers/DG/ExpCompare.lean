/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.ExpCompare at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# From the coupling bound of DG Lemma 2.5 to the exponent inequality (DG eqn-exponent-mono)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex` l. 770–776: "By Theorem 1.5 and
Lemma 2.5, … (eqn-exponent-mono)". The step is: if `δ^{ξ̃²/2} X̃_δ ≤ C δ^{ξ²/2} X_δ` with
probability `≥ 1 − O(1/C)` uniformly in `δ`, and `X_δ = δ^{λ + o(1)}`, `X̃_δ = δ^{λ̃ + o(1)}` in
probability, then `λ + ξ²/2 ≤ λ̃ + ξ̃²/2` (DEC-A D-A1 step 5, "Sign check"). DG leave this
one-line deduction to the reader; the argument below is the evident one (choose `C` with
`O(1/C) < 1/4`, a common good `δ`, and compare logarithms).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace DG

/-- **Exponent comparison.** -/
theorem exponent_le_of_coupling_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Xt : ℝ → Ω → ℝ} (hX : ∀ δ, 0 < δ → ∀ p, 0 < X δ p)
    (hXt : ∀ δ, 0 < δ → ∀ p, 0 < Xt δ p) {ξ ξt lam lamt : ℝ}
    (h1 : TendstoInMeasure μ (fun δ p => Real.log (X δ p) / Real.log δ) (𝓝[>] 0)
      (fun _ => lam))
    (h2 : TendstoInMeasure μ (fun δ p => Real.log (Xt δ p) / Real.log δ) (𝓝[>] 0)
      (fun _ => lamt))
    (hB : ∃ K : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ C : ℝ, 0 < C →
      μ {p | C * δ ^ (ξ ^ 2 / 2) * X δ p < δ ^ (ξt ^ 2 / 2) * Xt δ p} ≤
        ENNReal.ofReal (K / C)) :
    lam + ξ ^ 2 / 2 ≤ lamt + ξt ^ 2 / 2 := by
  by_contra hlt
  push Not at hlt
  set η := (lam + ξ ^ 2 / 2 - (lamt + ξt ^ 2 / 2)) / 4 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  obtain ⟨K, hK⟩ := hB
  set C := 4 * |K| + 4 with hC
  have hC0 : 0 < C := by positivity
  set q : ℝ≥0∞ := ENNReal.ofReal (1 / 4) with hq
  have hq0 : (0 : ℝ≥0∞) < q := ENNReal.ofReal_pos.2 (by norm_num)
  have hKC : ENNReal.ofReal (K / C) < q := by
    have : K / C < 1 / 4 := by
      rw [div_lt_iff₀ hC0]; have := le_abs_self K; linarith
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 this
  rw [tendstoInMeasure_iff_dist] at h1 h2
  have e1 := (h1 η hη0).eventually (gt_mem_nhds hq0)
  have e2 := (h2 η hη0).eventually (gt_mem_nhds hq0)
  have e3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), Real.log δ < -Real.log C / (2 * η) :=
    Real.tendsto_log_nhdsGT_zero.eventually (eventually_lt_atBot _)
  have e0 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo 0 1 := Ioo_mem_nhdsGT one_pos
  obtain ⟨δ, ⟨hδ0, hδ1⟩, a1, a2, a3⟩ := (e0.and (e1.and (e2.and e3))).exists
  -- a point outside the three bad sets
  have hex : ∃ p, ¬ (η ≤ dist (Real.log (X δ p) / Real.log δ) lam) ∧
      ¬ (η ≤ dist (Real.log (Xt δ p) / Real.log δ) lamt) ∧
      ¬ (C * δ ^ (ξ ^ 2 / 2) * X δ p < δ ^ (ξt ^ 2 / 2) * Xt δ p) := by
    by_contra hno
    push Not at hno
    have hsub : (univ : Set Ω) ⊆ {p | η ≤ dist (Real.log (X δ p) / Real.log δ) lam} ∪
        {p | η ≤ dist (Real.log (Xt δ p) / Real.log δ) lamt} ∪
        {p | C * δ ^ (ξ ^ 2 / 2) * X δ p < δ ^ (ξt ^ 2 / 2) * Xt δ p} := by
      intro p _
      by_cases q1 : η ≤ dist (Real.log (X δ p) / Real.log δ) lam
      · exact Or.inl (Or.inl q1)
      by_cases q2 : η ≤ dist (Real.log (Xt δ p) / Real.log δ) lamt
      · exact Or.inl (Or.inr q2)
      · exact Or.inr (hno p (not_le.1 q1) (not_le.1 q2))
    have hm := (measure_mono (μ := μ) hsub).trans
      ((measure_union_le (μ := μ) _ _).trans (add_le_add_left (measure_union_le (μ := μ) _ _) _))
    rw [measure_univ] at hm
    have h3 := hK δ ⟨hδ0, hδ1⟩ C hC0
    have : (1 : ℝ≥0∞) < q + q + q :=
      lt_of_le_of_lt hm (ENNReal.add_lt_add (ENNReal.add_lt_add a1 a2) (h3.trans_lt hKC))
    have h34 : q + q + q ≤ 1 := by
      rw [hq, ← ENNReal.ofReal_add (by norm_num) (by norm_num),
        ← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    exact absurd (this.trans_le h34) (lt_irrefl 1)
  obtain ⟨p, q1, q2, q3⟩ := hex
  push Not at q1 q2 q3
  set L := Real.log δ
  have hL : L < 0 := Real.log_neg hδ0 hδ1
  have hx := hX δ hδ0 p
  have hxt := hXt δ hδ0 p
  set r1 := Real.log (X δ p) / L
  set r2 := Real.log (Xt δ p) / L
  have hr1 : Real.log (X δ p) = r1 * L := (div_mul_cancel₀ _ hL.ne).symm
  have hr2 : Real.log (Xt δ p) = r2 * L := (div_mul_cancel₀ _ hL.ne).symm
  rw [Real.dist_eq, abs_lt] at q1 q2
  have hlog := Real.log_le_log (by positivity) q3
  rw [Real.log_mul (by positivity) hxt.ne', Real.log_mul (by positivity) hx.ne',
    Real.log_mul hC0.ne' (by positivity), Real.log_rpow hδ0, Real.log_rpow hδ0, hr1, hr2] at hlog
  have m1 : (r1 - (lam - η)) * L < 0 := mul_neg_of_pos_of_neg (by linarith) hL
  have m2 : (lamt + η - r2) * L < 0 := mul_neg_of_pos_of_neg (by linarith) hL
  have h2η : 0 < 2 * η := by positivity
  have a3' : L * (2 * η) < -Real.log C := by
    have := (lt_div_iff₀ h2η).1 a3; linarith
  nlinarith

end DG
end LQGMetric
