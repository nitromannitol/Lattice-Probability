/-
# The factorial-Bernstein bound: mgf to moment

The factorial-moment hypothesis `∑_i E[|ξ_i|^q | F_{i-1}] ≤ (q!/2) a^{q-2} v` gives, through
`LatticeProb.condExp_exp_le_of_factorial` and the martingale product, the conditional Bernstein mgf

  `E[e^{λ S} | F_0] ≤ e^{λ²v/(2(1-aλ))}`,  `S = ∑_{i≤k} ξ_i`, `0 ≤ λ < 1/a`,

and hence the two-sided tail `P(|S| ≥ s) ≤ 2 e^{-s²/(2(v+as))}`.  This file closes that tail
from the mgf by Chernoff's bound at the optimal `λ = s/(v+as)`, and then applies
`LatticeProb.integral_rpow_le_of_tail` (`Prob/BernsteinFactorialClause.lean`) to obtain the actual
factorial-Bernstein `r`-th moment bound

  `(∫ |S|^r dμ)^{1/r} ≤ 32 (√(r v) + r a)`.

No new `Prop`; no new external input; no false Pinelis input; not imported by the root.
-/
import LatticeProb.Prob.BernsteinFactorialClause

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **One-sided Chernoff step.**  An mgf bound `mgf S μ λ ≤ e^{λ²v/(2(1-aλ))}` at the optimal
`λ = s/(v+as)` gives the one-sided Bernstein tail `P(S ≥ s) ≤ e^{-s²/(2(v+as))}`. -/
theorem mgf_tail_le [IsProbabilityMeasure μ] {S : Ω → ℝ} {a v s : ℝ}
    (ha : 0 < a) (hv : 0 < v) (hs : 0 < s)
    (hmgf : mgf S μ (s / (v + a * s))
      ≤ Real.exp ((s / (v + a * s)) ^ 2 * v / (2 * (1 - a * (s / (v + a * s))))))
    (hexpint : Integrable (fun ω => Real.exp ((s / (v + a * s)) * S ω)) μ) :
    (μ {ω | s ≤ S ω}).toReal ≤ Real.exp (-(s ^ 2 / (2 * (v + a * s)))) := by
  have hden : 0 < v + a * s := by positivity
  have hlam_pos : 0 < s / (v + a * s) := div_pos hs hden
  have hlam_a : (s / (v + a * s)) * a < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hden]
    nlinarith
  have hch := measure_ge_le_exp_mul_mgf (μ := μ) (X := S) (t := s / (v + a * s)) s hlam_pos.le
    hexpint
  have hexp : Real.exp (-(s / (v + a * s)) * s)
        * Real.exp ((s / (v + a * s)) ^ 2 * v / (2 * (1 - a * (s / (v + a * s)))))
      = Real.exp (-(s ^ 2 / (2 * (v + a * s)))) := by
    rw [← Real.exp_add]
    congr 1
    have h1m : (1 : ℝ) - a * (s / (v + a * s)) ≠ 0 := by
      have : 1 - a * (s / (v + a * s)) = v / (v + a * s) := by field_simp; ring
      rw [this]; exact div_ne_zero hv.ne' (by positivity)
    field_simp [h1m]
    rw [show v + s * a - s * a = v by ring, div_self hv.ne']
    ring
  calc (μ {ω | s ≤ S ω}).toReal
      ≤ Real.exp (-(s / (v + a * s)) * s) * mgf S μ (s / (v + a * s)) := hch
    _ ≤ Real.exp (-(s / (v + a * s)) * s)
          * Real.exp ((s / (v + a * s)) ^ 2 * v / (2 * (1 - a * (s / (v + a * s))))) := by
        gcongr
    _ = Real.exp (-(s ^ 2 / (2 * (v + a * s)))) := hexp

/-- **Two-sided Bernstein tail from the mgf.**  Applying the one-sided step to `S` and `-S`,
`P(|S| ≥ s) ≤ 2 e^{-s²/(2(v+as))}`. -/
theorem mgf_abs_tail_le [IsProbabilityMeasure μ] {S : Ω → ℝ} {a v s : ℝ}
    (ha : 0 < a) (hv : 0 < v) (hs : 0 < s)
    (hmgf : mgf S μ (s / (v + a * s))
      ≤ Real.exp ((s / (v + a * s)) ^ 2 * v / (2 * (1 - a * (s / (v + a * s))))))
    (hmgf' : mgf (fun ω => -S ω) μ (s / (v + a * s))
      ≤ Real.exp ((s / (v + a * s)) ^ 2 * v / (2 * (1 - a * (s / (v + a * s))))))
    (hexpint : Integrable (fun ω => Real.exp ((s / (v + a * s)) * S ω)) μ)
    (hexpint' : Integrable (fun ω => Real.exp ((s / (v + a * s)) * (-S ω))) μ) :
    (μ {ω | s ≤ |S ω|}).toReal ≤ 2 * Real.exp (-(s ^ 2 / (2 * (v + a * s)))) := by
  have hpos := mgf_tail_le (S := S) ha hv hs hmgf hexpint
  have hneg := mgf_tail_le (S := fun ω => -S ω) ha hv hs hmgf' hexpint'
  have hsub : {ω | s ≤ |S ω|} ⊆ {ω | s ≤ S ω} ∪ {ω | s ≤ -S ω} := by
    intro ω hω
    change s ≤ |S ω| at hω
    by_cases h : 0 ≤ S ω
    · left; rw [abs_of_nonneg h] at hω; exact hω
    · right; rw [abs_of_neg (not_le.mp h)] at hω; exact hω
  have h1 : μ {ω | s ≤ |S ω|} ≤ μ ({ω | s ≤ S ω} ∪ {ω | s ≤ -S ω}) :=
    measure_mono hsub
  have h2 : μ ({ω | s ≤ S ω} ∪ {ω | s ≤ -S ω})
      ≤ μ {ω | s ≤ S ω} + μ {ω | s ≤ -S ω} := measure_union_le _ _
  have h3 : (μ {ω | s ≤ |S ω|}).toReal
      ≤ (μ {ω | s ≤ S ω}).toReal + (μ {ω | s ≤ -S ω}).toReal :=
    calc (μ {ω | s ≤ |S ω|}).toReal
        ≤ (μ ({ω | s ≤ S ω} ∪ {ω | s ≤ -S ω})).toReal :=
          ENNReal.toReal_mono (measure_ne_top μ _) h1
      _ ≤ (μ {ω | s ≤ S ω} + μ {ω | s ≤ -S ω}).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
            ⟨measure_ne_top μ _, measure_ne_top μ _⟩) h2
      _ ≤ (μ {ω | s ≤ S ω}).toReal + (μ {ω | s ≤ -S ω}).toReal := ENNReal.toReal_add_le
  linarith

/-- **The factorial-Bernstein `r`-th moment bound from the mgf.**  Given the (symmetric) mgf bound
`E[e^{λ S}] ≤ e^{λ²v/(2(1-aλ))}` and finite `L^r` integrability, the tail-to-moment step gives

  `(∫ |S|^r dμ)^{1/r} ≤ 32 (√(r v) + r a)`. -/
theorem moment_le_of_mgf [IsProbabilityMeasure μ] {S : Ω → ℝ} {r a v : ℝ}
    (hr : 2 ≤ r) (ha : 0 < a) (hv : 0 < v)
    (hSint : Integrable (fun ω => |S ω| ^ r) μ)
    (hmgf : ∀ lam : ℝ, 0 ≤ lam → lam * a < 1 →
      mgf S μ lam ≤ Real.exp (lam ^ 2 * v / (2 * (1 - a * lam))))
    (hmgf' : ∀ lam : ℝ, 0 ≤ lam → lam * a < 1 →
      mgf (fun ω => -S ω) μ lam ≤ Real.exp (lam ^ 2 * v / (2 * (1 - a * lam))))
    (hexpint : ∀ lam : ℝ, 0 < lam → lam * a < 1 →
      Integrable (fun ω => Real.exp (lam * S ω)) μ)
    (hexpint' : ∀ lam : ℝ, 0 < lam → lam * a < 1 →
      Integrable (fun ω => Real.exp (lam * (-S ω))) μ)
    (hint : Integrable (fun t : ℝ => r * t ^ (r - 1)
      * (μ {ω | t ≤ |S ω|}).toReal) (volume.restrict (Set.Ioi 0)))
    (htailint : Integrable (fun t : ℝ => r * t ^ (r - 1)
      * (2 * Real.exp (-(t ^ 2 / (2 * (v + a * t)))))) (volume.restrict (Set.Ioi 0))) :
    (∫ ω, |S ω| ^ r ∂μ) ^ (1 / r) ≤ 32 * (Real.sqrt (r * v) + r * a) := by
  refine integral_rpow_le_of_tail hr ha hv (Filter.Eventually.of_forall fun ω => abs_nonneg _)
    hSint ?_ hint htailint
  intro s hs
  have hden : 0 < v + a * s := by positivity
  have hlam_pos : 0 < s / (v + a * s) := div_pos hs hden
  have hlam_a : (s / (v + a * s)) * a < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hden]
    nlinarith
  exact mgf_abs_tail_le ha hv hs
    (hmgf (s / (v + a * s)) hlam_pos.le hlam_a)
    (hmgf' (s / (v + a * s)) hlam_pos.le hlam_a)
    (hexpint (s / (v + a * s)) hlam_pos hlam_a)
    (hexpint' (s / (v + a * s)) hlam_pos hlam_a)

end LatticeProb
