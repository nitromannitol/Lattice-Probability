/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7V16 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V15
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V5

/-!
# LM Theorem 1.7, Steps 1–3 for one mesh: the θ-averaged Efron–Stein integrand

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Theorem 1.7 (l. 1011–1055; D107 §3(i)–(iv)): combining
`t17v_ES_le` (Steps 1–2 per field) with a per-metric family of bounds as produced by `t17v_perD`
(D107 §3(iii)–(iv)): `∫ dθ ES(θ, d) ≤ Γ` for `ν`-a.e. `d` and every `Γ` that bounds `∑_S b_S` for
a.e. `θ ∈ [0,1]²`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric.LM

/-- **the θ-averaged Efron–Stein integrand is bounded by the per-metric product bounds** -/
theorem t17v_int_ES_le (ν : Measure ContMetric) [IsProbabilityMeasure ν]
    (hL : ∀ᵐ d ∂ν, d.IsLength) {C : ℝ} (hC : 0 ≤ C)
    (hcopy : ∀ᵐ p ∂ν.prod ν, ∀ z w : ℂ, p.2.1 (z, w) ≤ C * p.1.1 (z, w)) {ε R : ℝ}
    {F : ContMetric → ℝ} (hFm : Measurable F)
    {Φ : (ℝ × ℝ) × (t17Box ε R → ℕ → ℝ≥0∞) → ℝ} (hΦ : Measurable Φ)
    (K : Kernel ((ℝ × ℝ) × (t17Box ε R → ℕ → ℝ≥0∞)) ContMetric) [IsMarkovKernel K]
    (hslice : ∀ᵐ θ ∂t17Λ, (ν.map (t17Y ε θ (t17Box ε R))) ⊗ₘ
        (K.comap (fun y => (θ, y)) (measurable_const.prodMk measurable_id)) =
      ν.map fun d => (t17Y ε θ (t17Box ε R) d, d))
    (hΦF : ∀ᵐ θ ∂t17Λ, ∀ᵐ d ∂ν, F d = Φ (θ, t17Y ε θ (t17Box ε R) d))
    (hprod : ∀ᵐ θ ∂(volume : Measure (ℝ × ℝ)), ν.map (t17Y ε θ (t17Box ε R)) =
      Measure.pi fun k : t17Box ε R => ν.map (t17eEnc (t17Square ε θ k))) :
    ∀ᵐ d ∂ν, ∀ Γ : ℝ, (∀ᵐ θ ∂(volume : Measure (ℝ × ℝ)), θ.1 ∈ Icc (0 : ℝ) 1 →
        θ.2 ∈ Icc (0 : ℝ) 1 → ∃ b : t17Box ε R → ℝ, (∀ k, 0 ≤ b k) ∧
          (∀ (k : t17Box ε R) (d'' : ContMetric), T17Compat C ε θ (t17Box ε R) d d'' k →
            max (F d'' - F d) 0 ^ 2 ≤ b k) ∧ ∑ k, b k ≤ Γ) →
      ∫⁻ θ, t17ES ε R F Φ ν θ d ∂t17Λ ≤ ENNReal.ofReal Γ := by
  filter_upwards [t17v_ES_le ν hL hC hcopy hFm hΦ K hslice hΦF hprod] with d hd Γ hΓ
  have hθ : ∀ᵐ θ ∂t17Λ, t17ES ε R F Φ ν θ d ≤ ENNReal.ofReal Γ := by
    filter_upwards [hd, t17Λ_ae hΓ, t17Λ_mem] with θ h1 h2 h3
    obtain ⟨b, hb0, hb, hsum⟩ := h2 h3.1 h3.2
    calc t17ES ε R F Φ ν θ d ≤ ∑ k, ENNReal.ofReal (b k) := h1 b hb
      _ = ENNReal.ofReal (∑ k, b k) :=
          (ENNReal.ofReal_sum_of_nonneg fun k _ => hb0 k).symm
      _ ≤ ENNReal.ofReal Γ := ENNReal.ofReal_le_ofReal hsum
  calc ∫⁻ θ, t17ES ε R F Φ ν θ d ∂t17Λ ≤ ∫⁻ _, ENNReal.ofReal Γ ∂t17Λ := lintegral_mono_ae hθ
    _ = ENNReal.ofReal Γ := by rw [lintegral_const, measure_univ, mul_one]

end LQGMetric.LM
