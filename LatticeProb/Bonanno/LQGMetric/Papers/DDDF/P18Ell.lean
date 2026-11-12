/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P18Ell at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Straight
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiField

/-!
# DDDF Proposition 18, Step 4: the a priori lower bound on `ℓ_n(φ, p)` (task P2-DDDF16)

DDDF (arXiv:1904.08021, `tightness.tex` l. 930, proof of Prop 18, Step 4): "By a direct
comparison with the supremum, we have `ℓ_n(φ,p) ≥ 2^{-ξ(2n + C√n)}`."
Proof (DDDF's one line, written out): by Prop 2 (2.10) (`prop2_tail`, DF Lemma 10.1) with
`a = log 4 + β/√n`, `P(max_{[0,1]²}|φ_{0,n}| ≥ n log 4 + C√n) ≤ C₂ e^{-2β√n} < p` for `β` large;
off this event `L^{(n)}_{1,1}(φ) ≥ e^{-ξ max|φ_{0,n}|}` (DDDF.S2.c, `exp_neg_le_lenObs`), hence
the quantile bound. (`2^{-ξ(2n + C√n)} = e^{-ξ(n log 4 + C' √n)}`.) Stated for `n ≥ 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : ℝ}

/-- **DDDF Prop 18, Step 4, a priori bound**: for `p ∈ (0,1)` there is `C` with
`ℓ_n(φ, p) ≥ e^{-ξ(n log 4 + C√n)}` for all `n ≥ 1`. -/
theorem dddf_p18_ell_lower {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (hξ : 0 < ξ)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Real.exp (-(ξ * (n * Real.log 4 + C * √n))) ≤
        ellQ ξ P (phiMN W P 0 n) (rectAB 1 1) (ENNReal.ofReal p) := by
  have := hW.isProbabilityMeasure
  obtain ⟨C₂, hC₂, h2⟩ := prop2_tail
  set β : ℝ := max 0 (Real.log (C₂ / p) / 2) + 1
  have hβ : 0 < β := by positivity
  have hβp : C₂ * Real.exp (-(2 * β)) < p := by
    have h1 : Real.log (C₂ / p) < 2 * β := by
      have := le_max_right 0 (Real.log (C₂ / p) / 2); simp only [β]; linarith
    have h2' : Real.exp (-(2 * β)) < Real.exp (-Real.log (C₂ / p)) := Real.exp_lt_exp.2 (by linarith)
    have e : Real.exp (-Real.log (C₂ / p)) = p / C₂ := by
      rw [Real.exp_neg, Real.exp_log (div_pos hC₂ hp0), inv_div]
    rw [e] at h2'
    calc C₂ * Real.exp (-(2 * β)) < C₂ * (p / C₂) := mul_lt_mul_of_pos_left h2' hC₂
      _ = p := by field_simp
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨C₂ * Real.log 4 + β + β * C₂, by positivity, fun n hn => ?_⟩
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.2 hn'
  have hsn2 : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
  set t : ℝ := √(n : ℝ) with ht_def
  have ht0 : 0 < t := by linarith
  set α : ℝ := Real.log 4 + β / t
  have hα : 0 < α := by positivity
  set M : ℝ := α * (n + C₂ * √n)
  -- the bad event
  set B := {ω | M ≤ ⨆ z : SupTail.ferniqueBox 0 1, |phiMN W P 0 n z ω|}
  have hB := h2 hW n (phiMN W P 0 n) (fun x => by simpa [inv_pow] using hφ.ae_eq x) hφ.cont α hα
  have hBp : P.real B < p := by
    refine lt_of_le_of_lt hB (lt_of_le_of_lt ?_ hβp)
    have e4 : (4 : ℝ) ^ n = Real.exp (n * Real.log 4) := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4), ← Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [e4, mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₂.le
    have hαsq : α ^ 2 * n / Real.log 4 = n * Real.log 4 + 2 * β * t + β ^ 2 / Real.log 4 := by
      rw [← hsn2]
      simp only [α]
      field_simp
      ring
    rw [neg_mul, neg_div, hαsq]
    have : 2 * β ≤ 2 * β * t := le_mul_of_one_le_right (by positivity) hsn
    have : 0 ≤ β ^ 2 / Real.log 4 := by positivity
    linarith
  -- off `B`, the crossing length is at least `e^{-ξ M}`
  have hM : M ≤ n * Real.log 4 + (C₂ * Real.log 4 + β + β * C₂) * t := by
    simp only [M, α]
    have e : (Real.log 4 + β / t) * (n + C₂ * t) =
        n * Real.log 4 + C₂ * Real.log 4 * t + β * t + β * C₂ := by
      rw [← hsn2]; field_simp; ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hsn (by positivity : (0 : ℝ) ≤ β * C₂)]
  have hlow : ∀ ω, ω ∉ B → Real.exp (-(ξ * M)) ≤ lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω := by
    intro ω hω
    have hω' : (⨆ z : SupTail.ferniqueBox 0 1, |phiMN W P 0 n z ω|) < M := not_le.1 hω
    have hb : ∀ x ∈ (rectAB 1 1).toSet, |phiMN W P 0 n x ω| ≤ M := by
      intro x hx
      rw [rectAB_one_toSet] at hx
      exact (le_ciSup (SupTail.bddAbove_abs_of_compact
        (by rw [← rectAB_one_toSet]; exact MarkedRect.isCompact_toSet _) (hφ.cont ω))
        (⟨x, hx⟩ : SupTail.ferniqueBox 0 1)).trans hω'.le
    have h := exp_neg_le_lenObs (ξ := ξ) hφ.cont (rectAB 1 1) (by norm_num [rectAB])
      (by norm_num [rectAB]) hb
    simpa [abs_of_pos hξ, rectAB, MarkedRect.crossWidth] using h
  -- the quantile
  have hfin : Real.exp (-(ξ * (n * Real.log 4 + (C₂ * Real.log 4 + β + β * C₂) * t))) ≤
      Real.exp (-(ξ * M)) :=
    Real.exp_le_exp.2 (by have := mul_le_mul_of_nonneg_left hM hξ.le; linarith)
  refine hfin.trans ?_
  by_contra hcon
  push Not at hcon
  have hq := prob_le_ellQ (ξ := ξ) (P := P) hφ.cont hφ.meas (rectAB 1 1)
    (ENNReal.ofReal_pos.2 hp0) (by rw [ENNReal.ofReal_lt_one]; exact hp1)
  have hsub : {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω ≤
      ellQ ξ P (phiMN W P 0 n) (rectAB 1 1) (ENNReal.ofReal p)} ⊆ B := by
    intro ω hω
    by_contra hωB
    have := hlow ω hωB
    exact absurd (lt_of_le_of_lt hω hcon) (not_lt.2 this)
  have h3 := hq.trans (measure_mono hsub)
  rw [← ofReal_measureReal (measure_ne_top P B), ENNReal.ofReal_le_ofReal_iff measureReal_nonneg]
    at h3
  linarith

end DDDF
end LQGMetric
