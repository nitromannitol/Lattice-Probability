/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.C17 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P16

/-!
# DDDF Corollary 17: lower tail of `L^{(n)}_{1,3}(φ)` (task P2-DDDF16)

DDDF (arXiv:1904.08021, `tightness.tex` l. 872–877, (4.48) = `eq:LowerTailsPhi`): "Using the
comparison result between `φ` and `ψ` (Proposition 5), we get": for `p` small enough but fixed,
`P(L^{(n)}_{1,3}(φ) ≤ e^{-s} ℓ_n(φ,p)) ≤ C e^{-cs²}`.

DDDF give no further proof. Written out (own routine argument from Prop 5 and Prop 16):
* (2.27) (`ellQ_phi_le_of_tail` with the Prop 5 tail at level `p`):
  `ℓ_n(φ, p) ≤ e^{ξM_p} ℓ_n(ψ, 2p)`;
* on `{X_{1,3} < s/(2ξ)}`: `L_{1,3}(ψ) ≤ e^{s/2} L_{1,3}(φ)` (`lenObs_le_of_XAB_le`), so
  `{L_{1,3}(φ) ≤ e^{-s}ℓ_n(φ,p)} ⊆ {X_{1,3} ≥ s/(2ξ)} ∪ {L_{1,3}(ψ) ≤ e^{-(s/2 − ξM_p)} ℓ_n(ψ,2p)}`;
* Prop 5 for the first event and Prop 16 for the second.
The field `ψ` is an auxiliary object: we use the parameters `psiQ₀` (`r₀ = 1/12`, `ε₀ = 1`),
for which DDDF's "`r₀` small enough" holds (`psiSmall_psiQ₀`: `σ_t ≤ 1/4` on `(0,1]`).
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

/-- auxiliary parameters for `ψ`: `r₀ = 1/12`, `ε₀ = 1` -/
def psiQ₀ : PsiParams where
  cut := Classical.choice exists_psiCutoff
  r₀ := 1 / 12
  ε₀ := 1
  r₀_pos := by norm_num
  ε₀_pos := by norm_num

/-- `σ_t = (1/12) √t (1 + |log t|) ≤ 1/4` on `(0, 1]` (`|log t| ≤ 2/√t`) -/
theorem psiSmall_psiQ₀ : PsiSmall psiQ₀ := by
  intro t ht0 ht1
  simp only [PsiParams.sigma, psiQ₀, Real.rpow_one]
  have hs0 : 0 < √t := Real.sqrt_pos.2 ht0
  have hs1 : √t ≤ 1 := Real.sqrt_le_one.2 ht1
  have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht1
  have h1 : Real.log (√t)⁻¹ ≤ (√t)⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.2 hs0)
  rw [Real.log_inv, Real.log_sqrt ht0.le] at h1
  have h2 : √t * (√t)⁻¹ = 1 := mul_inv_cancel₀ hs0.ne'
  rw [abs_of_nonpos hlog]
  nlinarith

/-- **DDDF Corollary 17** (`tightness.tex` l. 872–877, (4.48)): there is `p₀ > 0` such that for
every `p ∈ (0, p₀]` there are `C, c > 0` with
`P(L^{(n)}_{1,3}(φ) ≤ e^{-s} ℓ_n(φ, p)) ≤ C e^{-cs²}` for all `s > 0` and `n ≥ 0`
(`ℓ_n(φ, p) = ℓ^{(n)}_{1,1}(φ, p)`). -/
theorem dddf_cor17 {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (hξ : 0 < ξ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ) (s : ℝ), 0 < s →
      P {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 3) ω ≤
          Real.exp (-s) * ellQ ξ P (phiMN W P 0 n) (rectAB 1 1) (ENNReal.ofReal p)} ≤
        ENNReal.ofReal (C * Real.exp (-c * s ^ 2)) := by
  have := hW.isProbabilityMeasure
  set Q := psiQ₀
  obtain ⟨p₁, C₁, c₁, hp₁, hC₁, hc₁, h16⟩ := dddf_prop16 hW hξ Q psiSmall_psiQ₀
  obtain ⟨C', c', hC', hc', htail⟩ := exists_tail_XAB_unif hW Q 3
  obtain ⟨C₅, c₅, hC₅, hc₅, h5⟩ := dddf_prop5_XAB hW Q 1 3
  refine ⟨min (p₁ / 2) (1 / 4), lt_min (by positivity) (by norm_num), fun p hp hpp => ?_⟩
  have hp2 : 2 * p ≤ p₁ := by linarith [min_le_left (p₁ / 2) (1 / 4)]
  have hp4 : p ≤ 1 / 4 := hpp.trans (min_le_right _ _)
  set M : ℝ := √(max 1 (Real.log (C' / p)) / c')
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  set c : ℝ := min (c₅ / (4 * ξ ^ 2)) (c₁ / 16)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  set C : ℝ := (C₅ + C₁ + 1) * Real.exp (c * (4 * ξ * M) ^ 2)
  refine ⟨C, c, by positivity, hc, fun n s hs => ?_⟩
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  have hCe : Real.exp (c * (4 * ξ * M) ^ 2) * Real.exp (-c * s ^ 2) ≤
      C * Real.exp (-c * s ^ 2) := by
    have h1 : (1 : ℝ) ≤ C₅ + C₁ + 1 := by linarith
    have h2 := Real.exp_pos (c * (4 * ξ * M) ^ 2)
    have h3 := Real.exp_pos (-c * s ^ 2)
    calc Real.exp (c * (4 * ξ * M) ^ 2) * Real.exp (-c * s ^ 2)
        = 1 * (Real.exp (c * (4 * ξ * M) ^ 2) * Real.exp (-c * s ^ 2)) := (one_mul _).symm
      _ ≤ (C₅ + C₁ + 1) * (Real.exp (c * (4 * ξ * M) ^ 2) * Real.exp (-c * s ^ 2)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = C * Real.exp (-c * s ^ 2) := by simp only [C]; ring
  by_cases hsM : s < 4 * ξ * M
  · refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal (le_trans ?_ hCe)
    rw [← Real.exp_add]
    refine Real.one_le_exp ?_
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.le hsM.le 2) hc.le]
  push Not at hsM
  -- (2.27): `ℓ_n(φ, p) ≤ e^{ξM} ℓ_n(ψ, 2p)`
  have hcmp := ellQ_phi_le_of_tail (ξ := ξ) hW Q zero_le_one zero_le_one hM
    (htail 1 1 (by norm_num) (by norm_num) p hp) (p := ENNReal.ofReal p)
    (ENNReal.ofReal_pos.2 hp)
    (by rw [← ENNReal.ofReal_add hp.le hp.le, ENNReal.ofReal_lt_one]; linarith) n
  rw [← ENNReal.ofReal_add hp.le hp.le, show p + p = 2 * p by ring, abs_of_pos hξ] at hcmp
  set x : ℝ := s / (2 * ξ)
  have hx : 0 < x := by positivity
  set s' : ℝ := s / 2 - ξ * M
  have hs' : s / 4 ≤ s' := by simp only [s']; linarith
  set E₁ := {ω | ENNReal.ofReal x ≤
    XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) 1 3}
  set E₂ := {ω | lenObs ξ (psiMN Q W P 0 n) (rectAB 1 3) ω ≤
    Real.exp (-s') * ellQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal (2 * p))}
  have hsub : {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 3) ω ≤
      Real.exp (-s) * ellQ ξ P (phiMN W P 0 n) (rectAB 1 1) (ENNReal.ofReal p)} ⊆ E₁ ∪ E₂ := by
    intro ω hω
    by_cases h1 : ω ∈ E₁
    · exact Or.inl h1
    right
    have hX : XAB (fun n y => psiMN Q W P 0 n y ω) (fun n y => phiMN W P 0 n y ω) 1 3 ≤
        ENNReal.ofReal x := by
      rw [XAB_comm]; exact (not_le.1 h1).le
    have hL := lenObs_le_of_XAB_le (ξ := ξ) (φ := fun n => psiMN Q W P 0 n)
      (ψ := fun n => phiMN W P 0 n)
      (fun k _ => (isPhiVersion_phiMN hW (Nat.zero_le k)).cont _) zero_le_one
      (by norm_num) hx.le hX n
    rw [abs_of_pos hξ] at hL
    have hω' : lenObs ξ (phiMN W P 0 n) (rectAB 1 3) ω ≤ Real.exp (-s) * (Real.exp (ξ * M) *
        ellQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal (2 * p))) :=
      hω.trans (mul_le_mul_of_nonneg_left hcmp (Real.exp_pos _).le)
    show lenObs ξ (psiMN Q W P 0 n) (rectAB 1 3) ω ≤
      Real.exp (-s') * ellQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal (2 * p))
    calc _ ≤ _ := hL
      _ ≤ Real.exp (ξ * x) * (Real.exp (-s) * (Real.exp (ξ * M) *
          ellQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal (2 * p)))) :=
          mul_le_mul_of_nonneg_left hω' (Real.exp_pos _).le
      _ = Real.exp (ξ * x + -s + ξ * M) *
          ellQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal (2 * p)) := by
          rw [Real.exp_add, Real.exp_add]; ring
      _ = _ := by
          congr 2
          simp only [x, s']; field_simp; ring
  have hP1 := h5 x hx
  have hP2 := h16 n (2 * p) s' (by positivity) hp2 (by linarith)
  have hb1 : C₅ * Real.exp (-(c₅ * x ^ 2)) ≤ C₅ * Real.exp (-c * s ^ 2) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₅.le
    have hx2 : x ^ 2 = s ^ 2 / (4 * ξ ^ 2) := by simp only [x]; rw [div_pow, mul_pow]; norm_num
    have hcc : c ≤ c₅ / (4 * ξ ^ 2) := min_le_left _ _
    rw [hx2]
    have : c * s ^ 2 ≤ c₅ / (4 * ξ ^ 2) * s ^ 2 := mul_le_mul_of_nonneg_right hcc (by positivity)
    rw [div_mul_eq_mul_div] at this
    rw [mul_div_assoc']
    linarith
  have hb2 : C₁ * Real.exp (-c₁ * s' ^ 2) ≤ C₁ * Real.exp (-c * s ^ 2) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₁.le
    have hcc : c ≤ c₁ / 16 := min_le_right _ _
    have h1 : s ^ 2 / 16 ≤ s' ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hc₁.le, mul_le_mul_of_nonneg_right hcc (sq_nonneg s)]
  have he : 1 ≤ Real.exp (c * (4 * ξ * M) ^ 2) := Real.one_le_exp (by positivity)
  calc _ ≤ P (E₁ ∪ E₂) := measure_mono hsub
    _ ≤ P E₁ + P E₂ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (C₅ * Real.exp (-(c₅ * x ^ 2))) +
        ENNReal.ofReal (C₁ * Real.exp (-c₁ * s' ^ 2)) := add_le_add hP1 hP2
    _ = ENNReal.ofReal (C₅ * Real.exp (-(c₅ * x ^ 2)) + C₁ * Real.exp (-c₁ * s' ^ 2)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (C * Real.exp (-c * s ^ 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h3 : (C₅ + C₁) * Real.exp (-c * s ^ 2) ≤ C * Real.exp (-c * s ^ 2) := by
          have : C₅ + C₁ ≤ C := by
            have : (C₅ + C₁) * 1 ≤ (C₅ + C₁ + 1) * Real.exp (c * (4 * ξ * M) ^ 2) :=
              mul_le_mul (by linarith) he zero_le_one (by positivity)
            simpa using this
          exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
        nlinarith

end DDDF
end LQGMetric
