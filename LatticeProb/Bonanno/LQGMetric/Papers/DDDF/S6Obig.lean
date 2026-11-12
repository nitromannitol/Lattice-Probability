/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Obig at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CMom
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CDefs

/-!
# DDDF Prop 26: the gradient term `2^{-k} sup ‖∇φ_{0,k}‖ ≤ M √k` w.h.p. (task P2-DDDF6)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 1329 (proof of Prop 26, Step 2): "using the gradient estimates (2.16), we get
`P(2^{-k} ‖∇φ_{0,k}‖_{[0,1]²} ≥ C √k) ≤ e^{-ck}` for `C` large enough". We prove the form needed
there (probability `≤ ε` for `k` large), on the box `[-2,3]²` of `Obig` (`T20C.Obig`), from the
exponential moments (2.17) on translated boxes (`T20C.prop3_expMoment_shift`, `ε = 1/4`) and
Markov's inequality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6

open WhiteNoise T20C

/-- `P(Obig k Y ≥ M √k) ≤ ε` for `k ≥ k₂`, uniformly over white noises and `C¹` versions. -/
theorem obig_tail {ε : ℝ} (hε : 0 < ε) : ∃ M : ℝ, 0 ≤ M ∧ ∃ k₂ : ℕ,
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
    ∀ (k : ℕ), k₂ ≤ k → ∀ (Y : ℂ → Ω → ℝ),
    (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ k)⁻¹ 1 x) →
    (∀ ω, ContDiff ℝ 1 fun x => Y x ω) →
      P {ω | M * √(k : ℝ) ≤ Obig k Y ω} ≤ ENNReal.ofReal ε := by
  obtain ⟨c, K, hmom⟩ := prop3_expMoment_shift (ε := 1 / 4) (by norm_num) (a := 1) one_pos
  set M : ℝ := |c| + |K| + 1
  have hM0 : 0 ≤ M := by positivity
  set L : ℝ := max 0 (Real.log (25 / ε))
  refine ⟨M, hM0, ⌈L ^ 2⌉₊ + 1, fun {Ω} _ {P} {W} hW k hk Y hY hYc => ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by
    have : (1 : ℕ) ≤ k := le_trans (Nat.le_add_left 1 _) hk
    exact_mod_cast this
  have hk0 : (0 : ℝ) < k := by linarith
  set T : ℂ → Ω → ℝ := fun c₁ ω =>
    ((2 : ℝ) ^ k)⁻¹ * ⨆ z : SupTail.ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y (x + c₁) ω) z‖
  -- rpow bookkeeping: `k^{1/4} · M √k = M k^{3/4}`, `k^{1/2} ≤ k^{3/4}`
  have e34 : (k : ℝ) ^ (1 / 4 : ℝ) * √(k : ℝ) = (k : ℝ) ^ (1 / 2 + 1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hk0]; ring_nf
  have h12 : (k : ℝ) ^ (2 * (1 / 4) : ℝ) ≤ (k : ℝ) ^ (1 / 2 + 1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hk1 (by norm_num)
  have hpos34 : 0 ≤ (k : ℝ) ^ (1 / 2 + 1 / 4 : ℝ) := by positivity
  have hsq : √(k : ℝ) ≤ (k : ℝ) ^ (1 / 2 + 1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hk1 (by norm_num)
  -- one offset
  have hone : ∀ c₁ : ℂ, P {ω | M * √(k : ℝ) ≤ T c₁ ω} ≤
      ENNReal.ofReal (Real.exp (-(k : ℝ) ^ (1 / 2 + 1 / 4 : ℝ))) := by
    intro c₁
    obtain ⟨hmeas, hint⟩ := hmom hW k Y hY hYc c₁
    set g : Ω → ℝ≥0∞ := fun ω =>
      ENNReal.ofReal (Real.exp (1 * (k : ℝ) ^ (1 / 4 : ℝ) * T c₁ ω))
    have hg : AEMeasurable g P :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (Real.measurable_exp.comp_aemeasurable (hmeas.const_mul _))
    set t : ℝ := Real.exp (1 * (k : ℝ) ^ (1 / 4 : ℝ) * (M * √(k : ℝ)))
    have hsub : {ω | M * √(k : ℝ) ≤ T c₁ ω} ⊆ {ω | ENNReal.ofReal t ≤ g ω} := by
      intro ω hω
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      exact mul_le_mul_of_nonneg_left hω (by positivity)
    have hmk := meas_ge_le_lintegral_div hg (ε := ENNReal.ofReal t)
      (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top
    refine (measure_mono hsub).trans (hmk.trans ?_)
    refine (ENNReal.div_le_div_right hint _).trans ?_
    rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have e1 : 1 * (k : ℝ) ^ (1 / 4 : ℝ) * (M * √(k : ℝ)) = M * (k : ℝ) ^ (1 / 2 + 1 / 4 : ℝ) := by
      rw [← e34]; ring
    rw [e1]
    have hc : c * (k : ℝ) ^ (1 / 2 + 1 / 4 : ℝ) ≤ |c| * (k : ℝ) ^ (1 / 2 + 1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self c) hpos34
    have hK : K * (k : ℝ) ^ (2 * (1 / 4) : ℝ) ≤ |K| * (k : ℝ) ^ (1 / 2 + 1 / 4 : ℝ) :=
      (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)).trans
        (mul_le_mul_of_nonneg_left h12 (abs_nonneg K))
    simp only [M]; nlinarith
  -- union over the 25 offsets
  have hsub : {ω | M * √(k : ℝ) ≤ Obig k Y ω} ⊆ ⋃ c₁ ∈ offs, {ω | M * √(k : ℝ) ≤ T c₁ ω} := by
    intro ω hω
    have hω' : M * √(k : ℝ) ≤ Obig k Y ω := hω
    unfold Obig at hω'
    obtain ⟨c₁, hc₁, h⟩ := (Finset.le_sup'_iff offs_nonempty).1 hω'
    exact mem_biUnion hc₁ h
  have hsum := (measure_mono (μ := P) hsub).trans (measure_biUnion_finset_le (μ := P) offs _)
  refine hsum.trans ?_
  refine (Finset.sum_le_sum fun c₁ _ => hone c₁).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  -- `25 e^{-k^{3/4}} ≤ ε`
  have hL : L ≤ (k : ℝ) ^ (1 / 2 + 1 / 4 : ℝ) := by
    have h1 : (L ^ 2 : ℝ) < k := by
      have := Nat.le_ceil (L ^ 2)
      have h2 : ((⌈L ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
      push_cast at h2; linarith
    have h3 : L < √(k : ℝ) := (Real.lt_sqrt (le_max_left _ _)).2 h1
    linarith
  have hexp : Real.exp (-(k : ℝ) ^ (1 / 2 + 1 / 4 : ℝ)) ≤ ε / 25 := by
    calc Real.exp (-(k : ℝ) ^ (1 / 2 + 1 / 4 : ℝ)) ≤ Real.exp (-Real.log (25 / ε)) :=
          Real.exp_le_exp.2 (by linarith [le_max_right 0 (Real.log (25 / ε))])
      _ = ε / 25 := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  calc (offs.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(k : ℝ) ^ (1 / 2 + 1 / 4 : ℝ)))
      ≤ (25 : ℝ≥0∞) * ENNReal.ofReal (ε / 25) := by
        gcongr
        · exact_mod_cast card_offs_le
    _ = ENNReal.ofReal ε := by
        rw [show (25 : ℝ≥0∞) = ENNReal.ofReal 25 by simp, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring

end S6
end DDDF
end LQGMetric
