/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6TailsAB5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6TailsAB4
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Mul

/-!
# DDDF (6.102)/(6.103) for `[0,a] × [0,b]` (task P2-DDDF6e, packet O6)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1639–1647 (`eq:RightTails`, `eq:LeftTails`): for
`a, b > 0` there are `c, C > 0` such that for `s > 2`, uniformly in `δ ∈ (0,1)`,
`P(λ_δ^{-1} L^{(δ)}_{a,b} ≥ e^s) ≤ C e^{-c s²/log s}` and `P(λ_δ^{-1} L^{(δ)}_{a,b} ≤ e^{-s}) ≤
C e^{-c s²}`. "The same argument as in the two previous paragraphs" (l. 1608–1613): for
`δ = 2^{-r} 2^{-n}`, decouple `φ_{2^{-r},1}` (`tail_decomp_AB`), use (6.98)
(`s6_eq6_98_of_Lambda`) and the dyadic tails of `L^{(n)}_{a 2^r, b 2^r}` (`dyadic_right_AB`,
`dyadic_left_AB`). Given `Λ_n` bounded (Theorem 20), as `S6.s6_eq6_102_11`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6AB

open WhiteNoise SupTail S6

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- the scale `α = 2^{-r} ∈ [1/2, 1]` and the shapes `α⁻¹ a ∈ [min a b, 2 max a b]` -/
lemma alpha_facts {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 / 2 ≤ (2 : ℝ) ^ (-r) ∧ (2 : ℝ) ^ (-r) ≤ 1 ∧
      ((2 : ℝ) ^ (-r))⁻¹ * a ∈ Icc (min a b) (2 * max a b) ∧
      ((2 : ℝ) ^ (-r))⁻¹ * b ∈ Icc (min a b) (2 * max a b) := by
  set α : ℝ := (2 : ℝ) ^ (-r)
  have ha1 : α ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have ha12 : 1 / 2 ≤ α := by
    have : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ (-r) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rwa [Real.rpow_neg_one, ← one_div] at this
  have ha0 : 0 < α := by positivity
  have hc1 : 1 ≤ α⁻¹ := one_le_inv_iff₀.2 ⟨ha0, ha1⟩
  have hc2 : α⁻¹ ≤ 2 := by rw [inv_le_comm₀ ha0 (by norm_num)]; linarith
  have key : ∀ x, 0 < x → x ≤ max a b → min a b ≤ x → α⁻¹ * x ∈ Icc (min a b) (2 * max a b) :=
    fun x hx hxm hxn => ⟨hxn.trans (le_mul_of_one_le_left hx.le hc1),
      mul_le_mul hc2 hxm hx.le (by norm_num)⟩
  exact ⟨ha12, ha1, key a ha (le_max_left _ _) (min_le_left _ _),
    key b hb (le_max_right _ _) (min_le_right _ _)⟩

/-- **DDDF (6.102)** (`eq:RightTails`, l. 1641–1643) for `[0,a] × [0,b]`, given `Λ` bounded. -/
theorem s6_eq6_102_AB (hW : IsWhiteNoise P W) (hξ : 0 < ξ)
    (hΛ : ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ B : ℝ, ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ s : ℝ, 2 < s → ∀ δ : ℝ, 0 < δ → δ < 1 →
      P {ω | Real.exp s * lambdaDelta ξ W P δ ≤ lenObs ξ (phiVer W P δ 1) (rectAB a b) ω} ≤
        ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s)) := by
  have hP := hW.isProbabilityMeasure
  obtain ⟨C₆, h698⟩ := s6_eq6_98_of_Lambda hW hξ hΛ
  obtain ⟨c₁, C₁, hc₁, hC₁, hR⟩ := dyadic_right_AB hW hξ hΛ (A₀ := min a b)
    (B₀ := 2 * max a b) (lt_min ha hb)
  set m := max a b
  have hm : 0 < m := lt_max_of_lt_left ha
  set m₀ : ℝ := ferniqueCF * Real.sqrt (8 * m * m)
  have hm₀ : 0 ≤ m₀ := by have := ferniqueCF_pos; positivity
  set D : ℝ := ξ * m₀ + |C₆|
  have hD : 0 ≤ D := by positivity
  set c : ℝ := min (c₁ / 4) (1 / (32 * ξ ^ 2))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨c, max (2 + C₁) (Real.exp (c * max (max 4 (4 * D)) 2 ^ 2 / Real.log 2)), hc,
    lt_max_of_lt_left (by linarith), fun s hs δ hδ0 hδ1 => absorb_log (P := P)
    (E := fun s => {ω | Real.exp s * lambdaDelta ξ W P δ ≤
      lenObs ξ (phiVer W P δ 1) (rectAB a b) ω}) hc (fun s hsS => ?_) s hs⟩
  beta_reduce
  have hs4 : 4 < s := lt_of_le_of_lt (le_max_left _ _) hsS
  have hsD : 4 * D < s := lt_of_le_of_lt (le_max_right _ _) hsS
  have hls : 0 < Real.log s := Real.log_pos (by linarith)
  obtain ⟨n, r, hr0, hr1, rfl⟩ := exists_split hδ0 hδ1
  obtain ⟨hlo98, -⟩ := h698 n r hr0 hr1
  obtain ⟨ha12, ha1, hxa, hxb⟩ := alpha_facts hr0 hr1 ha hb
  set α : ℝ := (2 : ℝ) ^ (-r)
  have ha0 : 0 < α := by positivity
  rw [two_rpow_split n r] at hlo98 ⊢
  set lamδ := lambdaDelta ξ W P (α * (2 : ℝ)⁻¹ ^ n)
  set lamn := lambdaN ξ W P n
  have hlam0 : 0 < lamn := lambdaN_pos hW n
  set u : ℝ := s / (4 * ξ)
  have hu : 0 ≤ u := by positivity
  set t : ℝ := Real.exp (s - ξ * (m₀ + u)) * lamδ
  obtain ⟨hdec, -⟩ := tail_decomp_AB (ξ := ξ) hW hξ.le n ha12 ha1 ha.le hb.le hm
    (le_max_left a b) (le_max_right a b) hu t
  have ht : Real.exp (ξ * (m₀ + u)) * t = Real.exp s * lamδ := by
    simp only [t]; rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
  rw [ht] at hdec
  refine hdec.trans ?_
  set s' : ℝ := 3 * s / 4 - D
  have hs'2 : s / 2 ≤ s' := by simp only [s']; linarith
  have hs'le : s' ≤ s := by simp only [s']; linarith
  have hs'2' : 2 < s' := by linarith
  have hZ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hP1 : P {ω | t ≤ α * lenObs ξ (phiMN W P 0 n) (rectAB (α⁻¹ * a) (α⁻¹ * b)) ω} ≤
      ENNReal.ofReal (C₁ * Real.exp (-c₁ * s' ^ 2 / Real.log s')) := by
    refine (measure_mono fun ω hω => ?_).trans (hR _ hxa _ hxb n s' hs'2')
    simp only [mem_ofPred_eq] at hω ⊢
    have hL0 : 0 ≤ lenObs ξ (phiMN W P 0 n) (rectAB (α⁻¹ * a) (α⁻¹ * b)) ω :=
      ENNReal.toReal_nonneg
    have h2 : α * lenObs ξ (phiMN W P 0 n) (rectAB (α⁻¹ * a) (α⁻¹ * b)) ω ≤
        lenObs ξ (phiMN W P 0 n) (rectAB (α⁻¹ * a) (α⁻¹ * b)) ω := mul_le_of_le_one_left hL0 ha1
    have h4 : Real.exp s' * lamn ≤ t := by
      have hu4 : ξ * u = s / 4 := by simp only [u]; field_simp
      have e1 : Real.exp s' * lamn = Real.exp (s - ξ * (m₀ + u)) * (Real.exp (-|C₆|) * lamn) := by
        rw [← mul_assoc, ← Real.exp_add]; congr 2; simp only [s', D]; rw [mul_add, hu4]; ring
      rw [e1]
      refine mul_le_mul_of_nonneg_left (le_trans ?_ hlo98) (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith [le_abs_self C₆]))
        hlam0.le
    linarith
  have hgauss : 2 * Real.exp (-u ^ 2 / (2 * 1 ^ 2)) ≤
      2 * Real.exp (-c * s ^ 2 / Real.log s) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
    have hl1 : 1 ≤ Real.log s := by
      rw [← Real.exp_le_exp, Real.exp_log (by linarith)]
      exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hs4.le
    have hu2 : u ^ 2 / (2 * 1 ^ 2) = s ^ 2 / (32 * ξ ^ 2) := by simp only [u]; field_simp; ring
    have h1 : c * s ^ 2 / Real.log s ≤ c * s ^ 2 := div_le_self (by positivity) hl1
    have h2 : c * s ^ 2 ≤ s ^ 2 / (32 * ξ ^ 2) := by
      rw [div_eq_mul_one_div, mul_comm (s ^ 2)]
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
    rw [neg_div, neg_mul, neg_div, hu2]; linarith
  have hP1' : C₁ * Real.exp (-c₁ * s' ^ 2 / Real.log s') ≤
      C₁ * Real.exp (-c * s ^ 2 / Real.log s) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₁.le
    have hls' : 0 < Real.log s' := Real.log_pos (by linarith)
    have hlog : Real.log s' ≤ Real.log s := Real.log_le_log (by linarith) hs'le
    have h1 : c * s ^ 2 / Real.log s ≤ c₁ / 4 * s ^ 2 / Real.log s :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
        hls.le
    have h2 : c₁ / 4 * s ^ 2 / Real.log s ≤ c₁ * s' ^ 2 / Real.log s' := by
      have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ s / 2) hs'2
      have : c₁ / 4 * s ^ 2 ≤ c₁ * s' ^ 2 := by
        have := mul_le_mul_of_nonneg_left hsq hc₁.le
        nlinarith
      exact div_le_div₀ (by positivity) this hls' hlog
    rw [neg_mul, neg_div, neg_mul, neg_div]; linarith
  calc ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * 1 ^ 2))) +
        P {ω | t ≤ α * lenObs ξ (phiMN W P 0 n) (rectAB (α⁻¹ * a) (α⁻¹ * b)) ω}
      ≤ ENNReal.ofReal (2 * Real.exp (-c * s ^ 2 / Real.log s)) +
          ENNReal.ofReal (C₁ * Real.exp (-c * s ^ 2 / Real.log s)) :=
        add_le_add (ENNReal.ofReal_le_ofReal hgauss) (hP1.trans (ENNReal.ofReal_le_ofReal hP1'))
    _ = ENNReal.ofReal ((2 + C₁) * Real.exp (-c * s ^ 2 / Real.log s)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

/-- **DDDF (6.103)** (`eq:LeftTails`, l. 1644–1646) for `[0,a] × [0,b]`, given `Λ` bounded. -/
theorem s6_eq6_103_AB (hW : IsWhiteNoise P W) (hξ : 0 < ξ)
    (hΛ : ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ B : ℝ, ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ s : ℝ, 2 < s → ∀ δ : ℝ, 0 < δ → δ < 1 →
      P {ω | lenObs ξ (phiVer W P δ 1) (rectAB a b) ω ≤ Real.exp (-s) * lambdaDelta ξ W P δ} ≤
        ENNReal.ofReal (C * Real.exp (-c * s ^ 2)) := by
  have hP := hW.isProbabilityMeasure
  obtain ⟨C₆, h698⟩ := s6_eq6_98_of_Lambda hW hξ hΛ
  obtain ⟨c₁, C₁, hc₁, hC₁, hL⟩ := dyadic_left_AB hW hξ hΛ (A₀ := min a b)
    (B₀ := 2 * max a b) (lt_min ha hb)
  set m := max a b
  have hm : 0 < m := lt_max_of_lt_left ha
  set m₀ : ℝ := ferniqueCF * Real.sqrt (8 * m * m)
  have hm₀ : 0 ≤ m₀ := by have := ferniqueCF_pos; positivity
  set D : ℝ := ξ * m₀ + |C₆| + Real.log 2
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hD : 0 ≤ D := by positivity
  set c : ℝ := min (c₁ / 4) (1 / (32 * ξ ^ 2))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨c, max (2 + C₁) (Real.exp (c * max (max 4 (4 * D)) 2 ^ 2)), hc,
    lt_max_of_lt_left (by linarith), fun s hs δ hδ0 hδ1 => absorb_sq (P := P)
    (E := fun s => {ω | lenObs ξ (phiVer W P δ 1) (rectAB a b) ω ≤
      Real.exp (-s) * lambdaDelta ξ W P δ}) hc (fun s hsS => ?_) s hs⟩
  beta_reduce
  have hs4 : 4 < s := lt_of_le_of_lt (le_max_left _ _) hsS
  have hsD : 4 * D < s := lt_of_le_of_lt (le_max_right _ _) hsS
  obtain ⟨n, r, hr0, hr1, rfl⟩ := exists_split hδ0 hδ1
  obtain ⟨-, hhi98⟩ := h698 n r hr0 hr1
  obtain ⟨ha12, ha1, hxa, hxb⟩ := alpha_facts hr0 hr1 ha hb
  set α : ℝ := (2 : ℝ) ^ (-r)
  have ha0 : 0 < α := by positivity
  rw [two_rpow_split n r] at hhi98 ⊢
  set lamδ := lambdaDelta ξ W P (α * (2 : ℝ)⁻¹ ^ n)
  set lamn := lambdaN ξ W P n
  have hlam0 : 0 < lamn := lambdaN_pos hW n
  set u : ℝ := s / (4 * ξ)
  have hu : 0 ≤ u := by positivity
  set t : ℝ := Real.exp (-s + ξ * (m₀ + u)) * lamδ
  obtain ⟨-, hdec⟩ := tail_decomp_AB (ξ := ξ) hW hξ.le n ha12 ha1 ha.le hb.le hm
    (le_max_left a b) (le_max_right a b) hu t
  have ht : Real.exp (-(ξ * (m₀ + u))) * t = Real.exp (-s) * lamδ := by
    simp only [t]; rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
  rw [ht] at hdec
  refine hdec.trans ?_
  set s'' : ℝ := 3 * s / 4 - D
  have hs'2 : s / 2 ≤ s'' := by simp only [s'']; linarith
  have hs'2' : 2 < s'' := by linarith
  have hP1 : P {ω | α * lenObs ξ (phiMN W P 0 n) (rectAB (α⁻¹ * a) (α⁻¹ * b)) ω ≤ t} ≤
      ENNReal.ofReal (C₁ * Real.exp (-c₁ * s'' ^ 2)) := by
    refine (measure_mono fun ω hω => ?_).trans (hL _ hxa _ hxb n s'' hs'2')
    simp only [mem_ofPred_eq] at hω ⊢
    have hL0 : 0 ≤ lenObs ξ (phiMN W P 0 n) (rectAB (α⁻¹ * a) (α⁻¹ * b)) ω :=
      ENNReal.toReal_nonneg
    have h2 : lenObs ξ (phiMN W P 0 n) (rectAB (α⁻¹ * a) (α⁻¹ * b)) ω ≤
        2 * (α * lenObs ξ (phiMN W P 0 n) (rectAB (α⁻¹ * a) (α⁻¹ * b)) ω) := by
      have := mul_le_mul_of_nonneg_right ha12 hL0; linarith
    have h4 : 2 * t ≤ Real.exp (-s'') * lamn := by
      have hu4 : ξ * u = s / 4 := by simp only [u]; field_simp
      have e1 : Real.exp (-s'') * lamn = Real.exp (-s + ξ * (m₀ + u)) *
          (Real.exp |C₆| * (Real.exp (Real.log 2) * lamn)) := by
        rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 2; simp only [s'', D]; rw [mul_add, hu4]; ring
      rw [e1, Real.exp_log (by norm_num)]
      simp only [t]
      have h5 : lamδ ≤ Real.exp |C₆| * lamn :=
        hhi98.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (le_abs_self C₆)) hlam0.le)
      have : 2 * lamδ ≤ Real.exp |C₆| * (2 * lamn) := by linarith
      calc 2 * (Real.exp (-s + ξ * (m₀ + u)) * lamδ)
          = Real.exp (-s + ξ * (m₀ + u)) * (2 * lamδ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    linarith
  have hgauss : 2 * Real.exp (-u ^ 2 / (2 * 1 ^ 2)) ≤ 2 * Real.exp (-c * s ^ 2) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
    have hu2 : u ^ 2 / (2 * 1 ^ 2) = s ^ 2 / (32 * ξ ^ 2) := by simp only [u]; field_simp; ring
    have h2 : c * s ^ 2 ≤ s ^ 2 / (32 * ξ ^ 2) := by
      rw [div_eq_mul_one_div, mul_comm (s ^ 2)]
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
    rw [neg_div, neg_mul, hu2]; linarith
  have hP1' : C₁ * Real.exp (-c₁ * s'' ^ 2) ≤ C₁ * Real.exp (-c * s ^ 2) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₁.le
    have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ s / 2) hs'2
    have h1 : c * s ^ 2 ≤ c₁ / 4 * s ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
    have := mul_le_mul_of_nonneg_left hsq hc₁.le
    rw [neg_mul, neg_mul]; nlinarith
  calc ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * 1 ^ 2))) +
        P {ω | α * lenObs ξ (phiMN W P 0 n) (rectAB (α⁻¹ * a) (α⁻¹ * b)) ω ≤ t}
      ≤ ENNReal.ofReal (2 * Real.exp (-c * s ^ 2)) +
          ENNReal.ofReal (C₁ * Real.exp (-c * s ^ 2)) :=
        add_le_add (ENNReal.ofReal_le_ofReal hgauss) (hP1.trans (ENNReal.ofReal_le_ofReal hP1'))
    _ = ENNReal.ofReal ((2 + C₁) * Real.exp (-c * s ^ 2)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end S6AB
end DDDF
end LQGMetric
