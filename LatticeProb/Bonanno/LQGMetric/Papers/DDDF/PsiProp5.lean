/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.PsiProp5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiDecomp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries

/-!
# DDDF Proposition 5: comparison of `φ` and `ψ` (task P2-DDDFPSI; blueprint DDDF.P5)

DDDF (arXiv:1904.08021, `tightness.tex` l. 423–451, Prop 5 = `Prop:ComparisonFields`):
there are `C, c > 0` with `P(sup_{n ≥ 0} ‖φ_{0,n} − ψ_{0,n}‖_{[0,1]²} ≥ x) ≤ C e^{−c x²}` for all
`x > 0`; in the notation (2.25) = `DefX`, `P(X_{1,1} ≥ x) ≤ C e^{−cx²}` (`dddf_prop5`).

Proof, as DDDF: "an adaptation of Lemma 2.7 in [DZZ18]" (DZZ arXiv:1807.00422, l. 548–575)
with the inputs (2.23) (`variance_deltaM_le`) and (2.24) (`exists_incr_deltaM_le`):
* a.s. `X_{1,1} ≤ Σ_k ‖D_k‖_{[0,1]²}` (`ae_XAB_le_tsum`, the display at DZZ l. 570);
* per scale, the Fernique + concentration + union bound over boxes of side `2^{-k}k^{-4}`
  (`exists_tail_iSup_deltaM`, DZZ (2.40)–(2.41));
* the thresholds `(C_F√K₀ + λ)k^{-2}` and the union bound over `k`; the `n_k² ≤ e^{10k}` boxes
  are beaten by `σ_k^{-2} ≥ c k⁷` (from `e^{r₀² k^{2ε₀}} ≥ (r₀² k^{2ε₀})^N/N!`), which is where
  DDDF's remark "(2.23) is weaker than in DZZ but still much stronger than required" is used.
  The elementary summation is our own (DZZ: "this completes the proof").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Real
open scoped ENNReal Nat

namespace LQGMetric
namespace DDDF

open WhiteNoise

/-- `e^{r₀² k^{2ε₀}} ≥ c k⁷` for `k ≥ 1` (`e^y ≥ y^N/N!`, `2ε₀N ≥ 7`). -/
lemma exists_exp_rpow_ge_pow {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℝ, 1 ≤ k → c * k ^ 7 ≤ exp (r ^ 2 * k ^ (2 * ε)) := by
  set N : ℕ := ⌈7 / (2 * ε)⌉₊
  have hN : 7 ≤ 2 * ε * N := by
    have := Nat.le_ceil (7 / (2 * ε))
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  refine ⟨(r ^ 2) ^ N / (N ! : ℝ), by positivity, fun k hk => ?_⟩
  have hk0 : 0 ≤ k := by linarith
  have h1 := Real.pow_div_factorial_le_exp (r ^ 2 * k ^ (2 * ε)) (by positivity) N
  have h2 : k ^ 7 ≤ (k ^ (2 * ε)) ^ N := by
    rw [← Real.rpow_natCast (k ^ (2 * ε)), ← Real.rpow_mul hk0,
      show (k ^ 7 : ℝ) = k ^ ((7 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
    exact Real.rpow_le_rpow_of_exponent_le hk (by push_cast; linarith)
  calc (r ^ 2) ^ N / (N ! : ℝ) * k ^ 7 ≤ (r ^ 2) ^ N / (N ! : ℝ) * (k ^ (2 * ε)) ^ N :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (r ^ 2 * k ^ (2 * ε)) ^ N / (N ! : ℝ) := by rw [mul_pow]; ring
    _ ≤ _ := h1

/-- `n_m² ≤ e^{10(m+1)}`. -/
lemma boxN_sq_le (m : ℕ) : (boxN m : ℝ) ^ 2 ≤ exp (10 * ((m : ℝ) + 1)) := by
  set k : ℝ := (m : ℝ) + 1
  have hk : 0 ≤ k := by positivity
  have h2 : (2 : ℝ) ≤ exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h2k : (2 : ℝ) ^ (m + 1) ≤ exp k := by
    rw [show k = ((m + 1 : ℕ) : ℝ) * 1 by push_cast; ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) h2 _
  have hkk : k ≤ exp k := by have := Real.add_one_le_exp k; linarith
  have hb : (boxN m : ℝ) ≤ exp k * exp k ^ 4 := by
    simp only [boxN]; push_cast
    exact mul_le_mul h2k (pow_le_pow_left₀ hk hkk 4) (by positivity) (by positivity)
  calc (boxN m : ℝ) ^ 2 ≤ (exp k * exp k ^ 4) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hb 2
    _ = exp (10 * k) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul]; push_cast; ring_nf

/-- `Σ_m e^{−β(m+1)} ≤ 2 e^{−β}` for `β ≥ 1`. -/
lemma tsum_exp_neg_le {β : ℝ} (hβ : 1 ≤ β) :
    Summable (fun m : ℕ => exp (-(β * ((m : ℝ) + 1)))) ∧
      ∑' m : ℕ, exp (-(β * ((m : ℝ) + 1))) ≤ 2 * exp (-β) := by
  have hq0 : 0 ≤ exp (-β) := (exp_pos _).le
  have hq1 : exp (-β) ≤ 1 / 2 := by
    have : exp (-β) ≤ exp (-1) := exp_le_exp.mpr (by linarith)
    have h := Real.exp_one_gt_d9
    have : exp (-1) = (exp 1)⁻¹ := Real.exp_neg 1
    have : (exp 1)⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ (exp_pos _) (by norm_num)]; norm_num; linarith
    linarith
  have e : (fun m : ℕ => exp (-(β * ((m : ℝ) + 1)))) = fun m => exp (-β) * exp (-β) ^ m := by
    funext m
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  rw [e]
  have hs := summable_geometric_of_lt_one hq0 (by linarith)
  refine ⟨hs.mul_left _, ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 (by linarith)]
  have : (1 - exp (-β))⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}


set_option maxHeartbeats 1000000 in
/-- **DDDF Proposition 5 for `X_{a,b}`** (DDDF l. 476–480, "for some `C > 0` (depending only on
`a` and `b`)"): `P(X_{a,b} ≥ x) ≤ C e^{−cx²}`, `X_{a,b} = sup_n ‖φ_{0,n} − ψ_{0,n}‖_{R_{a,b}}`
((2.25) = `DefX`), for the continuous versions `φ_{0,n} = phiMN W P 0 n`,
`ψ_{0,n} = psiMN Q W P 0 n`. Proved directly on the square `[0, max(a,b,1)]²` (same proof). -/
theorem dddf_prop5_XAB (hW : IsWhiteNoise P W) (Q : PsiParams) (a b : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x : ℝ, 0 < x →
      P {ω | ENNReal.ofReal x ≤
          XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) a b} ≤
        ENNReal.ofReal (C * exp (-(c * x ^ 2))) := by
  have hP := hW.isProbabilityMeasure
  obtain ⟨K₀, hK₀, htail'⟩ := exists_tail_iSup_deltaM hW Q
  set R : ℝ := max (max a b) 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have htail := htail' R hR
  have hrect : (rectAB a b).toSet ⊆ SupTail.ferniqueBox 0 R := by
    intro y hy
    simp only [MarkedRect.toSet, rectAB, SupTail.ferniqueBox, Complex.zero_re,
      Complex.zero_im, zero_add] at hy ⊢
    obtain ⟨h1, h2⟩ := Complex.mem_reProdIm.mp hy
    refine Complex.mem_reProdIm.mpr ⟨⟨h1.1, h1.2.trans ?_⟩, ⟨h2.1, h2.2.trans ?_⟩⟩
    · exact (le_max_left a b).trans (le_max_left _ _)
    · exact (le_max_right a b).trans (le_max_left _ _)
  obtain ⟨c0, hc0, hpoly⟩ := exists_exp_rpow_ge_pow Q.r₀_pos Q.ε₀_pos
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set K : ℝ := SupTail.ferniqueCF * Real.sqrt (K₀ * R) with hK
  have hK0 : 0 ≤ K := by have := SupTail.ferniqueCF_pos; positivity
  have hZs : Summable fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two)
    simpa [Nat.cast_add, Nat.cast_one] using this
  set Z : ℝ := ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2 with hZ
  have hZpos : 0 < Z := hZs.tsum_pos (fun m => by positivity) 0 (by norm_num)
  set c1 : ℝ := c0 / (2 * Real.log 4) with hc1
  have hc1p : 0 < c1 := by positivity
  set l1 : ℝ := Real.sqrt (20 / c1) with hl1
  have hl1p : 0 ≤ l1 := Real.sqrt_nonneg _
  set x0 : ℝ := 4 * Z * (K + l1) with hx0
  set c' : ℝ := c1 / (32 * Z ^ 2) with hc'
  have hc'p : 0 < c' := by positivity
  refine ⟨max 4 (exp (c' * x0 ^ 2)), c', by positivity, hc'p, fun x hx => ?_⟩
  by_cases hxx : x < x0
  · calc P _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : 1 ≤ exp (c' * x0 ^ 2) * exp (-(c' * x ^ 2)) := by
          rw [← Real.exp_add]
          refine Real.one_le_exp ?_
          have : x ^ 2 ≤ x0 ^ 2 := pow_le_pow_left₀ hx.le hxx.le 2
          nlinarith
        exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (exp_pos _).le)
  push Not at hxx
  set l : ℝ := x / (2 * Z) - K with hl
  have hq : K + l1 ≤ x / (4 * Z) := by rw [le_div_iff₀ (by positivity)]; linarith
  have he2 : x / (2 * Z) = 2 * (x / (4 * Z)) := by field_simp; ring
  have hlx : x / (4 * Z) ≤ l := by rw [hl, he2]; linarith
  have hl1l : l1 ≤ l := by linarith
  have hl0 : 0 ≤ l := hl1p.trans hl1l
  have hcl : 20 ≤ c1 * l ^ 2 := by
    have h1 : l1 ^ 2 ≤ l ^ 2 := pow_le_pow_left₀ hl1p hl1l 2
    have h2 : l1 ^ 2 = 20 / c1 := Real.sq_sqrt (by positivity)
    rw [h2] at h1
    have := mul_le_mul_of_nonneg_left h1 hc1p.le
    rwa [mul_div_cancel₀ _ hc1p.ne'] at this
  set β : ℝ := c1 * l ^ 2 / 2 with hβ
  have hβ1 : 1 ≤ β := by rw [hβ]; linarith
  -- per-scale bound
  have hterm : ∀ m : ℕ, P {ω | ENNReal.ofReal (SupTail.ferniqueCF * Real.sqrt (K₀ * R) /
      ((m : ℝ) + 1) ^ 2 + l / ((m : ℝ) + 1) ^ 2) ≤ supDelta Q W P (SupTail.ferniqueBox 0 R) m ω} ≤
      ENNReal.ofReal (2 * exp (-(β * ((m : ℝ) + 1)))) := by
    intro m
    refine (htail m (l / ((m : ℝ) + 1) ^ 2) (by positivity)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    set k : ℝ := (m : ℝ) + 1 with hk
    have hk1 : 1 ≤ k := by rw [hk]; linarith [m.cast_nonneg (α := ℝ)]
    have hk0 : 0 < k := by linarith
    have hp := hpoly k hk1
    set E : ℝ := exp (Q.r₀ ^ 2 * k ^ (2 * Q.ε₀)) with hE
    have hσ : sigmaM Q m ^ 2 = Real.log 4 * E⁻¹ := by rw [sigmaM_sq, Real.exp_neg]
    have hexp : c1 * l ^ 2 * k ^ 3 ≤ (l / k ^ 2) ^ 2 / (2 * sigmaM Q m ^ 2) := by
      rw [hσ]
      have hEp : 0 < E := exp_pos _
      have e : (l / k ^ 2) ^ 2 / (2 * (Real.log 4 * E⁻¹)) =
          l ^ 2 * E / (2 * Real.log 4 * k ^ 4) := by field_simp
      rw [e, le_div_iff₀ (by positivity)]
      have h2 := mul_le_mul_of_nonneg_left hp (sq_nonneg l)
      have e2 : c1 * l ^ 2 * k ^ 3 * (2 * Real.log 4 * k ^ 4) = l ^ 2 * (c0 * k ^ 7) := by
        rw [hc1]; field_simp
      rw [e2]; exact h2
    have hn := boxN_sq_le m
    rw [← hk] at hn
    have hk3 : k ≤ k ^ 3 := by nlinarith
    have hfin : 10 * k + -(c1 * l ^ 2 * k ^ 3) ≤ -(β * k) := by
      rw [hβ]; nlinarith
    calc 2 * (boxN m : ℝ) ^ 2 * exp (-(l / k ^ 2) ^ 2 / (2 * sigmaM Q m ^ 2))
        ≤ 2 * exp (10 * k) * exp (-(c1 * l ^ 2 * k ^ 3)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hn (by norm_num)) ?_ (exp_pos _).le
            (by positivity)
          rw [neg_div]; exact exp_le_exp.mpr (neg_le_neg hexp)
      _ = 2 * exp (10 * k + -(c1 * l ^ 2 * k ^ 3)) := by rw [Real.exp_add]; ring
      _ ≤ 2 * exp (-(β * k)) :=
          mul_le_mul_of_nonneg_left (exp_le_exp.mpr hfin) (by norm_num)
  -- the event inclusion
  have hsub : {ω | ENNReal.ofReal x ≤
      XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) a b} ≤ᵐ[P]
      ⋃ m : ℕ, {ω | ENNReal.ofReal (SupTail.ferniqueCF * Real.sqrt (K₀ * R) /
        ((m : ℝ) + 1) ^ 2 + l / ((m : ℝ) + 1) ^ 2) ≤ supDelta Q W P (SupTail.ferniqueBox 0 R) m ω} := by
    filter_upwards [ae_XAB_le_tsum hW Q a b] with ω hω0 hx'
    have hω : XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) a b ≤
        ∑' m, supDelta Q W P (SupTail.ferniqueBox 0 R) m ω :=
      hω0.trans (ENNReal.tsum_le_tsum fun m => biSup_mono fun y hy => hrect hy)
    by_contra hne
    simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_le] at hne
    have hx'' : ENNReal.ofReal x ≤ _ := hx'
    have hs2 : Summable fun m : ℕ => SupTail.ferniqueCF * Real.sqrt (K₀ * R) / ((m : ℝ) + 1) ^ 2 +
        l / ((m : ℝ) + 1) ^ 2 := by
      have := hZs.mul_left (K + l)
      refine this.congr fun m => ?_
      rw [hK]; ring
    have hsum : ∑' m, supDelta Q W P (SupTail.ferniqueBox 0 R) m ω ≤ ENNReal.ofReal (x / 2) := by
      calc ∑' m, supDelta Q W P (SupTail.ferniqueBox 0 R) m ω ≤ ∑' m : ℕ, ENNReal.ofReal
            (SupTail.ferniqueCF * Real.sqrt (K₀ * R) / ((m : ℝ) + 1) ^ 2 + l / ((m : ℝ) + 1) ^ 2) :=
            ENNReal.tsum_le_tsum fun m => (hne m).le
        _ = ENNReal.ofReal (∑' m : ℕ,
            (SupTail.ferniqueCF * Real.sqrt (K₀ * R) / ((m : ℝ) + 1) ^ 2 + l / ((m : ℝ) + 1) ^ 2)) :=
            (ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hs2).symm
        _ = ENNReal.ofReal (x / 2) := by
            congr 1
            have e : (fun m : ℕ => SupTail.ferniqueCF * Real.sqrt (K₀ * R) / ((m : ℝ) + 1) ^ 2 +
                l / ((m : ℝ) + 1) ^ 2) = fun m : ℕ => (K + l) * (1 / ((m : ℝ) + 1) ^ 2) := by
              funext m; rw [hK]; ring
            rw [e, tsum_mul_left, ← hZ, hl]
            field_simp
            ring
    have := hx''.trans (hω.trans hsum)
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
    linarith
  obtain ⟨hgs, hgt⟩ := tsum_exp_neg_le hβ1
  calc P _ ≤ P (⋃ m : ℕ, {ω | ENNReal.ofReal (SupTail.ferniqueCF * Real.sqrt (K₀ * R) /
        ((m : ℝ) + 1) ^ 2 + l / ((m : ℝ) + 1) ^ 2) ≤ supDelta Q W P (SupTail.ferniqueBox 0 R) m ω}) :=
        measure_mono_ae hsub
    _ ≤ ∑' m : ℕ, P {ω | ENNReal.ofReal (SupTail.ferniqueCF * Real.sqrt (K₀ * R) /
        ((m : ℝ) + 1) ^ 2 + l / ((m : ℝ) + 1) ^ 2) ≤ supDelta Q W P (SupTail.ferniqueBox 0 R) m ω} :=
        measure_iUnion_le _
    _ ≤ ∑' m : ℕ, ENNReal.ofReal (2 * exp (-(β * ((m : ℝ) + 1)))) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' m : ℕ, 2 * exp (-(β * ((m : ℝ) + 1)))) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) (hgs.mul_left 2)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [tsum_mul_left]
        have hβx : c' * x ^ 2 ≤ β := by
          have h1 : (x / (4 * Z)) ^ 2 ≤ l ^ 2 := pow_le_pow_left₀ (by positivity) hlx 2
          have e : c' * x ^ 2 = c1 * (x / (4 * Z)) ^ 2 / 2 := by rw [hc']; field_simp; ring
          rw [e, hβ]
          have := mul_le_mul_of_nonneg_left h1 hc1p.le
          linarith
        have h3 : exp (-β) ≤ exp (-(c' * x ^ 2)) := exp_le_exp.mpr (by linarith)
        calc 2 * ∑' m : ℕ, exp (-(β * ((m : ℝ) + 1))) ≤ 2 * (2 * exp (-β)) := by linarith
          _ ≤ 4 * exp (-(c' * x ^ 2)) := by linarith
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (exp_pos _).le

/-- **DDDF Proposition 5** (`Prop:ComparisonFields`, l. 423–428): there are `C, c > 0` such that
for all `x > 0`, `P(sup_{n ≥ 0} ‖φ_{0,n} − ψ_{0,n}‖_{[0,1]²} ≥ x) ≤ C e^{−c x²}`. -/
theorem dddf_prop5 (hW : IsWhiteNoise P W) (Q : PsiParams) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x : ℝ, 0 < x →
      P {ω | ENNReal.ofReal x ≤
          XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) 1 1} ≤
        ENNReal.ofReal (C * exp (-(c * x ^ 2))) :=
  dddf_prop5_XAB hW Q 1 1

end DDDF
end LQGMetric
