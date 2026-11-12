/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P5ULarge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiProp5

/-!
# DDDF Proposition 5 on large rectangles, with explicit dependence on the size (task P2-DDDF18S1)

DDDF (arXiv:1904.08021, `tightness.tex` l. 423–451, Prop 5 = `Prop:ComparisonFields`) state the
comparison of `φ` and `ψ` with constants "depending only on `a` and `b`". The proof of Prop 18,
Step 1 (l. 906–907) uses `P(X_{3k,k} ≥ C√k) ≤ C e^{-ck}` uniformly in `k`. We read the size
dependence off the same proof (`dddf_prop5_XAB`, PsiProp5.lean, DZZ Lemma 2.7 adaptation): on
`[0,R]²` the Fernique threshold of scale `m` is `C_F √(K₀R)/(m+1)²` (`exists_tail_iSup_deltaM`),
so the tail `P(X_{a,b} ≥ x) ≤ 4 e^{-c'x²}` holds for all `x ≥ x₁(√R + 1)`, `R = max(a,b,1)`,
with `x₁, c'` independent of `a, b` (`prop5_XAB_large`). The proof is that of `dddf_prop5_XAB`
with the constants fixed before `a, b`.
* `prop5_X3k_tail`: `P(X_{3k,k} ≥ A√k) ≤ 4 e^{-c'A²k}` for `k ≥ 1` (DDDF l. 906–907).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Real
open scoped ENNReal Nat

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

set_option maxHeartbeats 1000000 in
/-- **DDDF Prop 5 with the size dependence** (proof of `dddf_prop5_XAB`): there are `x₁, c' > 0`
such that for all `a, b` and `x ≥ x₁ (√(max(a,b,1)) + 1)`, `P(X_{a,b} ≥ x) ≤ 4 e^{-c'x²}`. -/
theorem prop5_XAB_large (hW : IsWhiteNoise P W) (Q : PsiParams) :
    ∃ x₁ c' : ℝ, 0 < x₁ ∧ 0 < c' ∧ ∀ a b x : ℝ, x₁ * (√(max (max a b) 1) + 1) ≤ x →
      P {ω | ENNReal.ofReal x ≤
          XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) a b} ≤
        ENNReal.ofReal (4 * exp (-(c' * x ^ 2))) := by
  obtain ⟨K₀, hK₀, htail'⟩ := exists_tail_iSup_deltaM hW Q
  obtain ⟨c0, hc0, hpoly⟩ := exists_exp_rpow_ge_pow Q.r₀_pos Q.ε₀_pos
  have hZs : Summable fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two)
    simpa [Nat.cast_add, Nat.cast_one] using this
  set Z : ℝ := ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2 with hZ
  have hZpos : 0 < Z := hZs.tsum_pos (fun m => by positivity) 0 (by norm_num)
  set c1 : ℝ := c0 / (2 * Real.log 4) with hc1
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hc1p : 0 < c1 := by positivity
  set l1 : ℝ := Real.sqrt (20 / c1) with hl1
  have hl1p : 0 ≤ l1 := Real.sqrt_nonneg _
  set c' : ℝ := c1 / (32 * Z ^ 2) with hc'
  have hc'p : 0 < c' := by positivity
  have hCF := SupTail.ferniqueCF_pos
  refine ⟨4 * Z * (SupTail.ferniqueCF * Real.sqrt K₀ + l1 + 1), c', by positivity, hc'p,
    fun a b x hx => ?_⟩
  have hP := hW.isProbabilityMeasure
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
  set K : ℝ := SupTail.ferniqueCF * Real.sqrt (K₀ * R) with hK
  have hK0 : 0 ≤ K := by positivity
  set x0 : ℝ := 4 * Z * (K + l1) with hx0
  have hxx : x0 ≤ x := by
    refine le_trans ?_ hx
    have hsR : 0 ≤ √R := Real.sqrt_nonneg _
    have e : K = SupTail.ferniqueCF * Real.sqrt K₀ * √R := by
      rw [hK, Real.sqrt_mul hK₀.le]; ring
    rw [hx0, e]
    have h4Z : 0 ≤ 4 * Z := by positivity
    have hA : 0 ≤ SupTail.ferniqueCF * Real.sqrt K₀ := by positivity
    nlinarith [mul_nonneg h4Z (mul_nonneg hA hsR), mul_nonneg h4Z hsR, mul_nonneg h4Z hl1p]
  have hx : 0 < x := lt_of_lt_of_le (by positivity) hx
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

/-- **`X_{3k,k}` tail uniform in `k`** (DDDF l. 906–907, "Proposition 5 to bound `X_{3k,k}`"):
`P(X_{3k,k} ≥ A√k) ≤ 4 e^{-ck}` for all `k ≥ 1`. -/
theorem prop5_X3k_tail (hW : IsWhiteNoise P W) (Q : PsiParams) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      P {ω | ENNReal.ofReal (A * √k) ≤
          XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) (3 * k) k} ≤
        ENNReal.ofReal (4 * exp (-(c * k))) := by
  obtain ⟨x₁, c', hx₁, hc', h⟩ := prop5_XAB_large hW Q
  refine ⟨3 * x₁, c' * (3 * x₁) ^ 2, by positivity, by positivity, fun k hk => ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hR : max (max (3 * (k : ℝ)) k) 1 = 3 * k := by
    rw [max_eq_left (by linarith : (k : ℝ) ≤ 3 * k), max_eq_left (by linarith)]
  have hs1 : 1 ≤ √(k : ℝ) := Real.one_le_sqrt.mpr hk1
  have hs3 : √(3 * (k : ℝ)) ≤ 2 * √k := by
    rw [show (2 : ℝ) * √k = √(4 * k) by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  refine (h (3 * k) k (3 * x₁ * √k) ?_).trans (ENNReal.ofReal_le_ofReal ?_)
  · rw [hR]; nlinarith
  · have e : c' * (3 * x₁ * √(k : ℝ)) ^ 2 = c' * (3 * x₁) ^ 2 * k := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    rw [e]

end DDDF
end LQGMetric
