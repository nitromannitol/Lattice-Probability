import LatticeProb.Prob.McLeish.Remainder
import LatticeProb.Prob.McLeish.Truncation
import LatticeProb.Prob.McLeish.ProductMoment
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Order.Basic

/-!
# Convergence in measure of the normalised exponential ratio

For a row-indexed array `X n k` of real random variables, the truncated terms `trunc (X n) c`
define the quotient `exp (i t ∑ X') / ∏ (1 + i t X')`. When the sum of squares of the terms
converges in measure to a level `σsq < c` and the terms are uniformly small in measure, this
quotient converges in measure to `exp (-σsq t ^ 2 / 2)`.

## Main results

* `prodOneAddI_mul_truncRatio` : the quotient times the product is the exponential.
* `norm_truncRatio_sub_le` : the deterministic error bound for the quotient.
* `tendstoInMeasure_truncRatio` : the convergence in measure of the quotient.
-/

namespace LatticeProb.McLeish

open MeasureTheory Filter Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The ratio `exp (i t ∑_{k<n} X' k) / ∏_{k<n} (1 + i t X' k)` for the truncated terms
`X' = trunc X c`. -/
noncomputable def truncRatio (X : ℕ → Ω → ℝ) (c t : ℝ) (n : ℕ) (ω : Ω) : ℂ :=
  Complex.exp (Complex.I * ((t * ∑ k ∈ Finset.range n, trunc X c k ω : ℝ) : ℂ)) /
    prodOneAddI (trunc X c) t n ω

/-- The product of the factors `1 + i t X' k` times the ratio is the exponential. -/
theorem prodOneAddI_mul_truncRatio (X : ℕ → Ω → ℝ) (c t : ℝ) (n : ℕ) (ω : Ω) :
    prodOneAddI (trunc X c) t n ω * truncRatio X c t n ω =
      Complex.exp (Complex.I * ((t * ∑ k ∈ Finset.range n, trunc X c k ω : ℝ) : ℂ)) := by
  have hP : prodOneAddI (trunc X c) t n ω ≠ 0 := by
    unfold prodOneAddI
    exact Finset.prod_ne_zero_iff.mpr fun k _ => one_add_I_mul_ne_zero _
  unfold truncRatio
  rw [mul_div_assoc', mul_div_cancel_left₀ _ hP]

/-- For `b ≤ a ≤ 0`, the difference of the exponentials is at most `a - b`. -/
private lemma exp_sub_exp_le_sub {a b : ℝ} (hab : b ≤ a) (ha : a ≤ 0) :
    Real.exp a - Real.exp b ≤ a - b := by
  have hexp : Real.exp b = Real.exp a * Real.exp (b - a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h1 : Real.exp a * (b - a + 1) ≤ Real.exp b := by
    rw [hexp]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (b - a)])
      (Real.exp_nonneg a)
  have h2 : Real.exp a ≤ 1 := Real.exp_le_one_iff.mpr ha
  have h3 : 0 ≤ (1 - Real.exp a) * (a - b) := mul_nonneg (by linarith) (by linarith)
  linarith

/-- The exponential is `1`-Lipschitz on the nonpositive reals. -/
private lemma abs_exp_sub_exp_le {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b| := by
  rcases le_total b a with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 h)), abs_of_nonneg (sub_nonneg.2 h)]
    exact exp_sub_exp_le_sub h ha
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 h)), abs_sub_comm a b,
      abs_of_nonneg (sub_nonneg.2 h)]
    exact exp_sub_exp_le_sub h hb

/-- The deterministic error bound for the ratio, when the sum of squares is within `δ` of `σsq`
and every term is at most `δ` in modulus. -/
theorem norm_truncRatio_sub_le (X : ℕ → Ω → ℝ) (n : ℕ) (σsq c t δ : ℝ) (ω : Ω) (hσ : 0 ≤ σsq)
    (hδ : 0 ≤ δ) (hδc : σsq + δ ≤ c) (htδ : |t| * δ ≤ 1 / 2) (hρ : 2 * |t| ^ 3 * δ * c ≤ 1)
    (hX : ∀ k < n, |X k ω| ≤ δ) (hV : |∑ k ∈ Finset.range n, X k ω ^ 2 - σsq| ≤ δ) :
    ‖truncRatio X c t n ω - Complex.exp ((-(σsq * t ^ 2 / 2) : ℝ) : ℂ)‖ ≤
      4 * |t| ^ 3 * δ * c + t ^ 2 * δ / 2 := by
  have hVc : ∑ k ∈ Finset.range n, X k ω ^ 2 ≤ c := by
    have := (abs_le.mp hV).2
    linarith
  have hsq : sqSum X n ω ≤ c := hVc
  have htrunc : ∀ k ∈ Finset.range n, trunc X c k ω = X k ω := fun k hk =>
    trunc_eq_of_le X c (Finset.mem_range.1 hk).le ω hsq
  have hsum : ∑ k ∈ Finset.range n, trunc X c k ω = ∑ k ∈ Finset.range n, X k ω :=
    sum_trunc_eq_of_sqSum_le X c n ω hsq
  have hprod : prodOneAddI (trunc X c) t n ω =
      ∏ k ∈ Finset.range n, (1 + Complex.I * ((t * X k ω : ℝ) : ℂ)) := by
    unfold prodOneAddI
    exact Finset.prod_congr rfl fun k hk => by rw [htrunc k hk]
  have hq : truncRatio X c t n ω =
      Complex.exp (Complex.I * ((t * ∑ k ∈ Finset.range n, X k ω : ℝ) : ℂ)) /
        ∏ k ∈ Finset.range n, (1 + Complex.I * ((t * X k ω : ℝ) : ℂ)) := by
    unfold truncRatio
    rw [hsum, hprod]
  have hA0 : 0 ≤ 4 * |t| ^ 3 * δ :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (abs_nonneg t) 3)) hδ
  have hρ' : 2 * |t| ^ 3 * δ * ∑ k ∈ Finset.range n, X k ω ^ 2 ≤ 1 := by
    have h2 : 0 ≤ 2 * |t| ^ 3 * δ :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (abs_nonneg t) 3)) hδ
    have h1 := mul_le_mul_of_nonneg_left hVc h2
    linarith
  have hE : ‖Complex.exp (Complex.I * ((t * ∑ k ∈ Finset.range n, X k ω : ℝ) : ℂ)) /
        ∏ k ∈ Finset.range n, (1 + Complex.I * ((t * X k ω : ℝ) : ℂ)) -
      Complex.exp (((-(t ^ 2 * ∑ k ∈ Finset.range n, X k ω ^ 2) / 2 : ℝ) : ℂ))‖ ≤
      4 * |t| ^ 3 * δ * ∑ k ∈ Finset.range n, X k ω ^ 2 :=
    norm_exp_div_prod_sub_le (fun k => X k ω) t δ n (fun k hk => hX k hk) htδ hρ'
  have hV4 : 4 * |t| ^ 3 * δ * ∑ k ∈ Finset.range n, X k ω ^ 2 ≤ 4 * |t| ^ 3 * δ * c :=
    mul_le_mul_of_nonneg_left hVc hA0
  have hd : ‖Complex.exp (((-(t ^ 2 * ∑ k ∈ Finset.range n, X k ω ^ 2) / 2 : ℝ) : ℂ)) -
      Complex.exp ((-(σsq * t ^ 2 / 2) : ℝ) : ℂ)‖ ≤ t ^ 2 * δ / 2 := by
    have ha : -(t ^ 2 * ∑ k ∈ Finset.range n, X k ω ^ 2) / 2 ≤ 0 := by
      have hS : 0 ≤ ∑ k ∈ Finset.range n, X k ω ^ 2 :=
        Finset.sum_nonneg fun k _ => sq_nonneg (X k ω)
      have := mul_nonneg (sq_nonneg t) hS
      linarith
    have hb : -(σsq * t ^ 2 / 2) ≤ 0 := by
      have := mul_nonneg hσ (sq_nonneg t)
      linarith
    have hV1 := (abs_le.mp hV).1
    have hV2 := (abs_le.mp hV).2
    have hd1 := mul_le_mul_of_nonneg_left hV2 (sq_nonneg t)
    have hd2 := mul_le_mul_of_nonneg_left hV1 (sq_nonneg t)
    rw [← Complex.ofReal_exp, ← Complex.ofReal_exp, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    exact (abs_exp_sub_exp_le ha hb).trans (abs_le.mpr ⟨by linarith, by linarith⟩)
  rw [hq]
  refine (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add hE hd).trans ?_)
  linarith

/-- For positive `δ` small enough, the three smallness conditions and the final bound below `ε`
hold simultaneously. -/
private lemma exists_delta_pos (σsq c t ε : ℝ) (hσ : 0 ≤ σsq) (hσc : σsq < c) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ σsq + δ ≤ c ∧ |t| * δ ≤ 1 / 2 ∧ 2 * |t| ^ 3 * δ * c ≤ 1 ∧
      4 * |t| ^ 3 * δ * c + t ^ 2 * δ / 2 < ε := by
  have hc0 : 0 < c := by linarith
  have hT : 0 ≤ |t| := abs_nonneg t
  have hT3c : 0 ≤ |t| ^ 3 * c := mul_nonneg (pow_nonneg hT 3) hc0.le
  have hsq : 0 ≤ t ^ 2 := sq_nonneg t
  have hMnn : 0 ≤ 2 * |t| + 2 + 2 * (|t| ^ 3 * c) := by linarith
  have hKnn : 0 ≤ 4 * (|t| ^ 3 * c) + t ^ 2 + 1 := by linarith
  obtain ⟨δ1, hδ1, hM⟩ := exists_pos_mul_lt one_pos (2 * |t| + 2 + 2 * (|t| ^ 3 * c))
  obtain ⟨δ2, hδ2, hK⟩ := exists_pos_mul_lt hε (4 * (|t| ^ 3 * c) + t ^ 2 + 1)
  obtain ⟨δ, hδ, hd1, hd2, hd3⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ1 ∧ δ ≤ δ2 ∧ δ ≤ c - σsq :=
    ⟨min (min δ1 δ2) (c - σsq), lt_min (lt_min hδ1 hδ2) (sub_pos.2 (by linarith)),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      min_le_right _ _⟩
  have hMδ : (2 * |t| + 2 + 2 * (|t| ^ 3 * c)) * δ < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hd1 hMnn) hM
  have hKδ : (4 * (|t| ^ 3 * c) + t ^ 2 + 1) * δ < ε :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hd2 hKnn) hK
  refine ⟨δ, hδ, by linarith, by linarith [mul_nonneg hT3c hδ.le],
    by linarith [mul_nonneg hT hδ.le], by linarith [mul_nonneg hsq hδ.le]⟩

/-- Convergence in measure of the truncated ratio to `exp (-σsq t ^ 2 / 2)`, when the sum of
squares converges in measure to `σsq < c` and the terms are uniformly small in measure. -/
theorem tendstoInMeasure_truncRatio {P : Measure Ω} (X : ℕ → ℕ → Ω → ℝ) (L : ℕ → ℕ)
    (σsq c t : ℝ) (hσ : 0 ≤ σsq) (hσc : σsq < c)
    (hmax : ∀ δ > 0, Tendsto (fun n => P {ω | ∃ k < L n, δ < |X n k ω|}) atTop (𝓝 0))
    (hV : TendstoInMeasure P (fun n ω => ∑ k ∈ Finset.range (L n), X n k ω ^ 2) atTop
      (fun _ => σsq)) :
    TendstoInMeasure P (fun n => truncRatio (X n) c t (L n)) atTop
      (fun _ => Complex.exp ((-(σsq * t ^ 2 / 2) : ℝ) : ℂ)) := by
  rw [tendstoInMeasure_iff_dist] at hV ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδc, ht, hρ, hsmall⟩ := exists_delta_pos σsq c t ε hσ hσc hε
  have hA : Tendsto (fun n => P {ω | ∃ k < L n, δ < |X n k ω|}) atTop (𝓝 0) := hmax δ hδ
  have hB : Tendsto (fun n => P {ω | δ ≤ dist (∑ k ∈ Finset.range (L n), X n k ω ^ 2) σsq})
      atTop (𝓝 0) := hV δ hδ
  have hsub : ∀ n, {ω | ε ≤ dist (truncRatio (X n) c t (L n) ω)
        (Complex.exp ((-(σsq * t ^ 2 / 2) : ℝ) : ℂ))} ⊆
      {ω | ∃ k < L n, δ < |X n k ω|} ∪
        {ω | δ ≤ dist (∑ k ∈ Finset.range (L n), X n k ω ^ 2) σsq} := by
    intro n ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and, not_lt,
      not_le] at hcon hω
    obtain ⟨hX, hV'⟩ := hcon
    rw [Real.dist_eq] at hV'
    have hbound := norm_truncRatio_sub_le (X n) (L n) σsq c t δ ω hσ hδ.le hδc ht hρ hX hV'.le
    rw [dist_eq_norm] at hω
    linarith
  have hbd : ∀ n, P {ω | ε ≤ dist (truncRatio (X n) c t (L n) ω)
        (Complex.exp ((-(σsq * t ^ 2 / 2) : ℝ) : ℂ))} ≤
      P {ω | ∃ k < L n, δ < |X n k ω|} +
        P {ω | δ ≤ dist (∑ k ∈ Finset.range (L n), X n k ω ^ 2) σsq} :=
    fun n => (measure_mono (hsub n)).trans (measure_union_le _ _)
  have hlim := hA.add hB
  rw [add_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hbd

end LatticeProb.McLeish
